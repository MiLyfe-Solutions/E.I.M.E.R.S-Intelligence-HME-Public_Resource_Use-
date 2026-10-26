import V185TrunkScan20Chunk166

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_1016888 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 3]
def baseStart_1016888 : Nat := 118140960795 + 1016888 * 2 ^ 59
def prefixEnd_1016888 : Nat := 4983230072969 + 3 ^ 40 * 1016888 * 2
def baseEnd_1016888 : Nat := 464135391812731248643043

theorem tailTrace_1016888 : CollatzResearch.WordTrace tailWord_1016888 prefixEnd_1016888 464135391812731248643043 := by
  unfold tailWord_1016888
  simp only [CollatzResearch.WordTrace]
  refine ⟨18544476169997960744441659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24725968226663947659255545 18544476169997960744441659)
  ·
    refine ⟨27816714254996941116662489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18544476169997960744441659 27816714254996941116662489)
    ·
      refine ⟨20862535691247705837496867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27816714254996941116662489 20862535691247705837496867)
      ·
        refine ⟨31293803536871558756245301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20862535691247705837496867 31293803536871558756245301)
        ·
          refine ⟨2933794081581708633397997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31293803536871558756245301 2933794081581708633397997)
          ·
            refine ⟨1100172780593140737524249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2933794081581708633397997 1100172780593140737524249)
            ·
              refine ⟨825129585444855553143187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100172780593140737524249 825129585444855553143187)
              ·
                refine ⟨1237694378167283329714781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825129585444855553143187 1237694378167283329714781)
                ·
                  refine ⟨464135391812731248643043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237694378167283329714781 464135391812731248643043)
                  ·
                    rfl

theorem cell20_1016888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_1016888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016888 prefixEnd_1016888 := by exact prefixLift 1016888
  have htrace : WordTrace (prefixWord ++ tailWord_1016888) baseStart_1016888 baseEnd_1016888 := by
    simpa [prefixWord, tailWord_1016888, baseEnd_1016888] using wordTrace_append hprefix tailTrace_1016888
  have hstable : (prefixWord ++ tailWord_1016888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016888).length < 2 ^ (prefixWord ++ tailWord_1016888).sum := by decide
  have hdescent : baseEnd_1016888 < baseStart_1016888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016902 : List Nat := [6, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1016902 : Nat := 118140960795 + 1016902 * 2 ^ 59
def prefixEnd_1016902 : Nat := 4983230072969 + 3 ^ 40 * 1016902 * 2
def baseEnd_1016902 : Nat := 154713927264736474058773

theorem tailTrace_1016902 : CollatzResearch.WordTrace tailWord_1016902 prefixEnd_1016902 154713927264736474058773 := by
  unfold tailWord_1016902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159045717560787558746655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24726308641296801253261973 1159045717560787558746655)
  ·
    refine ⟨1738568576341181338119983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1159045717560787558746655 1738568576341181338119983)
    ·
      refine ⟨2607852864511772007179975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1738568576341181338119983 2607852864511772007179975)
      ·
        refine ⟨3911779296767658010769963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607852864511772007179975 3911779296767658010769963)
        ·
          refine ⟨5867668945151487016154945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911779296767658010769963 5867668945151487016154945)
          ·
            refine ⟨4400751708863615262116209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5867668945151487016154945 4400751708863615262116209)
            ·
              refine ⟨3300563781647711446587157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4400751708863615262116209 3300563781647711446587157)
              ·
                refine ⟨154713927264736474058773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3300563781647711446587157 154713927264736474058773)
                ·
                  rfl

theorem cell20_1016902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1016902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016902 prefixEnd_1016902 := by exact prefixLift 1016902
  have htrace : WordTrace (prefixWord ++ tailWord_1016902) baseStart_1016902 baseEnd_1016902 := by
    simpa [prefixWord, tailWord_1016902, baseEnd_1016902] using wordTrace_append hprefix tailTrace_1016902
  have hstable : (prefixWord ++ tailWord_1016902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016902).length < 2 ^ (prefixWord ++ tailWord_1016902).sum := by decide
  have hdescent : baseEnd_1016902 < baseStart_1016902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016906 : List Nat := [3, 1, 2, 1, 1, 2, 4, 6]
def baseStart_1016906 : Nat := 118140960795 + 1016906 * 2 ^ 59
def prefixEnd_1016906 : Nat := 4983230072969 + 3 ^ 40 * 1016906 * 2
def baseEnd_1016906 : Nat := 154714535834401062014323

theorem tailTrace_1016906 : CollatzResearch.WordTrace tailWord_1016906 prefixEnd_1016906 154714535834401062014323 := by
  unfold tailWord_1016906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272402213482677640759643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24726405902620473708692381 9272402213482677640759643)
  ·
    refine ⟨13908603320224016461139465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9272402213482677640759643 13908603320224016461139465)
    ·
      refine ⟨10431452490168012345854599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13908603320224016461139465 10431452490168012345854599)
      ·
        refine ⟨15647178735252018518781899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10431452490168012345854599 15647178735252018518781899)
        ·
          refine ⟨23470768102878027778172849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15647178735252018518781899 23470768102878027778172849)
          ·
            refine ⟨17603076077158520833629637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23470768102878027778172849 17603076077158520833629637)
            ·
              refine ⟨3300576764467222656305557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17603076077158520833629637 3300576764467222656305557)
              ·
                refine ⟨154714535834401062014323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3300576764467222656305557 154714535834401062014323)
                ·
                  rfl

theorem cell20_1016906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_1016906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016906 prefixEnd_1016906 := by exact prefixLift 1016906
  have htrace : WordTrace (prefixWord ++ tailWord_1016906) baseStart_1016906 baseEnd_1016906 := by
    simpa [prefixWord, tailWord_1016906, baseEnd_1016906] using wordTrace_append hprefix tailTrace_1016906
  have hstable : (prefixWord ++ tailWord_1016906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016906).length < 2 ^ (prefixWord ++ tailWord_1016906).sum := by decide
  have hdescent : baseEnd_1016906 < baseStart_1016906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016913 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_1016913 : Nat := 118140960795 + 1016913 * 2 ^ 59
def prefixEnd_1016913 : Nat := 4983230072969 + 3 ^ 40 * 1016913 * 2
def baseEnd_1016913 : Nat := 464146802493942272809607

theorem tailTrace_1016913 : CollatzResearch.WordTrace tailWord_1016913 prefixEnd_1016913 464146802493942272809607 := by
  unfold tailWord_1016913
  simp only [CollatzResearch.WordTrace]
  refine ⟨37089864164905350758543393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24726576109936900505695595 37089864164905350758543393)
  ·
    refine ⟨27817398123679013068907545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37089864164905350758543393 27817398123679013068907545)
    ·
      refine ⟨20863048592759259801680659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27817398123679013068907545 20863048592759259801680659)
      ·
        refine ⟨31294572889138889702520989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20863048592759259801680659 31294572889138889702520989)
        ·
          refine ⟨11735464833427083638445371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31294572889138889702520989 11735464833427083638445371)
          ·
            refine ⟨17603197250140625457668057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11735464833427083638445371 17603197250140625457668057)
            ·
              refine ⟨13202397937605469093251043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17603197250140625457668057 13202397937605469093251043)
              ·
                refine ⟨19803596906408203639876565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13202397937605469093251043 19803596906408203639876565)
                ·
                  refine ⟨464146802493942272809607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19803596906408203639876565 464146802493942272809607)
                  ·
                    rfl

theorem cell20_1016913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_1016913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016913 prefixEnd_1016913 := by exact prefixLift 1016913
  have htrace : WordTrace (prefixWord ++ tailWord_1016913) baseStart_1016913 baseEnd_1016913 := by
    simpa [prefixWord, tailWord_1016913, baseEnd_1016913] using wordTrace_append hprefix tailTrace_1016913
  have hstable : (prefixWord ++ tailWord_1016913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016913).length < 2 ^ (prefixWord ++ tailWord_1016913).sum := by decide
  have hdescent : baseEnd_1016913 < baseStart_1016913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016992 : List Nat := [2, 1, 1, 4, 2, 1, 1, 6, 2]
def baseStart_1016992 : Nat := 118140960795 + 1016992 * 2 ^ 59
def prefixEnd_1016992 : Nat := 4983230072969 + 3 ^ 40 * 1016992 * 2
def baseEnd_1016992 : Nat := 464182860246569109175951

theorem tailTrace_1016992 : CollatzResearch.WordTrace tailWord_1016992 prefixEnd_1016992 464182860246569109175951 := by
  unfold tailWord_1016992
  simp only [CollatzResearch.WordTrace]
  refine ⟨18546372765809573625334615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24728497021079431500446153 18546372765809573625334615)
  ·
    refine ⟨27819559148714360438001923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18546372765809573625334615 27819559148714360438001923)
    ·
      refine ⟨41729338723071540657002885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27819559148714360438001923 41729338723071540657002885)
      ·
        refine ⟨7824251010575913873188041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41729338723071540657002885 7824251010575913873188041)
        ·
          refine ⟨5868188257931935404891031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7824251010575913873188041 5868188257931935404891031)
          ·
            refine ⟨8802282386897903107336547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5868188257931935404891031 8802282386897903107336547)
            ·
              refine ⟨13203423580346854661004821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8802282386897903107336547 13203423580346854661004821)
              ·
                refine ⟨618910480328758812234601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13203423580346854661004821 618910480328758812234601)
                ·
                  refine ⟨464182860246569109175951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618910480328758812234601 464182860246569109175951)
                  ·
                    rfl

theorem cell20_1016992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_1016992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1016992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1016992 prefixEnd_1016992 := by exact prefixLift 1016992
  have htrace : WordTrace (prefixWord ++ tailWord_1016992) baseStart_1016992 baseEnd_1016992 := by
    simpa [prefixWord, tailWord_1016992, baseEnd_1016992] using wordTrace_append hprefix tailTrace_1016992
  have hstable : (prefixWord ++ tailWord_1016992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016992).length < 2 ^ (prefixWord ++ tailWord_1016992).sum := by decide
  have hdescent : baseEnd_1016992 < baseStart_1016992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017061 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 3]
def baseStart_1017061 : Nat := 118140960795 + 1017061 * 2 ^ 59
def prefixEnd_1017061 : Nat := 4983230072969 + 3 ^ 40 * 1017061 * 2
def baseEnd_1017061 : Nat := 464214353726711535875669

theorem tailTrace_1017061 : CollatzResearch.WordTrace tailWord_1017061 prefixEnd_1017061 464214353726711535875669 := by
  unfold tailWord_1017061
  simp only [CollatzResearch.WordTrace]
  refine ⟨37095262168369172034931037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24730174778912781356620691 37095262168369172034931037)
  ·
    refine ⟨13910723313138439513099139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37095262168369172034931037 13910723313138439513099139)
    ·
      refine ⟨20866084969707659269648709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13910723313138439513099139 20866084969707659269648709)
      ·
        refine ⟨3912390931820186113059133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20866084969707659269648709 3912390931820186113059133)
        ·
          refine ⟨1467146599432569792397175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3912390931820186113059133 1467146599432569792397175)
          ·
            refine ⟨2200719899148854688595763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467146599432569792397175 2200719899148854688595763)
            ·
              refine ⟨3301079848723282032893645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200719899148854688595763 3301079848723282032893645)
              ·
                refine ⟨1237904943271230762335117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3301079848723282032893645 1237904943271230762335117)
                ·
                  refine ⟨464214353726711535875669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237904943271230762335117 464214353726711535875669)
                  ·
                    rfl

theorem cell20_1017061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_1017061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017061 prefixEnd_1017061 := by exact prefixLift 1017061
  have htrace : WordTrace (prefixWord ++ tailWord_1017061) baseStart_1017061 baseEnd_1017061 := by
    simpa [prefixWord, tailWord_1017061, baseEnd_1017061] using wordTrace_append hprefix tailTrace_1017061
  have hstable : (prefixWord ++ tailWord_1017061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017061).length < 2 ^ (prefixWord ++ tailWord_1017061).sum := by decide
  have hdescent : baseEnd_1017061 < baseStart_1017061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017096 : List Nat := [2, 1, 3, 2, 4, 8]
def baseStart_1017096 : Nat := 118140960795 + 1017096 * 2 ^ 59
def prefixEnd_1017096 : Nat := 4983230072969 + 3 ^ 40 * 1017096 * 2
def baseEnd_1017096 : Nat := 17193715877052109989217

theorem tailTrace_1017096 : CollatzResearch.WordTrace tailWord_1017096 prefixEnd_1017096 17193715877052109989217 := by
  unfold tailWord_1017096
  simp only [CollatzResearch.WordTrace]
  refine ⟨18548269361621186506227571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24731025815494915341636761 18548269361621186506227571)
  ·
    refine ⟨27822404042431779759341357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18548269361621186506227571 27822404042431779759341357)
    ·
      refine ⟨10433401515911917409753009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27822404042431779759341357 10433401515911917409753009)
      ·
        refine ⟨7825051136933938057314757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10433401515911917409753009 7825051136933938057314757)
        ·
          refine ⟨1467197088175113385746517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7825051136933938057314757 1467197088175113385746517)
          ·
            refine ⟨17193715877052109989217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1467197088175113385746517 17193715877052109989217)
            ·
              rfl

theorem cell20_1017096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 8].length) (baseStart_1017096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017096 prefixEnd_1017096 := by exact prefixLift 1017096
  have htrace : WordTrace (prefixWord ++ tailWord_1017096) baseStart_1017096 baseEnd_1017096 := by
    simpa [prefixWord, tailWord_1017096, baseEnd_1017096] using wordTrace_append hprefix tailTrace_1017096
  have hstable : (prefixWord ++ tailWord_1017096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017096).length < 2 ^ (prefixWord ++ tailWord_1017096).sum := by decide
  have hdescent : baseEnd_1017096 < baseStart_1017096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017102 : List Nat := [4, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_1017102 : Nat := 118140960795 + 1017102 * 2 ^ 59
def prefixEnd_1017102 : Nat := 4983230072969 + 3 ^ 40 * 1017102 * 2
def baseEnd_1017102 : Nat := 464233067243897615508835

theorem tailTrace_1017102 : CollatzResearch.WordTrace tailWord_1017102 prefixEnd_1017102 464233067243897615508835 := by
  unfold tailWord_1017102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637094695152579504646695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24731171707480424024782373 4637094695152579504646695)
  ·
    refine ⟨6955642042728869256970043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4637094695152579504646695 6955642042728869256970043)
    ·
      refine ⟨10433463064093303885455065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6955642042728869256970043 10433463064093303885455065)
      ·
        refine ⟨7825097298069977914091299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10433463064093303885455065 7825097298069977914091299)
        ·
          refine ⟨11737645947104966871136949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825097298069977914091299 11737645947104966871136949)
          ·
            refine ⟨1100404307541090644169089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11737645947104966871136949 1100404307541090644169089)
            ·
              refine ⟨825303230655817983126817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100404307541090644169089 825303230655817983126817)
              ·
                refine ⟨618977422991863487345113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825303230655817983126817 618977422991863487345113)
                ·
                  refine ⟨464233067243897615508835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618977422991863487345113 464233067243897615508835)
                  ·
                    rfl

theorem cell20_1017102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_1017102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017102 prefixEnd_1017102 := by exact prefixLift 1017102
  have htrace : WordTrace (prefixWord ++ tailWord_1017102) baseStart_1017102 baseEnd_1017102 := by
    simpa [prefixWord, tailWord_1017102, baseEnd_1017102] using wordTrace_append hprefix tailTrace_1017102
  have hstable : (prefixWord ++ tailWord_1017102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017102).length < 2 ^ (prefixWord ++ tailWord_1017102).sum := by decide
  have hdescent : baseEnd_1017102 < baseStart_1017102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017130 : List Nat := [3, 1, 4, 2, 1, 2, 3, 4]
def baseStart_1017130 : Nat := 118140960795 + 1017130 * 2 ^ 59
def prefixEnd_1017130 : Nat := 4983230072969 + 3 ^ 40 * 1017130 * 2
def baseEnd_1017130 : Nat := 154748615735617987525129

theorem tailTrace_1017130 : CollatzResearch.WordTrace tailWord_1017130 prefixEnd_1017130 154748615735617987525129 := by
  unfold tailWord_1017130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9274444701279799204798211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24731852536746131212795229 9274444701279799204798211)
  ·
    refine ⟨13911667051919698807197317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9274444701279799204798211 13911667051919698807197317)
    ·
      refine ⟨2608437572234943526349497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13911667051919698807197317 2608437572234943526349497)
      ·
        refine ⟨1956328179176207644762123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2608437572234943526349497 1956328179176207644762123)
        ·
          refine ⟨2934492268764311467143185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956328179176207644762123 2934492268764311467143185)
          ·
            refine ⟨2200869201573233600357389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2934492268764311467143185 2200869201573233600357389)
            ·
              refine ⟨825325950589962600134021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2200869201573233600357389 825325950589962600134021)
              ·
                refine ⟨154748615735617987525129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825325950589962600134021 154748615735617987525129)
                ·
                  rfl

theorem cell20_1017130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_1017130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017130 prefixEnd_1017130 := by exact prefixLift 1017130
  have htrace : WordTrace (prefixWord ++ tailWord_1017130) baseStart_1017130 baseEnd_1017130 := by
    simpa [prefixWord, tailWord_1017130, baseEnd_1017130] using wordTrace_append hprefix tailTrace_1017130
  have hstable : (prefixWord ++ tailWord_1017130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017130).length < 2 ^ (prefixWord ++ tailWord_1017130).sum := by decide
  have hdescent : baseEnd_1017130 < baseStart_1017130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017172 : List Nat := [2, 4, 1, 1, 2, 1, 2, 7]
def baseStart_1017172 : Nat := 118140960795 + 1017172 * 2 ^ 59
def prefixEnd_1017172 : Nat := 4983230072969 + 3 ^ 40 * 1017172 * 2
def baseEnd_1017172 : Nat := 154755005717096161058405

theorem tailTrace_1017172 : CollatzResearch.WordTrace tailWord_1017172 prefixEnd_1017172 154755005717096161058405 := by
  unfold tailWord_1017172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18549655335483518996110885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24732873780644691994814513 18549655335483518996110885)
  ·
    refine ⟨3478060375403159811770791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18549655335483518996110885 3478060375403159811770791)
    ·
      refine ⟨5217090563104739717656187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3478060375403159811770791 5217090563104739717656187)
      ·
        refine ⟨7825635844657109576484281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217090563104739717656187 7825635844657109576484281)
        ·
          refine ⟨5869226883492832182363211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7825635844657109576484281 5869226883492832182363211)
          ·
            refine ⟨8803840325239248273544817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5869226883492832182363211 8803840325239248273544817)
            ·
              refine ⟨6602880243929436205158613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8803840325239248273544817 6602880243929436205158613)
              ·
                refine ⟨154755005717096161058405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6602880243929436205158613 154755005717096161058405)
                ·
                  rfl

theorem cell20_1017172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_1017172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017172 prefixEnd_1017172 := by exact prefixLift 1017172
  have htrace : WordTrace (prefixWord ++ tailWord_1017172) baseStart_1017172 baseEnd_1017172 := by
    simpa [prefixWord, tailWord_1017172, baseEnd_1017172] using wordTrace_append hprefix tailTrace_1017172
  have hstable : (prefixWord ++ tailWord_1017172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017172).length < 2 ^ (prefixWord ++ tailWord_1017172).sum := by decide
  have hdescent : baseEnd_1017172 < baseStart_1017172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017175 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 3]
def baseStart_1017175 : Nat := 118140960795 + 1017175 * 2 ^ 59
def prefixEnd_1017175 : Nat := 4983230072969 + 3 ^ 40 * 1017175 * 2
def baseEnd_1017175 : Nat := 464266386433033806075203

theorem tailTrace_1017175 : CollatzResearch.WordTrace tailWord_1017175 prefixEnd_1017175 464266386433033806075203 := by
  unfold tailWord_1017175
  simp only [CollatzResearch.WordTrace]
  refine ⟨37099420089956169504580979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24732946726637446336387319 37099420089956169504580979)
  ·
    refine ⟨55649130134934254256871469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37099420089956169504580979 55649130134934254256871469)
    ·
      refine ⟨20868423800600345346326801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55649130134934254256871469 20868423800600345346326801)
      ·
        refine ⟨15651317850450259009745101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20868423800600345346326801 15651317850450259009745101)
        ·
          refine ⟨5869244193918847128654413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15651317850450259009745101 5869244193918847128654413)
          ·
            refine ⟨2200966572719567673245405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5869244193918847128654413 2200966572719567673245405)
            ·
              refine ⟨825362464769837877467027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2200966572719567673245405 825362464769837877467027)
              ·
                refine ⟨1238043697154756816200541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825362464769837877467027 1238043697154756816200541)
                ·
                  refine ⟨464266386433033806075203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238043697154756816200541 464266386433033806075203)
                  ·
                    rfl

theorem cell20_1017175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 3].length) (baseStart_1017175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017175 prefixEnd_1017175 := by exact prefixLift 1017175
  have htrace : WordTrace (prefixWord ++ tailWord_1017175) baseStart_1017175 baseEnd_1017175 := by
    simpa [prefixWord, tailWord_1017175, baseEnd_1017175] using wordTrace_append hprefix tailTrace_1017175
  have hstable : (prefixWord ++ tailWord_1017175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017175).length < 2 ^ (prefixWord ++ tailWord_1017175).sum := by decide
  have hdescent : baseEnd_1017175 < baseStart_1017175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017181 : List Nat := [1, 4, 5, 1, 2, 1, 2, 4]
def baseStart_1017181 : Nat := 118140960795 + 1017181 * 2 ^ 59
def prefixEnd_1017181 : Nat := 4983230072969 + 3 ^ 40 * 1017181 * 2
def baseEnd_1017181 : Nat := 154756374998841483958393

theorem tailTrace_1017181 : CollatzResearch.WordTrace tailWord_1017181 prefixEnd_1017181 154756374998841483958393 := by
  unfold tailWord_1017181
  simp only [CollatzResearch.WordTrace]
  refine ⟨37099638927934432529299397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24733092618622955019532931 37099638927934432529299397)
  ·
    refine ⟨6956182298987706099243637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37099638927934432529299397 6956182298987706099243637)
    ·
      refine ⟨652142090530097446804091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6956182298987706099243637 652142090530097446804091)
      ·
        refine ⟨978213135795146170206137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652142090530097446804091 978213135795146170206137)
        ·
          refine ⟨733659851846359627654603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978213135795146170206137 733659851846359627654603)
          ·
            refine ⟨1100489777769539441481905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733659851846359627654603 1100489777769539441481905)
            ·
              refine ⟨825367333327154581111429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100489777769539441481905 825367333327154581111429)
              ·
                refine ⟨154756374998841483958393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825367333327154581111429 154756374998841483958393)
                ·
                  rfl

theorem cell20_1017181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 4].length) (baseStart_1017181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017181 prefixEnd_1017181 := by exact prefixLift 1017181
  have htrace : WordTrace (prefixWord ++ tailWord_1017181) baseStart_1017181 baseEnd_1017181 := by
    simpa [prefixWord, tailWord_1017181, baseEnd_1017181] using wordTrace_append hprefix tailTrace_1017181
  have hstable : (prefixWord ++ tailWord_1017181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017181).length < 2 ^ (prefixWord ++ tailWord_1017181).sum := by decide
  have hdescent : baseEnd_1017181 < baseStart_1017181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017220 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 4]
def baseStart_1017220 : Nat := 118140960795 + 1017220 * 2 ^ 59
def prefixEnd_1017220 : Nat := 4983230072969 + 3 ^ 40 * 1017220 * 2
def baseEnd_1017220 : Nat := 464286925659213649575019

theorem tailTrace_1017220 : CollatzResearch.WordTrace tailWord_1017220 prefixEnd_1017220 464286925659213649575019 := by
  unfold tailWord_1017220
  simp only [CollatzResearch.WordTrace]
  refine ⟨18550530687396571094984557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24734040916528761459979409 18550530687396571094984557)
  ·
    refine ⟨6956449007773714160619209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18550530687396571094984557 6956449007773714160619209)
    ·
      refine ⟨5217336755830285620464407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6956449007773714160619209 5217336755830285620464407)
      ·
        refine ⟨7826005133745428430696611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217336755830285620464407 7826005133745428430696611)
        ·
          refine ⟨11739007700618142646044917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7826005133745428430696611 11739007700618142646044917)
          ·
            refine ⟨1100531971932950873066711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11739007700618142646044917 1100531971932950873066711)
            ·
              refine ⟨1650797957899426309600067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100531971932950873066711 1650797957899426309600067)
              ·
                refine ⟨2476196936849139464400101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650797957899426309600067 2476196936849139464400101)
                ·
                  refine ⟨464286925659213649575019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476196936849139464400101 464286925659213649575019)
                  ·
                    rfl

theorem cell20_1017220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_1017220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017220 prefixEnd_1017220 := by exact prefixLift 1017220
  have htrace : WordTrace (prefixWord ++ tailWord_1017220) baseStart_1017220 baseEnd_1017220 := by
    simpa [prefixWord, tailWord_1017220, baseEnd_1017220] using wordTrace_append hprefix tailTrace_1017220
  have hstable : (prefixWord ++ tailWord_1017220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017220).length < 2 ^ (prefixWord ++ tailWord_1017220).sum := by decide
  have hdescent : baseEnd_1017220 < baseStart_1017220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017331 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 3]
def baseStart_1017331 : Nat := 118140960795 + 1017331 * 2 ^ 59
def prefixEnd_1017331 : Nat := 4983230072969 + 3 ^ 40 * 1017331 * 2
def baseEnd_1017331 : Nat := 464337589083790596874565

theorem tailTrace_1017331 : CollatzResearch.WordTrace tailWord_1017331 prefixEnd_1017331 464337589083790596874565 := by
  unfold tailWord_1017331
  simp only [CollatzResearch.WordTrace]
  refine ⟨37105109877391008147259847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24736739918260672098173231 37105109877391008147259847)
  ·
    refine ⟨55657664816086512220889771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37105109877391008147259847 55657664816086512220889771)
    ·
      refine ⟨83486497224129768331334657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55657664816086512220889771 83486497224129768331334657)
      ·
        refine ⟨62614872918097326248500993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83486497224129768331334657 62614872918097326248500993)
        ·
          refine ⟨46961154688572994686375745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62614872918097326248500993 46961154688572994686375745)
          ·
            refine ⟨35220866016429746014781809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46961154688572994686375745 35220866016429746014781809)
            ·
              refine ⟨26415649512322309511086357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35220866016429746014781809 26415649512322309511086357)
              ·
                refine ⟨1238233570890108258332173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26415649512322309511086357 1238233570890108258332173)
                ·
                  refine ⟨464337589083790596874565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238233570890108258332173 464337589083790596874565)
                  ·
                    rfl

theorem cell20_1017331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 3].length) (baseStart_1017331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017331 prefixEnd_1017331 := by exact prefixLift 1017331
  have htrace : WordTrace (prefixWord ++ tailWord_1017331) baseStart_1017331 baseEnd_1017331 := by
    simpa [prefixWord, tailWord_1017331, baseEnd_1017331] using wordTrace_append hprefix tailTrace_1017331
  have hstable : (prefixWord ++ tailWord_1017331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017331).length < 2 ^ (prefixWord ++ tailWord_1017331).sum := by decide
  have hdescent : baseEnd_1017331 < baseStart_1017331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017334 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1017334 : Nat := 118140960795 + 1017334 * 2 ^ 59
def prefixEnd_1017334 : Nat := 4983230072969 + 3 ^ 40 * 1017334 * 2
def baseEnd_1017334 : Nat := 464338958365535919774553

theorem tailTrace_1017334 : CollatzResearch.WordTrace tailWord_1017334 prefixEnd_1017334 464338958365535919774553 := by
  unfold tailWord_1017334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319076206023758728726191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24736812864253426439746037 2319076206023758728726191)
  ·
    refine ⟨3478614309035638093089287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2319076206023758728726191 3478614309035638093089287)
    ·
      refine ⟨5217921463553457139633931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3478614309035638093089287 5217921463553457139633931)
      ·
        refine ⟨7826882195330185709450897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217921463553457139633931 7826882195330185709450897)
        ·
          refine ⟨5870161646497639282088173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7826882195330185709450897 5870161646497639282088173)
          ·
            refine ⟨2201310617436614730783065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5870161646497639282088173 2201310617436614730783065)
            ·
              refine ⟨1650982963077461048087299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2201310617436614730783065 1650982963077461048087299)
              ·
                refine ⟨2476474444616191572130949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650982963077461048087299 2476474444616191572130949)
                ·
                  refine ⟨464338958365535919774553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476474444616191572130949 464338958365535919774553)
                  ·
                    rfl

theorem cell20_1017334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1017334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017334 prefixEnd_1017334 := by exact prefixLift 1017334
  have htrace : WordTrace (prefixWord ++ tailWord_1017334) baseStart_1017334 baseEnd_1017334 := by
    simpa [prefixWord, tailWord_1017334, baseEnd_1017334] using wordTrace_append hprefix tailTrace_1017334
  have hstable : (prefixWord ++ tailWord_1017334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017334).length < 2 ^ (prefixWord ++ tailWord_1017334).sum := by decide
  have hdescent : baseEnd_1017334 < baseStart_1017334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017358 : List Nat := [4, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1017358 : Nat := 118140960795 + 1017358 * 2 ^ 59
def prefixEnd_1017358 : Nat := 4983230072969 + 3 ^ 40 * 1017358 * 2
def baseEnd_1017358 : Nat := 154783304206499500991485

theorem tailTrace_1017358 : CollatzResearch.WordTrace tailWord_1017358 prefixEnd_1017358 154783304206499500991485 := by
  unfold tailWord_1017358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4638261831036648969811591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24737396432195461172328485 4638261831036648969811591)
  ·
    refine ⟨6957392746554973454717387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4638261831036648969811591 6957392746554973454717387)
    ·
      refine ⟨10436089119832460182076081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6957392746554973454717387 10436089119832460182076081)
      ·
        refine ⟨7827066839874345136557061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10436089119832460182076081 7827066839874345136557061)
        ·
          refine ⟨1467575032476439713104449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7827066839874345136557061 1467575032476439713104449)
          ·
            refine ⟨1100681274357329784828337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1467575032476439713104449 1100681274357329784828337)
            ·
              refine ⟨825510955767997338621253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100681274357329784828337 825510955767997338621253)
              ·
                refine ⟨154783304206499500991485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825510955767997338621253 154783304206499500991485)
                ·
                  rfl

theorem cell20_1017358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1017358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017358 prefixEnd_1017358 := by exact prefixLift 1017358
  have htrace : WordTrace (prefixWord ++ tailWord_1017358) baseStart_1017358 baseEnd_1017358 := by
    simpa [prefixWord, tailWord_1017358, baseEnd_1017358] using wordTrace_append hprefix tailTrace_1017358
  have hstable : (prefixWord ++ tailWord_1017358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017358).length < 2 ^ (prefixWord ++ tailWord_1017358).sum := by decide
  have hdescent : baseEnd_1017358 < baseStart_1017358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017368 : List Nat := [2, 1, 2, 3, 5, 1, 1, 3, 2]
def baseStart_1017368 : Nat := 118140960795 + 1017368 * 2 ^ 59
def prefixEnd_1017368 : Nat := 4983230072969 + 3 ^ 40 * 1017368 * 2
def baseEnd_1017368 : Nat := 464354476891982912641081

theorem tailTrace_1017368 : CollatzResearch.WordTrace tailWord_1017368 prefixEnd_1017368 464354476891982912641081 := by
  unfold tailWord_1017368
  simp only [CollatzResearch.WordTrace]
  refine ⟨18553229689128481733178379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24737639585504642310904505 18553229689128481733178379)
  ·
    refine ⟨27829844533692722599767569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18553229689128481733178379 27829844533692722599767569)
    ·
      refine ⟨20872383400269541949825677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27829844533692722599767569 20872383400269541949825677)
      ·
        refine ⟨7827143775101078231184629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20872383400269541949825677 7827143775101078231184629)
        ·
          refine ⟨733794728915726084173559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7827143775101078231184629 733794728915726084173559)
          ·
            refine ⟨1100692093373589126260339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733794728915726084173559 1100692093373589126260339)
            ·
              refine ⟨1651038140060383689390509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100692093373589126260339 1651038140060383689390509)
              ·
                refine ⟨619139302522643883521441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1651038140060383689390509 619139302522643883521441)
                ·
                  refine ⟨464354476891982912641081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619139302522643883521441 464354476891982912641081)
                  ·
                    rfl

theorem cell20_1017368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_1017368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017368 prefixEnd_1017368 := by exact prefixLift 1017368
  have htrace : WordTrace (prefixWord ++ tailWord_1017368) baseStart_1017368 baseEnd_1017368 := by
    simpa [prefixWord, tailWord_1017368, baseEnd_1017368] using wordTrace_append hprefix tailTrace_1017368
  have hstable : (prefixWord ++ tailWord_1017368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017368).length < 2 ^ (prefixWord ++ tailWord_1017368).sum := by decide
  have hdescent : baseEnd_1017368 < baseStart_1017368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017379 : List Nat := [1, 1, 1, 4, 6, 1, 6]
def baseStart_1017379 : Nat := 118140960795 + 1017379 * 2 ^ 59
def prefixEnd_1017379 : Nat := 4983230072969 + 3 ^ 40 * 1017379 * 2
def baseEnd_1017379 : Nat := 51595499732412862586041

theorem tailTrace_1017379 : CollatzResearch.WordTrace tailWord_1017379 prefixEnd_1017379 51595499732412862586041 := by
  unfold tailWord_1017379
  simp only [CollatzResearch.WordTrace]
  refine ⟨37106860581217112345007191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24737907054144741563338127 37106860581217112345007191)
  ·
    refine ⟨55660290871825668517510787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37106860581217112345007191 55660290871825668517510787)
    ·
      refine ⟨83490436307738502776266181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55660290871825668517510787 83490436307738502776266181)
      ·
        refine ⟨15654456807700969270549909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83490436307738502776266181 15654456807700969270549909)
        ·
          refine ⟨733802662860982934557027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15654456807700969270549909 733802662860982934557027)
          ·
            refine ⟨1100703994291474401835541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733802662860982934557027 1100703994291474401835541)
            ·
              refine ⟨51595499732412862586041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1100703994291474401835541 51595499732412862586041)
              ·
                rfl

theorem cell20_1017379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 6].length) (baseStart_1017379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017379 prefixEnd_1017379 := by exact prefixLift 1017379
  have htrace : WordTrace (prefixWord ++ tailWord_1017379) baseStart_1017379 baseEnd_1017379 := by
    simpa [prefixWord, tailWord_1017379, baseEnd_1017379] using wordTrace_append hprefix tailTrace_1017379
  have hstable : (prefixWord ++ tailWord_1017379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017379).length < 2 ^ (prefixWord ++ tailWord_1017379).sum := by decide
  have hdescent : baseEnd_1017379 < baseStart_1017379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017386 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_1017386 : Nat := 118140960795 + 1017386 * 2 ^ 59
def prefixEnd_1017386 : Nat := 4983230072969 + 3 ^ 40 * 1017386 * 2
def baseEnd_1017386 : Nat := 464362692582454850041007

theorem tailTrace_1017386 : CollatzResearch.WordTrace tailWord_1017386 prefixEnd_1017386 464362692582454850041007 := by
  unfold tailWord_1017386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9276778973047938135128003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24738077261461168360341341 9276778973047938135128003)
  ·
    refine ⟨13915168459571907202692005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9276778973047938135128003 13915168459571907202692005)
    ·
      refine ⟨2609094086169732600504751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13915168459571907202692005 2609094086169732600504751)
      ·
        refine ⟨3913641129254598900757127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609094086169732600504751 3913641129254598900757127)
        ·
          refine ⟨5870461693881898351135691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913641129254598900757127 5870461693881898351135691)
          ·
            refine ⟨8805692540822847526703537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870461693881898351135691 8805692540822847526703537)
            ·
              refine ⟨6604269405617135645027653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8805692540822847526703537 6604269405617135645027653)
              ·
                refine ⟨1238300513553212933442685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6604269405617135645027653 1238300513553212933442685)
                ·
                  refine ⟨464362692582454850041007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238300513553212933442685 464362692582454850041007)
                  ·
                    rfl

theorem cell20_1017386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_1017386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017386 prefixEnd_1017386 := by exact prefixLift 1017386
  have htrace : WordTrace (prefixWord ++ tailWord_1017386) baseStart_1017386 baseEnd_1017386 := by
    simpa [prefixWord, tailWord_1017386, baseEnd_1017386] using wordTrace_append hprefix tailTrace_1017386
  have hstable : (prefixWord ++ tailWord_1017386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017386).length < 2 ^ (prefixWord ++ tailWord_1017386).sum := by decide
  have hdescent : baseEnd_1017386 < baseStart_1017386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017400 : List Nat := [2, 1, 2, 1, 4, 3, 2, 5]
def baseStart_1017400 : Nat := 118140960795 + 1017400 * 2 ^ 59
def prefixEnd_1017400 : Nat := 4983230072969 + 3 ^ 40 * 1017400 * 2
def baseEnd_1017400 : Nat := 154789694187977674524761

theorem tailTrace_1017400 : CollatzResearch.WordTrace tailWord_1017400 prefixEnd_1017400 154789694187977674524761 := by
  unfold tailWord_1017400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18553813257070516465760827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24738417676094021954347769 18553813257070516465760827)
  ·
    refine ⟨27830719885605774698641241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18553813257070516465760827 27830719885605774698641241)
    ·
      refine ⟨20873039914204331023980931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27830719885605774698641241 20873039914204331023980931)
      ·
        refine ⟨31309559871306496535971397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20873039914204331023980931 31309559871306496535971397)
        ·
          refine ⟨5870542475869968100494637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31309559871306496535971397 5870542475869968100494637)
          ·
            refine ⟨2201453428451238037685489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5870542475869968100494637 2201453428451238037685489)
            ·
              refine ⟨1651090071338428528264117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2201453428451238037685489 1651090071338428528264117)
              ·
                refine ⟨154789694187977674524761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1651090071338428528264117 154789694187977674524761)
                ·
                  rfl

theorem cell20_1017400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_1017400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017400 prefixEnd_1017400 := by exact prefixLift 1017400
  have htrace : WordTrace (prefixWord ++ tailWord_1017400) baseStart_1017400 baseEnd_1017400 := by
    simpa [prefixWord, tailWord_1017400, baseEnd_1017400] using wordTrace_append hprefix tailTrace_1017400
  have hstable : (prefixWord ++ tailWord_1017400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017400).length < 2 ^ (prefixWord ++ tailWord_1017400).sum := by decide
  have hdescent : baseEnd_1017400 < baseStart_1017400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017452 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1017452 : Nat := 118140960795 + 1017452 * 2 ^ 59
def prefixEnd_1017452 : Nat := 4983230072969 + 3 ^ 40 * 1017452 * 2
def baseEnd_1017452 : Nat := 464392816780851953840737

theorem tailTrace_1017452 : CollatzResearch.WordTrace tailWord_1017452 prefixEnd_1017452 464392816780851953840737 := by
  unfold tailWord_1017452
  simp only [CollatzResearch.WordTrace]
  refine ⟨18554761554976322906207305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24739682073301763874943073 18554761554976322906207305)
  ·
    refine ⟨13916071166232242179655479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18554761554976322906207305 13916071166232242179655479)
    ·
      refine ⟨20874106749348363269483219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13916071166232242179655479 20874106749348363269483219)
      ·
        refine ⟨31311160124022544904224829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20874106749348363269483219 31311160124022544904224829)
        ·
          refine ⟨11741685046508454339084311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31311160124022544904224829 11741685046508454339084311)
          ·
            refine ⟨17612527569762681508626467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11741685046508454339084311 17612527569762681508626467)
            ·
              refine ⟨26418791354644022262939701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17612527569762681508626467 26418791354644022262939701)
              ·
                refine ⟨2476761689497877087150597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26418791354644022262939701 2476761689497877087150597)
                ·
                  refine ⟨464392816780851953840737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476761689497877087150597 464392816780851953840737)
                  ·
                    rfl

theorem cell20_1017452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1017452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017452 prefixEnd_1017452 := by exact prefixLift 1017452
  have htrace : WordTrace (prefixWord ++ tailWord_1017452) baseStart_1017452 baseEnd_1017452 := by
    simpa [prefixWord, tailWord_1017452, baseEnd_1017452] using wordTrace_append hprefix tailTrace_1017452
  have hstable : (prefixWord ++ tailWord_1017452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017452).length < 2 ^ (prefixWord ++ tailWord_1017452).sum := by decide
  have hdescent : baseEnd_1017452 < baseStart_1017452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017469 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1017469 : Nat := 118140960795 + 1017469 * 2 ^ 59
def prefixEnd_1017469 : Nat := 4983230072969 + 3 ^ 40 * 1017469 * 2
def baseEnd_1017469 : Nat := 464400576044075450274001

theorem tailTrace_1017469 : CollatzResearch.WordTrace tailWord_1017469 prefixEnd_1017469 464400576044075450274001 := by
  unfold tailWord_1017469
  simp only [CollatzResearch.WordTrace]
  refine ⟨37110143150891057715783461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24740095433927371810522307 37110143150891057715783461)
  ·
    refine ⟨6958151840792073321709399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37110143150891057715783461 6958151840792073321709399)
    ·
      refine ⟨10437227761188109982564099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6958151840792073321709399 10437227761188109982564099)
      ·
        refine ⟨15655841641782164973846149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10437227761188109982564099 15655841641782164973846149)
        ·
          refine ⟨2935470307834155932596153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15655841641782164973846149 2935470307834155932596153)
          ·
            refine ⟨2201602730875616949447115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2935470307834155932596153 2201602730875616949447115)
            ·
              refine ⟨3302404096313425424170673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2201602730875616949447115 3302404096313425424170673)
              ·
                refine ⟨2476803072235069068128005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302404096313425424170673 2476803072235069068128005)
                ·
                  refine ⟨464400576044075450274001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476803072235069068128005 464400576044075450274001)
                  ·
                    rfl

theorem cell20_1017469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1017469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017469 prefixEnd_1017469 := by exact prefixLift 1017469
  have htrace : WordTrace (prefixWord ++ tailWord_1017469) baseStart_1017469 baseEnd_1017469 := by
    simpa [prefixWord, tailWord_1017469, baseEnd_1017469] using wordTrace_append hprefix tailTrace_1017469
  have hstable : (prefixWord ++ tailWord_1017469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017469).length < 2 ^ (prefixWord ++ tailWord_1017469).sum := by decide
  have hdescent : baseEnd_1017469 < baseStart_1017469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017486 : List Nat := [4, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_1017486 : Nat := 118140960795 + 1017486 * 2 ^ 59
def prefixEnd_1017486 : Nat := 4983230072969 + 3 ^ 40 * 1017486 * 2
def baseEnd_1017486 : Nat := 464408335307298946707265

theorem tailTrace_1017486 : CollatzResearch.WordTrace tailWord_1017486 prefixEnd_1017486 464408335307298946707265 := by
  unfold tailWord_1017486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4638845398978683702394039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24740508794552979746101541 4638845398978683702394039)
  ·
    refine ⟨6958268098468025553591059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4638845398978683702394039 6958268098468025553591059)
    ·
      refine ⟨10437402147702038330386589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6958268098468025553591059 10437402147702038330386589)
      ·
        refine ⟨3914025805388264373894971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10437402147702038330386589 3914025805388264373894971)
        ·
          refine ⟨5871038708082396560842457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914025805388264373894971 5871038708082396560842457)
          ·
            refine ⟨4403279031061797420631843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5871038708082396560842457 4403279031061797420631843)
            ·
              refine ⟨6604918546592696130947765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4403279031061797420631843 6604918546592696130947765)
              ·
                refine ⟨619211113743065262276353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6604918546592696130947765 619211113743065262276353)
                ·
                  refine ⟨464408335307298946707265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619211113743065262276353 464408335307298946707265)
                  ·
                    rfl

theorem cell20_1017486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_1017486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017486 prefixEnd_1017486 := by exact prefixLift 1017486
  have htrace : WordTrace (prefixWord ++ tailWord_1017486) baseStart_1017486 baseEnd_1017486 := by
    simpa [prefixWord, tailWord_1017486, baseEnd_1017486] using wordTrace_append hprefix tailTrace_1017486
  have hstable : (prefixWord ++ tailWord_1017486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017486).length < 2 ^ (prefixWord ++ tailWord_1017486).sum := by decide
  have hdescent : baseEnd_1017486 < baseStart_1017486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017500 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 5]
def baseStart_1017500 : Nat := 118140960795 + 1017500 * 2 ^ 59
def prefixEnd_1017500 : Nat := 4983230072969 + 3 ^ 40 * 1017500 * 2
def baseEnd_1017500 : Nat := 464414725288777120240541

theorem tailTrace_1017500 : CollatzResearch.WordTrace tailWord_1017500 prefixEnd_1017500 464414725288777120240541 := by
  unfold tailWord_1017500
  simp only [CollatzResearch.WordTrace]
  refine ⟨18555636906889375005080977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24740849209185833340107969 18555636906889375005080977)
  ·
    refine ⟨13916727680167031253810733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18555636906889375005080977 13916727680167031253810733)
    ·
      refine ⟨5218772880062636720179025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13916727680167031253810733 5218772880062636720179025)
      ·
        refine ⟨3914079660046977540134269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5218772880062636720179025 3914079660046977540134269)
        ·
          refine ⟨1467779872517616577550351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3914079660046977540134269 1467779872517616577550351)
          ·
            refine ⟨2201669808776424866325527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467779872517616577550351 2201669808776424866325527)
            ·
              refine ⟨3302504713164637299488291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2201669808776424866325527 3302504713164637299488291)
              ·
                refine ⟨4953757069746955949232437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3302504713164637299488291 4953757069746955949232437)
                ·
                  refine ⟨464414725288777120240541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4953757069746955949232437 464414725288777120240541)
                  ·
                    rfl

theorem cell20_1017500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_1017500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017500 prefixEnd_1017500 := by exact prefixLift 1017500
  have htrace : WordTrace (prefixWord ++ tailWord_1017500) baseStart_1017500 baseEnd_1017500 := by
    simpa [prefixWord, tailWord_1017500, baseEnd_1017500] using wordTrace_append hprefix tailTrace_1017500
  have hstable : (prefixWord ++ tailWord_1017500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017500).length < 2 ^ (prefixWord ++ tailWord_1017500).sum := by decide
  have hdescent : baseEnd_1017500 < baseStart_1017500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017507 : List Nat := [1, 1, 1, 4, 1, 1, 3, 6, 2]
def baseStart_1017507 : Nat := 118140960795 + 1017507 * 2 ^ 59
def prefixEnd_1017507 : Nat := 4983230072969 + 3 ^ 40 * 1017507 * 2
def baseEnd_1017507 : Nat := 464417920279516207007179

theorem tailTrace_1017507 : CollatzResearch.WordTrace tailWord_1017507 prefixEnd_1017507 464417920279516207007179 := by
  unfold tailWord_1017507
  simp only [CollatzResearch.WordTrace]
  refine ⟨37111529124753390205666775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24741019416502260137111183 37111529124753390205666775)
  ·
    refine ⟨55667293687130085308500163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37111529124753390205666775 55667293687130085308500163)
    ·
      refine ⟨83500940530695127962750245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55667293687130085308500163 83500940530695127962750245)
      ·
        refine ⟨15656426349505336493015671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83500940530695127962750245 15656426349505336493015671)
        ·
          refine ⟨23484639524258004739523507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15656426349505336493015671 23484639524258004739523507)
          ·
            refine ⟨35226959286387007109285261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23484639524258004739523507 35226959286387007109285261)
            ·
              refine ⟨13210109732395127665981973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35226959286387007109285261 13210109732395127665981973)
              ·
                refine ⟨619223893706021609342905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13210109732395127665981973 619223893706021609342905)
                ·
                  refine ⟨464417920279516207007179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619223893706021609342905 464417920279516207007179)
                  ·
                    rfl

theorem cell20_1017507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 2].length) (baseStart_1017507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017507 prefixEnd_1017507 := by exact prefixLift 1017507
  have htrace : WordTrace (prefixWord ++ tailWord_1017507) baseStart_1017507 baseEnd_1017507 := by
    simpa [prefixWord, tailWord_1017507, baseEnd_1017507] using wordTrace_append hprefix tailTrace_1017507
  have hstable : (prefixWord ++ tailWord_1017507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017507).length < 2 ^ (prefixWord ++ tailWord_1017507).sum := by decide
  have hdescent : baseEnd_1017507 < baseStart_1017507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017517 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1017517 : Nat := 118140960795 + 1017517 * 2 ^ 59
def prefixEnd_1017517 : Nat := 4983230072969 + 3 ^ 40 * 1017517 * 2
def baseEnd_1017517 : Nat := 464422484552000616673805

theorem tailTrace_1017517 : CollatzResearch.WordTrace tailWord_1017517 prefixEnd_1017517 464422484552000616673805 := by
  unfold tailWord_1017517
  simp only [CollatzResearch.WordTrace]
  refine ⟨37111893854717161913530805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24741262569811441275687203 37111893854717161913530805)
  ·
    refine ⟨3479240048879733929393513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37111893854717161913530805 3479240048879733929393513)
    ·
      refine ⟨2609430036659800447045135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3479240048879733929393513 2609430036659800447045135)
      ·
        refine ⟨3914145054989700670567703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609430036659800447045135 3914145054989700670567703)
        ·
          refine ⟨5871217582484551005851555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914145054989700670567703 5871217582484551005851555)
          ·
            refine ⟨8806826373726826508777333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871217582484551005851555 8806826373726826508777333)
            ·
              refine ⟨825639972536889985197875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8806826373726826508777333 825639972536889985197875)
              ·
                refine ⟨1238459958805334977796813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825639972536889985197875 1238459958805334977796813)
                ·
                  refine ⟨464422484552000616673805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238459958805334977796813 464422484552000616673805)
                  ·
                    rfl

theorem cell20_1017517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1017517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017517 prefixEnd_1017517 := by exact prefixLift 1017517
  have htrace : WordTrace (prefixWord ++ tailWord_1017517) baseStart_1017517 baseEnd_1017517 := by
    simpa [prefixWord, tailWord_1017517, baseEnd_1017517] using wordTrace_append hprefix tailTrace_1017517
  have hstable : (prefixWord ++ tailWord_1017517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017517).length < 2 ^ (prefixWord ++ tailWord_1017517).sum := by decide
  have hdescent : baseEnd_1017517 < baseStart_1017517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017535 : List Nat := [1, 1, 2, 2, 2, 3, 3, 6]
def baseStart_1017535 : Nat := 118140960795 + 1017535 * 2 ^ 59
def prefixEnd_1017535 : Nat := 4983230072969 + 3 ^ 40 * 1017535 * 2
def baseEnd_1017535 : Nat := 154810233414157518024577

theorem tailTrace_1017535 : CollatzResearch.WordTrace tailWord_1017535 prefixEnd_1017535 154810233414157518024577 := by
  unfold tailWord_1017535
  simp only [CollatzResearch.WordTrace]
  refine ⟨37112550368651950987686059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24741700245767967325124039 37112550368651950987686059)
  ·
    refine ⟨55668825552977926481529089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37112550368651950987686059 55668825552977926481529089)
    ·
      refine ⟨41751619164733444861146817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55668825552977926481529089 41751619164733444861146817)
      ·
        refine ⟨31313714373550083645860113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41751619164733444861146817 31313714373550083645860113)
        ·
          refine ⟨23485285780162562734395085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31313714373550083645860113 23485285780162562734395085)
          ·
            refine ⟨8806982167560961025398157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23485285780162562734395085 8806982167560961025398157)
            ·
              refine ⟨3302618312835360384524309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8806982167560961025398157 3302618312835360384524309)
              ·
                refine ⟨154810233414157518024577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3302618312835360384524309 154810233414157518024577)
                ·
                  rfl

theorem cell20_1017535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_1017535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017535 prefixEnd_1017535 := by exact prefixLift 1017535
  have htrace : WordTrace (prefixWord ++ tailWord_1017535) baseStart_1017535 baseEnd_1017535 := by
    simpa [prefixWord, tailWord_1017535, baseEnd_1017535] using wordTrace_append hprefix tailTrace_1017535
  have hstable : (prefixWord ++ tailWord_1017535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017535).length < 2 ^ (prefixWord ++ tailWord_1017535).sum := by decide
  have hdescent : baseEnd_1017535 < baseStart_1017535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017558 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1017558 : Nat := 118140960795 + 1017558 * 2 ^ 59
def prefixEnd_1017558 : Nat := 4983230072969 + 3 ^ 40 * 1017558 * 2
def baseEnd_1017558 : Nat := 464441198069186696306971

theorem tailTrace_1017558 : CollatzResearch.WordTrace tailWord_1017558 prefixEnd_1017558 464441198069186696306971 := by
  unfold tailWord_1017558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319586827973039119735833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24742259498379083943848885 2319586827973039119735833)
  ·
    refine ⟨1739690120979779339801875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2319586827973039119735833 1739690120979779339801875)
    ·
      refine ⟨2609535181469669009702813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1739690120979779339801875 2609535181469669009702813)
      ·
        refine ⟨978575693051125878638555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2609535181469669009702813 978575693051125878638555)
        ·
          refine ⟨1467863539576688817957833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978575693051125878638555 1467863539576688817957833)
          ·
            refine ⟨1100897654682516613468375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1467863539576688817957833 1100897654682516613468375)
            ·
              refine ⟨1651346482023774920202563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100897654682516613468375 1651346482023774920202563)
              ·
                refine ⟨2477019723035662380303845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651346482023774920202563 2477019723035662380303845)
                ·
                  refine ⟨464441198069186696306971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477019723035662380303845 464441198069186696306971)
                  ·
                    rfl

theorem cell20_1017558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1017558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017558 prefixEnd_1017558 := by exact prefixLift 1017558
  have htrace : WordTrace (prefixWord ++ tailWord_1017558) baseStart_1017558 baseEnd_1017558 := by
    simpa [prefixWord, tailWord_1017558, baseEnd_1017558] using wordTrace_append hprefix tailTrace_1017558
  have hstable : (prefixWord ++ tailWord_1017558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017558).length < 2 ^ (prefixWord ++ tailWord_1017558).sum := by decide
  have hdescent : baseEnd_1017558 < baseStart_1017558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017559 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 3]
def baseStart_1017559 : Nat := 118140960795 + 1017559 * 2 ^ 59
def prefixEnd_1017559 : Nat := 4983230072969 + 3 ^ 40 * 1017559 * 2
def baseEnd_1017559 : Nat := 464441654496435137273633

theorem tailTrace_1017559 : CollatzResearch.WordTrace tailWord_1017559 prefixEnd_1017559 464441654496435137273633 := by
  unfold tailWord_1017559
  simp only [CollatzResearch.WordTrace]
  refine ⟨37113425720565003086559731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24742283813710002057706487 37113425720565003086559731)
  ·
    refine ⟨55670138580847504629839597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37113425720565003086559731 55670138580847504629839597)
    ·
      refine ⟨20876301967817814236189849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55670138580847504629839597 20876301967817814236189849)
      ·
        refine ⟨15657226475863360677142387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20876301967817814236189849 15657226475863360677142387)
        ·
          refine ⟨23485839713795041015713581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15657226475863360677142387 23485839713795041015713581)
          ·
            refine ⟨8807189892673140380892593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23485839713795041015713581 8807189892673140380892593)
            ·
              refine ⟨6605392419504855285669445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8807189892673140380892593 6605392419504855285669445)
              ·
                refine ⟨1238511078657160366063021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6605392419504855285669445 1238511078657160366063021)
                ·
                  refine ⟨464441654496435137273633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238511078657160366063021 464441654496435137273633)
                  ·
                    rfl

theorem cell20_1017559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 3].length) (baseStart_1017559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017559 prefixEnd_1017559 := by exact prefixLift 1017559
  have htrace : WordTrace (prefixWord ++ tailWord_1017559) baseStart_1017559 baseEnd_1017559 := by
    simpa [prefixWord, tailWord_1017559, baseEnd_1017559] using wordTrace_append hprefix tailTrace_1017559
  have hstable : (prefixWord ++ tailWord_1017559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017559).length < 2 ^ (prefixWord ++ tailWord_1017559).sum := by decide
  have hdescent : baseEnd_1017559 < baseStart_1017559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017576 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 3]
def baseStart_1017576 : Nat := 118140960795 + 1017576 * 2 ^ 59
def prefixEnd_1017576 : Nat := 4983230072969 + 3 ^ 40 * 1017576 * 2
def baseEnd_1017576 : Nat := 464449413759658633706897

theorem tailTrace_1017576 : CollatzResearch.WordTrace tailWord_1017576 prefixEnd_1017576 464449413759658633706897 := by
  unfold tailWord_1017576
  simp only [CollatzResearch.WordTrace]
  refine ⟨18557022880751707494964291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24742697174335609993285721 18557022880751707494964291)
  ·
    refine ⟨27835534321127561242446437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18557022880751707494964291 27835534321127561242446437)
    ·
      refine ⟨5219162685211417732958707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27835534321127561242446437 5219162685211417732958707)
      ·
        refine ⟨7828744027817126599438061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5219162685211417732958707 7828744027817126599438061)
        ·
          refine ⟨2935779010431422474789273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7828744027817126599438061 2935779010431422474789273)
          ·
            refine ⟨2201834257823566856091955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2935779010431422474789273 2201834257823566856091955)
            ·
              refine ⟨3302751386735350284137933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2201834257823566856091955 3302751386735350284137933)
              ·
                refine ⟨1238531770025756356551725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3302751386735350284137933 1238531770025756356551725)
                ·
                  refine ⟨464449413759658633706897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238531770025756356551725 464449413759658633706897)
                  ·
                    rfl

theorem cell20_1017576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_1017576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017576 prefixEnd_1017576 := by exact prefixLift 1017576
  have htrace : WordTrace (prefixWord ++ tailWord_1017576) baseStart_1017576 baseEnd_1017576 := by
    simpa [prefixWord, tailWord_1017576, baseEnd_1017576] using wordTrace_append hprefix tailTrace_1017576
  have hstable : (prefixWord ++ tailWord_1017576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017576).length < 2 ^ (prefixWord ++ tailWord_1017576).sum := by decide
  have hdescent : baseEnd_1017576 < baseStart_1017576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017590 : List Nat := [5, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1017590 : Nat := 118140960795 + 1017590 * 2 ^ 59
def prefixEnd_1017590 : Nat := 4983230072969 + 3 ^ 40 * 1017590 * 2
def baseEnd_1017590 : Nat := 154818601247045602413391

theorem tailTrace_1017590 : CollatzResearch.WordTrace tailWord_1017590 prefixEnd_1017590 154818601247045602413391 := by
  unfold tailWord_1017590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319659773965793461308639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24743037588968463587292149 2319659773965793461308639)
  ·
    refine ⟨3479489660948690191962959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2319659773965793461308639 3479489660948690191962959)
    ·
      refine ⟨5219234491423035287944439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3479489660948690191962959 5219234491423035287944439)
      ·
        refine ⟨7828851737134552931916659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5219234491423035287944439 7828851737134552931916659)
        ·
          refine ⟨11743277605701829397874989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7828851737134552931916659 11743277605701829397874989)
          ·
            refine ⟨4403729102138186024203121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11743277605701829397874989 4403729102138186024203121)
            ·
              refine ⟨3302796826603639518152341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4403729102138186024203121 3302796826603639518152341)
              ·
                refine ⟨154818601247045602413391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3302796826603639518152341 154818601247045602413391)
                ·
                  rfl

theorem cell20_1017590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1017590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017590 prefixEnd_1017590 := by exact prefixLift 1017590
  have htrace : WordTrace (prefixWord ++ tailWord_1017590) baseStart_1017590 baseEnd_1017590 := by
    simpa [prefixWord, tailWord_1017590, baseEnd_1017590] using wordTrace_append hprefix tailTrace_1017590
  have hstable : (prefixWord ++ tailWord_1017590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017590).length < 2 ^ (prefixWord ++ tailWord_1017590).sum := by decide
  have hdescent : baseEnd_1017590 < baseStart_1017590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017620 : List Nat := [2, 4, 4, 1, 2, 1, 1, 5]
def baseStart_1017620 : Nat := 118140960795 + 1017620 * 2 ^ 59
def prefixEnd_1017620 : Nat := 4983230072969 + 3 ^ 40 * 1017620 * 2
def baseEnd_1017620 : Nat := 154823165519530012080017

theorem tailTrace_1017620 : CollatzResearch.WordTrace tailWord_1017620 prefixEnd_1017620 154823165519530012080017 := by
  unfold tailWord_1017620
  simp only [CollatzResearch.WordTrace]
  refine ⟨18557825286672005252265157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24743767048896007003020209 18557825286672005252265157)
  ·
    refine ⟨3479592241251000984799717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18557825286672005252265157 3479592241251000984799717)
    ·
      refine ⟨652423545234562684649947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3479592241251000984799717 652423545234562684649947)
      ·
        refine ⟨978635317851844026974921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652423545234562684649947 978635317851844026974921)
        ·
          refine ⟨733976488388883020231191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978635317851844026974921 733976488388883020231191)
          ·
            refine ⟨1100964732583324530346787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733976488388883020231191 1100964732583324530346787)
            ·
              refine ⟨1651447098874986795520181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100964732583324530346787 1651447098874986795520181)
              ·
                refine ⟨154823165519530012080017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1651447098874986795520181 154823165519530012080017)
                ·
                  rfl

theorem cell20_1017620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_1017620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017620 prefixEnd_1017620 := by exact prefixLift 1017620
  have htrace : WordTrace (prefixWord ++ tailWord_1017620) baseStart_1017620 baseEnd_1017620 := by
    simpa [prefixWord, tailWord_1017620, baseEnd_1017620] using wordTrace_append hprefix tailTrace_1017620
  have hstable : (prefixWord ++ tailWord_1017620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017620).length < 2 ^ (prefixWord ++ tailWord_1017620).sum := by decide
  have hdescent : baseEnd_1017620 < baseStart_1017620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017635 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 3]
def baseStart_1017635 : Nat := 118140960795 + 1017635 * 2 ^ 59
def prefixEnd_1017635 : Nat := 4983230072969 + 3 ^ 40 * 1017635 * 2
def baseEnd_1017635 : Nat := 464476342967316650739989

theorem tailTrace_1017635 : CollatzResearch.WordTrace tailWord_1017635 prefixEnd_1017635 464476342967316650739989 := by
  unfold tailWord_1017635
  simp only [CollatzResearch.WordTrace]
  refine ⟨37116197668289668066326359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24744131778859778710884239 37116197668289668066326359)
  ·
    refine ⟨55674296502434502099489539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37116197668289668066326359 55674296502434502099489539)
    ·
      refine ⟨83511444753651753149234309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55674296502434502099489539 83511444753651753149234309)
      ·
        refine ⟨15658395891309703715481433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83511444753651753149234309 15658395891309703715481433)
        ·
          refine ⟨11743796918482277786611075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15658395891309703715481433 11743796918482277786611075)
          ·
            refine ⟨17615695377723416679916613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11743796918482277786611075 17615695377723416679916613)
            ·
              refine ⟨3302942883323140627484365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17615695377723416679916613 3302942883323140627484365)
              ·
                refine ⟨1238603581246177735306637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3302942883323140627484365 1238603581246177735306637)
                ·
                  refine ⟨464476342967316650739989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238603581246177735306637 464476342967316650739989)
                  ·
                    rfl

theorem cell20_1017635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 3].length) (baseStart_1017635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017635 prefixEnd_1017635 := by exact prefixLift 1017635
  have htrace : WordTrace (prefixWord ++ tailWord_1017635) baseStart_1017635 baseEnd_1017635 := by
    simpa [prefixWord, tailWord_1017635, baseEnd_1017635] using wordTrace_append hprefix tailTrace_1017635
  have hstable : (prefixWord ++ tailWord_1017635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017635).length < 2 ^ (prefixWord ++ tailWord_1017635).sum := by decide
  have hdescent : baseEnd_1017635 < baseStart_1017635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017690 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_1017690 : Nat := 118140960795 + 1017690 * 2 ^ 59
def prefixEnd_1017690 : Nat := 4983230072969 + 3 ^ 40 * 1017690 * 2
def baseEnd_1017690 : Nat := 464501446465980903906431

theorem tailTrace_1017690 : CollatzResearch.WordTrace tailWord_1017690 prefixEnd_1017690 464501446465980903906431 := by
  unfold tailWord_1017690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9279550920772603114894631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24745469122060274973052349 9279550920772603114894631)
  ·
    refine ⟨13919326381158904672341947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9279550920772603114894631 13919326381158904672341947)
    ·
      refine ⟨20878989571738357008512921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13919326381158904672341947 20878989571738357008512921)
      ·
        refine ⟨15659242178803767756384691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20878989571738357008512921 15659242178803767756384691)
        ·
          refine ⟨23488863268205651634577037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15659242178803767756384691 23488863268205651634577037)
          ·
            refine ⟨8808323725577119362966389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23488863268205651634577037 8808323725577119362966389)
            ·
              refine ⟨825780349272854940278099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8808323725577119362966389 825780349272854940278099)
              ·
                refine ⟨1238670523909282410417149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825780349272854940278099 1238670523909282410417149)
                ·
                  refine ⟨464501446465980903906431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238670523909282410417149 464501446465980903906431)
                  ·
                    rfl

theorem cell20_1017690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_1017690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017690 prefixEnd_1017690 := by exact prefixLift 1017690
  have htrace : WordTrace (prefixWord ++ tailWord_1017690) baseStart_1017690 baseEnd_1017690 := by
    simpa [prefixWord, tailWord_1017690, baseEnd_1017690] using wordTrace_append hprefix tailTrace_1017690
  have hstable : (prefixWord ++ tailWord_1017690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017690).length < 2 ^ (prefixWord ++ tailWord_1017690).sum := by decide
  have hdescent : baseEnd_1017690 < baseStart_1017690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017700 : List Nat := [2, 3, 1, 1, 6, 1, 2, 4]
def baseStart_1017700 : Nat := 118140960795 + 1017700 * 2 ^ 59
def prefixEnd_1017700 : Nat := 4983230072969 + 3 ^ 40 * 1017700 * 2
def baseEnd_1017700 : Nat := 154835336912821771191019

theorem tailTrace_1017700 : CollatzResearch.WordTrace tailWord_1017700 prefixEnd_1017700 154835336912821771191019 := by
  unfold tailWord_1017700
  simp only [CollatzResearch.WordTrace]
  refine ⟨18559284206527092083721277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24745712275369456111628369 18559284206527092083721277)
  ·
    refine ⟨6959731577447659531395479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18559284206527092083721277 6959731577447659531395479)
    ·
      refine ⟨10439597366171489297093219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6959731577447659531395479 10439597366171489297093219)
      ·
        refine ⟨15659396049257233945639829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10439597366171489297093219 15659396049257233945639829)
        ·
          refine ⟨734034189808932841201867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15659396049257233945639829 734034189808932841201867)
          ·
            refine ⟨1101051284713399261802801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734034189808932841201867 1101051284713399261802801)
            ·
              refine ⟨825788463535049446352101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101051284713399261802801 825788463535049446352101)
              ·
                refine ⟨154835336912821771191019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825788463535049446352101 154835336912821771191019)
                ·
                  rfl

theorem cell20_1017700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_1017700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017700 prefixEnd_1017700 := by exact prefixLift 1017700
  have htrace : WordTrace (prefixWord ++ tailWord_1017700) baseStart_1017700 baseEnd_1017700 := by
    simpa [prefixWord, tailWord_1017700, baseEnd_1017700] using wordTrace_append hprefix tailTrace_1017700
  have hstable : (prefixWord ++ tailWord_1017700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017700).length < 2 ^ (prefixWord ++ tailWord_1017700).sum := by decide
  have hdescent : baseEnd_1017700 < baseStart_1017700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017749 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 3]
def baseStart_1017749 : Nat := 118140960795 + 1017749 * 2 ^ 59
def prefixEnd_1017749 : Nat := 4983230072969 + 3 ^ 40 * 1017749 * 2
def baseEnd_1017749 : Nat := 464528375673638920939523

theorem tailTrace_1017749 : CollatzResearch.WordTrace tailWord_1017749 prefixEnd_1017749 464528375673638920939523 := by
  unfold tailWord_1017749
  simp only [CollatzResearch.WordTrace]
  refine ⟨37120355589876665535976301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24746903726584443690650867 37120355589876665535976301)
  ·
    refine ⟨13920133346203749575991113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37120355589876665535976301 13920133346203749575991113)
    ·
      refine ⟨10440100009652812181993335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13920133346203749575991113 10440100009652812181993335)
      ·
        refine ⟨15660150014479218272990003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10440100009652812181993335 15660150014479218272990003)
        ·
          refine ⟨23490225021718827409485005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15660150014479218272990003 23490225021718827409485005)
          ·
            refine ⟨8808834383144560278556877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23490225021718827409485005 8808834383144560278556877)
            ·
              refine ⟨3303312893679210104458829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8808834383144560278556877 3303312893679210104458829)
              ·
                refine ⟨1238742335129703789172061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3303312893679210104458829 1238742335129703789172061)
                ·
                  refine ⟨464528375673638920939523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238742335129703789172061 464528375673638920939523)
                  ·
                    rfl

theorem cell20_1017749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_1017749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017749 prefixEnd_1017749 := by exact prefixLift 1017749
  have htrace : WordTrace (prefixWord ++ tailWord_1017749) baseStart_1017749 baseEnd_1017749 := by
    simpa [prefixWord, tailWord_1017749, baseEnd_1017749] using wordTrace_append hprefix tailTrace_1017749
  have hstable : (prefixWord ++ tailWord_1017749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017749).length < 2 ^ (prefixWord ++ tailWord_1017749).sum := by decide
  have hdescent : baseEnd_1017749 < baseStart_1017749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017780 : List Nat := [2, 5, 2, 1, 10]
def baseStart_1017780 : Nat := 118140960795 + 1017780 * 2 ^ 59
def prefixEnd_1017780 : Nat := 4983230072969 + 3 ^ 40 * 1017780 * 2
def baseEnd_1017780 : Nat := 5735092900226427048223

theorem tailTrace_1017780 : CollatzResearch.WordTrace tailWord_1017780 prefixEnd_1017780 5735092900226427048223 := by
  unfold tailWord_1017780
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560743126382178915177397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24747657501842905220236529 18560743126382178915177397)
  ·
    refine ⟨1740069668098329273297881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18560743126382178915177397 1740069668098329273297881)
    ·
      refine ⟨1305052251073746954973411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1740069668098329273297881 1305052251073746954973411)
      ·
        refine ⟨1957578376610620432460117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305052251073746954973411 1957578376610620432460117)
        ·
          refine ⟨5735092900226427048223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1957578376610620432460117 5735092900226427048223)
          ·
            rfl

theorem cell20_1017780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 10].length) (baseStart_1017780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017780 prefixEnd_1017780 := by exact prefixLift 1017780
  have htrace : WordTrace (prefixWord ++ tailWord_1017780) baseStart_1017780 baseEnd_1017780 := by
    simpa [prefixWord, tailWord_1017780, baseEnd_1017780] using wordTrace_append hprefix tailTrace_1017780
  have hstable : (prefixWord ++ tailWord_1017780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017780).length < 2 ^ (prefixWord ++ tailWord_1017780).sum := by decide
  have hdescent : baseEnd_1017780 < baseStart_1017780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017790 : List Nat := [4, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_1017790 : Nat := 118140960795 + 1017790 * 2 ^ 59
def prefixEnd_1017790 : Nat := 4983230072969 + 3 ^ 40 * 1017790 * 2
def baseEnd_1017790 : Nat := 464547089190825000572689

theorem tailTrace_1017790 : CollatzResearch.WordTrace tailWord_1017790 prefixEnd_1017790 464547089190825000572689 := by
  unfold tailWord_1017790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640231372841016192277353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24747900655152086358812549 4640231372841016192277353)
  ·
    refine ⟨3480173529630762144208015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4640231372841016192277353 3480173529630762144208015)
    ·
      refine ⟨5220260294446143216312023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480173529630762144208015 5220260294446143216312023)
      ·
        refine ⟨7830390441669214824468035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5220260294446143216312023 7830390441669214824468035)
        ·
          refine ⟨11745585662503822236702053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7830390441669214824468035 11745585662503822236702053)
          ·
            refine ⟨2202297311719466669381635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11745585662503822236702053 2202297311719466669381635)
            ·
              refine ⟨3303445967579200004072453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202297311719466669381635 3303445967579200004072453)
              ·
                refine ⟨619396118921100000763585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3303445967579200004072453 619396118921100000763585)
                ·
                  refine ⟨464547089190825000572689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619396118921100000763585 464547089190825000572689)
                  ·
                    rfl

theorem cell20_1017790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_1017790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017790 prefixEnd_1017790 := by exact prefixLift 1017790
  have htrace : WordTrace (prefixWord ++ tailWord_1017790) baseStart_1017790 baseEnd_1017790 := by
    simpa [prefixWord, tailWord_1017790, baseEnd_1017790] using wordTrace_append hprefix tailTrace_1017790
  have hstable : (prefixWord ++ tailWord_1017790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017790).length < 2 ^ (prefixWord ++ tailWord_1017790).sum := by decide
  have hdescent : baseEnd_1017790 < baseStart_1017790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017814 : List Nat := [5, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1017814 : Nat := 118140960795 + 1017814 * 2 ^ 59
def prefixEnd_1017814 : Nat := 4983230072969 + 3 ^ 40 * 1017814 * 2
def baseEnd_1017814 : Nat := 154852681148262527924197

theorem tailTrace_1017814 : CollatzResearch.WordTrace tailWord_1017814 prefixEnd_1017814 154852681148262527924197 := by
  unfold tailWord_1017814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320170395915073852318281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24748484223094121091394997 2320170395915073852318281)
  ·
    refine ⟨1740127796936305389238711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2320170395915073852318281 1740127796936305389238711)
    ·
      refine ⟨2610191695404458083858067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740127796936305389238711 2610191695404458083858067)
      ·
        refine ⟨3915287543106687125787101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610191695404458083858067 3915287543106687125787101)
        ·
          refine ⟨1468232828665007672170163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3915287543106687125787101 1468232828665007672170163)
          ·
            refine ⟨2202349242997511508255245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468232828665007672170163 2202349242997511508255245)
            ·
              refine ⟨825880966124066815595717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202349242997511508255245 825880966124066815595717)
              ·
                refine ⟨154852681148262527924197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825880966124066815595717 154852681148262527924197)
                ·
                  rfl

theorem cell20_1017814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1017814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017814 prefixEnd_1017814 := by exact prefixLift 1017814
  have htrace : WordTrace (prefixWord ++ tailWord_1017814) baseStart_1017814 baseEnd_1017814 := by
    simpa [prefixWord, tailWord_1017814, baseEnd_1017814] using wordTrace_append hprefix tailTrace_1017814
  have hstable : (prefixWord ++ tailWord_1017814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017814).length < 2 ^ (prefixWord ++ tailWord_1017814).sum := by decide
  have hdescent : baseEnd_1017814 < baseStart_1017814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017849 : List Nat := [1, 2, 1, 3, 1, 4, 2, 4, 2]
def baseStart_1017849 : Nat := 118140960795 + 1017849 * 2 ^ 59
def prefixEnd_1017849 : Nat := 4983230072969 + 3 ^ 40 * 1017849 * 2
def baseEnd_1017849 : Nat := 464574018398483017605781

theorem tailTrace_1017849 : CollatzResearch.WordTrace tailWord_1017849 prefixEnd_1017849 464574018398483017605781 := by
  unfold tailWord_1017849
  simp only [CollatzResearch.WordTrace]
  refine ⟨37124002889514382614616601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24749335259676255076411067 37124002889514382614616601)
  ·
    refine ⟨27843002167135786960962451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37124002889514382614616601 27843002167135786960962451)
    ·
      refine ⟨41764503250703680441443677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27843002167135786960962451 41764503250703680441443677)
      ·
        refine ⟨15661688719013880165541379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41764503250703680441443677 15661688719013880165541379)
        ·
          refine ⟨23492533078520820248312069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15661688719013880165541379 23492533078520820248312069)
          ·
            refine ⟨4404849952222653796558513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23492533078520820248312069 4404849952222653796558513)
            ·
              refine ⟨3303637464166990347418885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4404849952222653796558513 3303637464166990347418885)
              ·
                refine ⟨619432024531310690141041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3303637464166990347418885 619432024531310690141041)
                ·
                  refine ⟨464574018398483017605781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619432024531310690141041 464574018398483017605781)
                  ·
                    rfl

theorem cell20_1017849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_1017849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017849 prefixEnd_1017849 := by exact prefixLift 1017849
  have htrace : WordTrace (prefixWord ++ tailWord_1017849) baseStart_1017849 baseEnd_1017849 := by
    simpa [prefixWord, tailWord_1017849, baseEnd_1017849] using wordTrace_append hprefix tailTrace_1017849
  have hstable : (prefixWord ++ tailWord_1017849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017849).length < 2 ^ (prefixWord ++ tailWord_1017849).sum := by decide
  have hdescent : baseEnd_1017849 < baseStart_1017849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017870 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1017870 : Nat := 118140960795 + 1017870 * 2 ^ 59
def prefixEnd_1017870 : Nat := 4983230072969 + 3 ^ 40 * 1017870 * 2
def baseEnd_1017870 : Nat := 464583603370700277905695

theorem tailTrace_1017870 : CollatzResearch.WordTrace tailWord_1017870 prefixEnd_1017870 464583603370700277905695 := by
  unfold tailWord_1017870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640596102804787900141383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24749845881625535467420709 4640596102804787900141383)
  ·
    refine ⟨6960894154207181850212075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4640596102804787900141383 6960894154207181850212075)
    ·
      refine ⟨10441341231310772775318113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6960894154207181850212075 10441341231310772775318113)
      ·
        refine ⟨7831005923483079581488585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10441341231310772775318113 7831005923483079581488585)
        ·
          refine ⟨5873254442612309686116439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7831005923483079581488585 5873254442612309686116439)
          ·
            refine ⟨8809881663918464529174659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5873254442612309686116439 8809881663918464529174659)
            ·
              refine ⟨13214822495877696793761989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809881663918464529174659 13214822495877696793761989)
              ·
                refine ⟨2477779217977068148830373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13214822495877696793761989 2477779217977068148830373)
                ·
                  refine ⟨464583603370700277905695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477779217977068148830373 464583603370700277905695)
                  ·
                    rfl

theorem cell20_1017870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1017870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017870 prefixEnd_1017870 := by exact prefixLift 1017870
  have htrace : WordTrace (prefixWord ++ tailWord_1017870) baseStart_1017870 baseEnd_1017870 := by
    simpa [prefixWord, tailWord_1017870, baseEnd_1017870] using wordTrace_append hprefix tailTrace_1017870
  have hstable : (prefixWord ++ tailWord_1017870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017870).length < 2 ^ (prefixWord ++ tailWord_1017870).sum := by decide
  have hdescent : baseEnd_1017870 < baseStart_1017870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017904 : List Nat := [2, 1, 1, 1, 2, 6, 3, 2, 2]
def baseStart_1017904 : Nat := 118140960795 + 1017904 * 2 ^ 59
def prefixEnd_1017904 : Nat := 4983230072969 + 3 ^ 40 * 1017904 * 2
def baseEnd_1017904 : Nat := 464599121897147270772223

theorem tailTrace_1017904 : CollatzResearch.WordTrace tailWord_1017904 prefixEnd_1017904 464599121897147270772223 := by
  unfold tailWord_1017904
  simp only [CollatzResearch.WordTrace]
  refine ⟨18563004452157563503934383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24750672602876751338579177 18563004452157563503934383)
  ·
    refine ⟨27844506678236345255901575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18563004452157563503934383 27844506678236345255901575)
    ·
      refine ⟨41766760017354517883852363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27844506678236345255901575 41766760017354517883852363)
      ·
        refine ⟨62650140026031776825778545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41766760017354517883852363 62650140026031776825778545)
        ·
          refine ⟨46987605019523832619333909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62650140026031776825778545 46987605019523832619333909)
          ·
            refine ⟨2202543985290179654031277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46987605019523832619333909 2202543985290179654031277)
            ·
              refine ⟨825953994483817370261729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202543985290179654031277 825953994483817370261729)
              ·
                refine ⟨619465495862863027696297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825953994483817370261729 619465495862863027696297)
                ·
                  refine ⟨464599121897147270772223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619465495862863027696297 464599121897147270772223)
                  ·
                    rfl

theorem cell20_1017904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_1017904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017904 prefixEnd_1017904 := by exact prefixLift 1017904
  have htrace : WordTrace (prefixWord ++ tailWord_1017904) baseStart_1017904 baseEnd_1017904 := by
    simpa [prefixWord, tailWord_1017904, baseEnd_1017904] using wordTrace_append hprefix tailTrace_1017904
  have hstable : (prefixWord ++ tailWord_1017904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017904).length < 2 ^ (prefixWord ++ tailWord_1017904).sum := by decide
  have hdescent : baseEnd_1017904 < baseStart_1017904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017929 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_1017929 : Nat := 118140960795 + 1017929 * 2 ^ 59
def prefixEnd_1017929 : Nat := 4983230072969 + 3 ^ 40 * 1017929 * 2
def baseEnd_1017929 : Nat := 464610532578358294938787

theorem tailTrace_1017929 : CollatzResearch.WordTrace tailWord_1017929 prefixEnd_1017929 464610532578358294938787 := by
  unfold tailWord_1017929
  simp only [CollatzResearch.WordTrace]
  refine ⟨37126920729224556277528841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24751280486149704185019227 37126920729224556277528841)
  ·
    refine ⟨27845190546918417208146631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37126920729224556277528841 27845190546918417208146631)
    ·
      refine ⟨41767785820377625812219947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27845190546918417208146631 41767785820377625812219947)
      ·
        refine ⟨62651678730566438718329921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41767785820377625812219947 62651678730566438718329921)
        ·
          refine ⟨46988759047924829038747441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62651678730566438718329921 46988759047924829038747441)
          ·
            refine ⟨35241569285943621779060581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46988759047924829038747441 35241569285943621779060581)
            ·
              refine ⟨6607794241114429083573859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35241569285943621779060581 6607794241114429083573859)
              ·
                refine ⟨9911691361671643625360789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607794241114429083573859 9911691361671643625360789)
                ·
                  refine ⟨464610532578358294938787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9911691361671643625360789 464610532578358294938787)
                  ·
                    rfl

theorem cell20_1017929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_1017929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017929 prefixEnd_1017929 := by exact prefixLift 1017929
  have htrace : WordTrace (prefixWord ++ tailWord_1017929) baseStart_1017929 baseEnd_1017929 := by
    simpa [prefixWord, tailWord_1017929, baseEnd_1017929] using wordTrace_append hprefix tailTrace_1017929
  have hstable : (prefixWord ++ tailWord_1017929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017929).length < 2 ^ (prefixWord ++ tailWord_1017929).sum := by decide
  have hdescent : baseEnd_1017929 < baseStart_1017929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017970 : List Nat := [3, 2, 1, 2, 2, 4, 1, 5]
def baseStart_1017970 : Nat := 118140960795 + 1017970 * 2 ^ 59
def prefixEnd_1017970 : Nat := 4983230072969 + 3 ^ 40 * 1017970 * 2
def baseEnd_1017970 : Nat := 154876415365181458190651

theorem tailTrace_1017970 : CollatzResearch.WordTrace tailWord_1017970 prefixEnd_1017970 154876415365181458190651 := by
  unfold tailWord_1017970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282104030519005069942841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24752277414717346853180909 9282104030519005069942841)
  ·
    refine ⟨6961578022889253802457131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9282104030519005069942841 6961578022889253802457131)
    ·
      refine ⟨10442367034333880703685697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6961578022889253802457131 10442367034333880703685697)
      ·
        refine ⟨7831775275750410527764273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10442367034333880703685697 7831775275750410527764273)
        ·
          refine ⟨5873831456812807895823205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7831775275750410527764273 5873831456812807895823205)
          ·
            refine ⟨1101343398152401480466851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5873831456812807895823205 1101343398152401480466851)
            ·
              refine ⟨1652015097228602220700277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101343398152401480466851 1652015097228602220700277)
              ·
                refine ⟨154876415365181458190651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1652015097228602220700277 154876415365181458190651)
                ·
                  rfl

theorem cell20_1017970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_1017970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017970 prefixEnd_1017970 := by exact prefixLift 1017970
  have htrace : WordTrace (prefixWord ++ tailWord_1017970) baseStart_1017970 baseEnd_1017970 := by
    simpa [prefixWord, tailWord_1017970, baseEnd_1017970] using wordTrace_append hprefix tailTrace_1017970
  have hstable : (prefixWord ++ tailWord_1017970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017970).length < 2 ^ (prefixWord ++ tailWord_1017970).sum := by decide
  have hdescent : baseEnd_1017970 < baseStart_1017970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017977 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 3]
def baseStart_1017977 : Nat := 118140960795 + 1017977 * 2 ^ 59
def prefixEnd_1017977 : Nat := 4983230072969 + 3 ^ 40 * 1017977 * 2
def baseEnd_1017977 : Nat := 464632441086283461338591

theorem tailTrace_1017977 : CollatzResearch.WordTrace tailWord_1017977 prefixEnd_1017977 464632441086283461338591 := by
  unfold tailWord_1017977
  simp only [CollatzResearch.WordTrace]
  refine ⟨37128671433050660475276185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24752447622033773650184123 37128671433050660475276185)
  ·
    refine ⟨27846503574787995356457139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37128671433050660475276185 27846503574787995356457139)
    ·
      refine ⟨41769755362181993034685709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27846503574787995356457139 41769755362181993034685709)
      ·
        refine ⟨15663658260818247388007141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41769755362181993034685709 15663658260818247388007141)
        ·
          refine ⟨2936935923903421385251339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15663658260818247388007141 2936935923903421385251339)
          ·
            refine ⟨4405403885855132077877009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936935923903421385251339 4405403885855132077877009)
            ·
              refine ⟨3304052914391349058407757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4405403885855132077877009 3304052914391349058407757)
              ·
                refine ⟨1239019842896755896902909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3304052914391349058407757 1239019842896755896902909)
                ·
                  refine ⟨464632441086283461338591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239019842896755896902909 464632441086283461338591)
                  ·
                    rfl

theorem cell20_1017977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_1017977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1017977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1017977 prefixEnd_1017977 := by exact prefixLift 1017977
  have htrace : WordTrace (prefixWord ++ tailWord_1017977) baseStart_1017977 baseEnd_1017977 := by
    simpa [prefixWord, tailWord_1017977, baseEnd_1017977] using wordTrace_append hprefix tailTrace_1017977
  have hstable : (prefixWord ++ tailWord_1017977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017977).length < 2 ^ (prefixWord ++ tailWord_1017977).sum := by decide
  have hdescent : baseEnd_1017977 < baseStart_1017977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018005 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1018005 : Nat := 118140960795 + 1018005 * 2 ^ 59
def prefixEnd_1018005 : Nat := 4983230072969 + 3 ^ 40 * 1018005 * 2
def baseEnd_1018005 : Nat := 464645221049239808405143

theorem tailTrace_1018005 : CollatzResearch.WordTrace tailWord_1018005 prefixEnd_1018005 464645221049239808405143 := by
  unfold tailWord_1018005
  simp only [CollatzResearch.WordTrace]
  refine ⟨37129692676949221257295469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24753128451299480838196979 37129692676949221257295469)
  ·
    refine ⟨13923634753855957971485801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37129692676949221257295469 13923634753855957971485801)
    ·
      refine ⟨10442726065391968478614351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13923634753855957971485801 10442726065391968478614351)
      ·
        refine ⟨15664089098087952717921527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10442726065391968478614351 15664089098087952717921527)
        ·
          refine ⟨23496133647131929076882291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15664089098087952717921527 23496133647131929076882291)
          ·
            refine ⟨35244200470697893615323437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23496133647131929076882291 35244200470697893615323437)
            ·
              refine ⟨13216575176511710105746289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35244200470697893615323437 13216575176511710105746289)
              ·
                refine ⟨9912431382383782579309717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13216575176511710105746289 9912431382383782579309717)
                ·
                  refine ⟨464645221049239808405143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9912431382383782579309717 464645221049239808405143)
                  ·
                    rfl

theorem cell20_1018005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1018005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018005 prefixEnd_1018005 := by exact prefixLift 1018005
  have htrace : WordTrace (prefixWord ++ tailWord_1018005) baseStart_1018005 baseEnd_1018005 := by
    simpa [prefixWord, tailWord_1018005, baseEnd_1018005] using wordTrace_append hprefix tailTrace_1018005
  have hstable : (prefixWord ++ tailWord_1018005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018005).length < 2 ^ (prefixWord ++ tailWord_1018005).sum := by decide
  have hdescent : baseEnd_1018005 < baseStart_1018005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018015 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 5]
def baseStart_1018015 : Nat := 118140960795 + 1018015 * 2 ^ 59
def prefixEnd_1018015 : Nat := 4983230072969 + 3 ^ 40 * 1018015 * 2
def baseEnd_1018015 : Nat := 464649785321724218071769

theorem tailTrace_1018015 : CollatzResearch.WordTrace tailWord_1018015 prefixEnd_1018015 464649785321724218071769 := by
  unfold tailWord_1018015
  simp only [CollatzResearch.WordTrace]
  refine ⟨37130057406912992965159499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24753371604608661976772999 37130057406912992965159499)
  ·
    refine ⟨55695086110369489447739249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37130057406912992965159499 55695086110369489447739249)
    ·
      refine ⟨41771314582777117085804437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55695086110369489447739249 41771314582777117085804437)
      ·
        refine ⟨1958030371067677363397083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41771314582777117085804437 1958030371067677363397083)
        ·
          refine ⟨2937045556601516045095625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958030371067677363397083 2937045556601516045095625)
          ·
            refine ⟨2202784167451137033821719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937045556601516045095625 2202784167451137033821719)
            ·
              refine ⟨3304176251176705550732579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202784167451137033821719 3304176251176705550732579)
              ·
                refine ⟨4956264376765058326098869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304176251176705550732579 4956264376765058326098869)
                ·
                  refine ⟨464649785321724218071769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4956264376765058326098869 464649785321724218071769)
                  ·
                    rfl

theorem cell20_1018015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_1018015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018015 prefixEnd_1018015 := by exact prefixLift 1018015
  have htrace : WordTrace (prefixWord ++ tailWord_1018015) baseStart_1018015 baseEnd_1018015 := by
    simpa [prefixWord, tailWord_1018015, baseEnd_1018015] using wordTrace_append hprefix tailTrace_1018015
  have hstable : (prefixWord ++ tailWord_1018015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018015).length < 2 ^ (prefixWord ++ tailWord_1018015).sum := by decide
  have hdescent : baseEnd_1018015 < baseStart_1018015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018018 : List Nat := [3, 3, 1, 3, 1, 1, 2, 4, 2]
def baseStart_1018018 : Nat := 118140960795 + 1018018 * 2 ^ 59
def prefixEnd_1018018 : Nat := 4983230072969 + 3 ^ 40 * 1018018 * 2
def baseEnd_1018018 : Nat := 464651154603469540971757

theorem tailTrace_1018018 : CollatzResearch.WordTrace tailWord_1018018 prefixEnd_1018018 464651154603469540971757 := by
  unfold tailWord_1018018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282541706475531119379677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24753444550601416318345805 9282541706475531119379677)
  ·
    refine ⟨3480953139928324169767379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9282541706475531119379677 3480953139928324169767379)
    ·
      refine ⟨5221429709892486254651069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480953139928324169767379 5221429709892486254651069)
      ·
        refine ⟨1958036141209682345494151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5221429709892486254651069 1958036141209682345494151)
        ·
          refine ⟨2937054211814523518241227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958036141209682345494151 2937054211814523518241227)
          ·
            refine ⟨4405581317721785277361841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937054211814523518241227 4405581317721785277361841)
            ·
              refine ⟨3304185988291338958021381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4405581317721785277361841 3304185988291338958021381)
              ·
                refine ⟨619534872804626054629009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3304185988291338958021381 619534872804626054629009)
                ·
                  refine ⟨464651154603469540971757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619534872804626054629009 464651154603469540971757)
                  ·
                    rfl

theorem cell20_1018018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_1018018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018018 prefixEnd_1018018 := by exact prefixLift 1018018
  have htrace : WordTrace (prefixWord ++ tailWord_1018018) baseStart_1018018 baseEnd_1018018 := by
    simpa [prefixWord, tailWord_1018018, baseEnd_1018018] using wordTrace_append hprefix tailTrace_1018018
  have hstable : (prefixWord ++ tailWord_1018018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018018).length < 2 ^ (prefixWord ++ tailWord_1018018).sum := by decide
  have hdescent : baseEnd_1018018 < baseStart_1018018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018043 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_1018043 : Nat := 118140960795 + 1018043 * 2 ^ 59
def prefixEnd_1018043 : Nat := 4983230072969 + 3 ^ 40 * 1018043 * 2
def baseEnd_1018043 : Nat := 464662565284680565138321

theorem tailTrace_1018043 : CollatzResearch.WordTrace tailWord_1018043 prefixEnd_1018043 464662565284680565138321 := by
  unfold tailWord_1018043
  simp only [CollatzResearch.WordTrace]
  refine ⟨37131078650811553747178783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24754052433874369164785855 37131078650811553747178783)
  ·
    refine ⟨55696617976217330620768175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37131078650811553747178783 55696617976217330620768175)
    ·
      refine ⟨83544926964325995931152263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55696617976217330620768175 83544926964325995931152263)
      ·
        refine ⟨125317390446488993896728395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83544926964325995931152263 125317390446488993896728395)
        ·
          refine ⟨187976085669733490845092593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125317390446488993896728395 187976085669733490845092593)
          ·
            refine ⟨140982064252300118133819445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187976085669733490845092593 140982064252300118133819445)
            ·
              refine ⟨13217068523653136075045573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140982064252300118133819445 13217068523653136075045573)
              ·
                refine ⟨2478200348184963014071045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13217068523653136075045573 2478200348184963014071045)
                ·
                  refine ⟨464662565284680565138321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2478200348184963014071045 464662565284680565138321)
                  ·
                    rfl

theorem cell20_1018043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_1018043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018043 prefixEnd_1018043 := by exact prefixLift 1018043
  have htrace : WordTrace (prefixWord ++ tailWord_1018043) baseStart_1018043 baseEnd_1018043 := by
    simpa [prefixWord, tailWord_1018043, baseEnd_1018043] using wordTrace_append hprefix tailTrace_1018043
  have hstable : (prefixWord ++ tailWord_1018043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018043).length < 2 ^ (prefixWord ++ tailWord_1018043).sum := by decide
  have hdescent : baseEnd_1018043 < baseStart_1018043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018046 : List Nat := [4, 2, 1, 1, 4, 1, 1, 6]
def baseStart_1018046 : Nat := 118140960795 + 1018046 * 2 ^ 59
def prefixEnd_1018046 : Nat := 4983230072969 + 3 ^ 40 * 1018046 * 2
def baseEnd_1018046 : Nat := 154887978188808629346103

theorem tailTrace_1018046 : CollatzResearch.WordTrace tailWord_1018046 prefixEnd_1018046 154887978188808629346103 := by
  unfold tailWord_1018046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4641398508725085657442249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24754125379867123506358661 4641398508725085657442249)
  ·
    refine ⟨3481048881543814243081687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4641398508725085657442249 3481048881543814243081687)
    ·
      refine ⟨5221573322315721364622531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3481048881543814243081687 5221573322315721364622531)
      ·
        refine ⟨7832359983473582046933797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5221573322315721364622531 7832359983473582046933797)
        ·
          refine ⟨1468567496901296633800087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7832359983473582046933797 1468567496901296633800087)
          ·
            refine ⟨2202851245351944950700131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468567496901296633800087 2202851245351944950700131)
            ·
              refine ⟨3304276868027917426050197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202851245351944950700131 3304276868027917426050197)
              ·
                refine ⟨154887978188808629346103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3304276868027917426050197 154887978188808629346103)
                ·
                  rfl

theorem cell20_1018046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_1018046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018046 prefixEnd_1018046 := by exact prefixLift 1018046
  have htrace : WordTrace (prefixWord ++ tailWord_1018046) baseStart_1018046 baseEnd_1018046 := by
    simpa [prefixWord, tailWord_1018046, baseEnd_1018046] using wordTrace_append hprefix tailTrace_1018046
  have hstable : (prefixWord ++ tailWord_1018046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018046).length < 2 ^ (prefixWord ++ tailWord_1018046).sum := by decide
  have hdescent : baseEnd_1018046 < baseStart_1018046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018070 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1018070 : Nat := 118140960795 + 1018070 * 2 ^ 59
def prefixEnd_1018070 : Nat := 4983230072969 + 3 ^ 40 * 1018070 * 2
def baseEnd_1018070 : Nat := 464674888820388471238211

theorem tailTrace_1018070 : CollatzResearch.WordTrace tailWord_1018070 prefixEnd_1018070 464674888820388471238211 := by
  unfold tailWord_1018070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320753963857108584900729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24754708947809158238941109 2320753963857108584900729)
  ·
    refine ⟨1740565472892831438675547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2320753963857108584900729 1740565472892831438675547)
    ·
      refine ⟨2610848209339247158013321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740565472892831438675547 2610848209339247158013321)
      ·
        refine ⟨1958136157004435368509991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2610848209339247158013321 1958136157004435368509991)
        ·
          refine ⟨2937204235506653052764987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958136157004435368509991 2937204235506653052764987)
          ·
            refine ⟨4405806353259979579147481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937204235506653052764987 4405806353259979579147481)
            ·
              refine ⟨3304354764944984684360611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4405806353259979579147481 3304354764944984684360611)
              ·
                refine ⟨4956532147417477026540917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304354764944984684360611 4956532147417477026540917)
                ·
                  refine ⟨464674888820388471238211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4956532147417477026540917 464674888820388471238211)
                  ·
                    rfl

theorem cell20_1018070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1018070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018070 prefixEnd_1018070 := by exact prefixLift 1018070
  have htrace : WordTrace (prefixWord ++ tailWord_1018070) baseStart_1018070 baseEnd_1018070 := by
    simpa [prefixWord, tailWord_1018070, baseEnd_1018070] using wordTrace_append hprefix tailTrace_1018070
  have hstable : (prefixWord ++ tailWord_1018070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018070).length < 2 ^ (prefixWord ++ tailWord_1018070).sum := by decide
  have hdescent : baseEnd_1018070 < baseStart_1018070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018074 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_1018074 : Nat := 118140960795 + 1018074 * 2 ^ 59
def prefixEnd_1018074 : Nat := 4983230072969 + 3 ^ 40 * 1018074 * 2
def baseEnd_1018074 : Nat := 464676714529382235104861

theorem tailTrace_1018074 : CollatzResearch.WordTrace tailWord_1018074 prefixEnd_1018074 464676714529382235104861 := by
  unfold tailWord_1018074
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283052328424811510389319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24754806209132830694371517 9283052328424811510389319)
  ·
    refine ⟨13924578492637217265583979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9283052328424811510389319 13924578492637217265583979)
    ·
      refine ⟨20886867738955825898375969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13924578492637217265583979 20886867738955825898375969)
      ·
        refine ⟨15665150804216869423781977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20886867738955825898375969 15665150804216869423781977)
        ·
          refine ⟨11748863103162652067836483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15665150804216869423781977 11748863103162652067836483)
          ·
            refine ⟨17623294654743978101754725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11748863103162652067836483 17623294654743978101754725)
            ·
              refine ⟨3304367747764495894079011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17623294654743978101754725 3304367747764495894079011)
              ·
                refine ⟨4956551621646743841118517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304367747764495894079011 4956551621646743841118517)
                ·
                  refine ⟨464676714529382235104861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4956551621646743841118517 464676714529382235104861)
                  ·
                    rfl

theorem cell20_1018074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_1018074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018074 prefixEnd_1018074 := by exact prefixLift 1018074
  have htrace : WordTrace (prefixWord ++ tailWord_1018074) baseStart_1018074 baseEnd_1018074 := by
    simpa [prefixWord, tailWord_1018074, baseEnd_1018074] using wordTrace_append hprefix tailTrace_1018074
  have hstable : (prefixWord ++ tailWord_1018074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018074).length < 2 ^ (prefixWord ++ tailWord_1018074).sum := by decide
  have hdescent : baseEnd_1018074 < baseStart_1018074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018077 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1018077 : Nat := 118140960795 + 1018077 * 2 ^ 59
def prefixEnd_1018077 : Nat := 4983230072969 + 3 ^ 40 * 1018077 * 2
def baseEnd_1018077 : Nat := 464678083811127558004849

theorem tailTrace_1018077 : CollatzResearch.WordTrace tailWord_1018077 prefixEnd_1018077 464678083811127558004849 := by
  unfold tailWord_1018077
  simp only [CollatzResearch.WordTrace]
  refine ⟨37132318732688377553916485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24754879155125585035944323 37132318732688377553916485)
  ·
    refine ⟨6962309762379070791359341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37132318732688377553916485 6962309762379070791359341)
    ·
      refine ⟨2610866160892151546759753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6962309762379070791359341 2610866160892151546759753)
      ·
        refine ⟨1958149620669113660069815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2610866160892151546759753 1958149620669113660069815)
        ·
          refine ⟨2937224431003670490104723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958149620669113660069815 2937224431003670490104723)
          ·
            refine ⟨4405836646505505735157085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937224431003670490104723 4405836646505505735157085)
            ·
              refine ⟨1652188742439564650683907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4405836646505505735157085 1652188742439564650683907)
              ·
                refine ⟨2478283113659346976025861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652188742439564650683907 2478283113659346976025861)
                ·
                  refine ⟨464678083811127558004849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2478283113659346976025861 464678083811127558004849)
                  ·
                    rfl

theorem cell20_1018077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1018077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018077 prefixEnd_1018077 := by exact prefixLift 1018077
  have htrace : WordTrace (prefixWord ++ tailWord_1018077) baseStart_1018077 baseEnd_1018077 := by
    simpa [prefixWord, tailWord_1018077, baseEnd_1018077] using wordTrace_append hprefix tailTrace_1018077
  have hstable : (prefixWord ++ tailWord_1018077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018077).length < 2 ^ (prefixWord ++ tailWord_1018077).sum := by decide
  have hdescent : baseEnd_1018077 < baseStart_1018077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018087 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 3]
def baseStart_1018087 : Nat := 118140960795 + 1018087 * 2 ^ 59
def prefixEnd_1018087 : Nat := 4983230072969 + 3 ^ 40 * 1018087 * 2
def baseEnd_1018087 : Nat := 464682648083611967671475

theorem tailTrace_1018087 : CollatzResearch.WordTrace tailWord_1018087 prefixEnd_1018087 464682648083611967671475 := by
  unfold tailWord_1018087
  simp only [CollatzResearch.WordTrace]
  refine ⟨37132683462652149261780515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24755122308434766174520343 37132683462652149261780515)
  ·
    refine ⟨55699025193978223892670773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37132683462652149261780515 55699025193978223892670773)
    ·
      refine ⟨5221783611935458489937885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55699025193978223892670773 5221783611935458489937885)
      ·
        refine ⟨1958168854475796933726707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5221783611935458489937885 1958168854475796933726707)
        ·
          refine ⟨2937253281713695400590061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958168854475796933726707 2937253281713695400590061)
          ·
            refine ⟨1101469980642635775221273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2937253281713695400590061 1101469980642635775221273)
            ·
              refine ⟨826102485481976831415955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101469980642635775221273 826102485481976831415955)
              ·
                refine ⟨1239153728222965247123933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826102485481976831415955 1239153728222965247123933)
                ·
                  refine ⟨464682648083611967671475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239153728222965247123933 464682648083611967671475)
                  ·
                    rfl

theorem cell20_1018087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 3].length) (baseStart_1018087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018087 prefixEnd_1018087 := by exact prefixLift 1018087
  have htrace : WordTrace (prefixWord ++ tailWord_1018087) baseStart_1018087 baseEnd_1018087 := by
    simpa [prefixWord, tailWord_1018087, baseEnd_1018087] using wordTrace_append hprefix tailTrace_1018087
  have hstable : (prefixWord ++ tailWord_1018087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018087).length < 2 ^ (prefixWord ++ tailWord_1018087).sum := by decide
  have hdescent : baseEnd_1018087 < baseStart_1018087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018129 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 3]
def baseStart_1018129 : Nat := 118140960795 + 1018129 * 2 ^ 59
def prefixEnd_1018129 : Nat := 4983230072969 + 3 ^ 40 * 1018129 * 2
def baseEnd_1018129 : Nat := 464701818028046488271303

theorem tailTrace_1018129 : CollatzResearch.WordTrace tailWord_1018129 prefixEnd_1018129 464701818028046488271303 := by
  unfold tailWord_1018129
  simp only [CollatzResearch.WordTrace]
  refine ⟨37134215328499990434809441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24756143552333326956539627 37134215328499990434809441)
  ·
    refine ⟨27850661496374992826107081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37134215328499990434809441 27850661496374992826107081)
    ·
      refine ⟨20887996122281244619580311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27850661496374992826107081 20887996122281244619580311)
      ·
        refine ⟨31331994183421866929370467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20887996122281244619580311 31331994183421866929370467)
        ·
          refine ⟨46997991275132800394055701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31331994183421866929370467 46997991275132800394055701)
          ·
            refine ⟨2203030841021850018471361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46997991275132800394055701 2203030841021850018471361)
            ·
              refine ⟨1652273130766387513853521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203030841021850018471361 1652273130766387513853521)
              ·
                refine ⟨1239204848074790635390141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652273130766387513853521 1239204848074790635390141)
                ·
                  refine ⟨464701818028046488271303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239204848074790635390141 464701818028046488271303)
                  ·
                    rfl

theorem cell20_1018129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_1018129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018129 prefixEnd_1018129 := by exact prefixLift 1018129
  have htrace : WordTrace (prefixWord ++ tailWord_1018129) baseStart_1018129 baseEnd_1018129 := by
    simpa [prefixWord, tailWord_1018129, baseEnd_1018129] using wordTrace_append hprefix tailTrace_1018129
  have hstable : (prefixWord ++ tailWord_1018129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018129).length < 2 ^ (prefixWord ++ tailWord_1018129).sum := by decide
  have hdescent : baseEnd_1018129 < baseStart_1018129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018143 : List Nat := [1, 1, 2, 4, 3, 1, 3, 5]
def baseStart_1018143 : Nat := 118140960795 + 1018143 * 2 ^ 59
def prefixEnd_1018143 : Nat := 4983230072969 + 3 ^ 40 * 1018143 * 2
def baseEnd_1018143 : Nat := 154902736003174887268193

theorem tailTrace_1018143 : CollatzResearch.WordTrace tailWord_1018143 prefixEnd_1018143 154902736003174887268193 := by
  unfold tailWord_1018143
  simp only [CollatzResearch.WordTrace]
  refine ⟨37134725950449270825819083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24756483966966180550546055 37134725950449270825819083)
  ·
    refine ⟨55702088925673906238728625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37134725950449270825819083 55702088925673906238728625)
    ·
      refine ⟨41776566694255429679046469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55702088925673906238728625 41776566694255429679046469)
      ·
        refine ⟨7833106255172893064821213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41776566694255429679046469 7833106255172893064821213)
        ·
          refine ⟨2937414845689834899307955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7833106255172893064821213 2937414845689834899307955)
          ·
            refine ⟨4406122268534752348961933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937414845689834899307955 4406122268534752348961933)
            ·
              refine ⟨1652295850700532130860725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4406122268534752348961933 1652295850700532130860725)
              ·
                refine ⟨154902736003174887268193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1652295850700532130860725 154902736003174887268193)
                ·
                  rfl

theorem cell20_1018143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_1018143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018143 prefixEnd_1018143 := by exact prefixLift 1018143
  have htrace : WordTrace (prefixWord ++ tailWord_1018143) baseStart_1018143 baseEnd_1018143 := by
    simpa [prefixWord, tailWord_1018143, baseEnd_1018143] using wordTrace_append hprefix tailTrace_1018143
  have hstable : (prefixWord ++ tailWord_1018143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018143).length < 2 ^ (prefixWord ++ tailWord_1018143).sum := by decide
  have hdescent : baseEnd_1018143 < baseStart_1018143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018180 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 3]
def baseStart_1018180 : Nat := 118140960795 + 1018180 * 2 ^ 59
def prefixEnd_1018180 : Nat := 4983230072969 + 3 ^ 40 * 1018180 * 2
def baseEnd_1018180 : Nat := 464725095817716977571095

theorem tailTrace_1018180 : CollatzResearch.WordTrace tailWord_1018180 prefixEnd_1018180 464725095817716977571095 := by
  unfold tailWord_1018180
  simp only [CollatzResearch.WordTrace]
  refine ⟨18568037725657613072457997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24757383634210150763277329 18568037725657613072457997)
  ·
    refine ⟨6963014147121604902171749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18568037725657613072457997 6963014147121604902171749)
    ·
      refine ⟨1305565152585300919157203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6963014147121604902171749 1305565152585300919157203)
      ·
        refine ⟨1958347728877951378735805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305565152585300919157203 1958347728877951378735805)
        ·
          refine ⟨734380398329231767025927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1958347728877951378735805 734380398329231767025927)
          ·
            refine ⟨1101570597493847650538891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734380398329231767025927 1101570597493847650538891)
            ·
              refine ⟨1652355896240771475808337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101570597493847650538891 1652355896240771475808337)
              ·
                refine ⟨1239266922180578606856253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652355896240771475808337 1239266922180578606856253)
                ·
                  refine ⟨464725095817716977571095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239266922180578606856253 464725095817716977571095)
                  ·
                    rfl

theorem cell20_1018180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_1018180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018180 prefixEnd_1018180 := by exact prefixLift 1018180
  have htrace : WordTrace (prefixWord ++ tailWord_1018180) baseStart_1018180 baseEnd_1018180 := by
    simpa [prefixWord, tailWord_1018180, baseEnd_1018180] using wordTrace_append hprefix tailTrace_1018180
  have hstable : (prefixWord ++ tailWord_1018180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018180).length < 2 ^ (prefixWord ++ tailWord_1018180).sum := by decide
  have hdescent : baseEnd_1018180 < baseStart_1018180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018188 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_1018188 : Nat := 118140960795 + 1018188 * 2 ^ 59
def prefixEnd_1018188 : Nat := 4983230072969 + 3 ^ 40 * 1018188 * 2
def baseEnd_1018188 : Nat := 464728747235704505304395

theorem tailTrace_1018188 : CollatzResearch.WordTrace tailWord_1018188 prefixEnd_1018188 464728747235704505304395 := by
  unfold tailWord_1018188
  simp only [CollatzResearch.WordTrace]
  refine ⟨18568183617643121755603609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24757578156857495674138145 18568183617643121755603609)
  ·
    refine ⟨13926137713232341316702707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18568183617643121755603609 13926137713232341316702707)
    ·
      refine ⟨20889206569848511975054061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13926137713232341316702707 20889206569848511975054061)
      ·
        refine ⟨7833452463693191990645273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20889206569848511975054061 7833452463693191990645273)
        ·
          refine ⟨5875089347769893992983955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7833452463693191990645273 5875089347769893992983955)
          ·
            refine ⟨8812634021654840989475933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875089347769893992983955 8812634021654840989475933)
            ·
              refine ⟨3304737758120565371053475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8812634021654840989475933 3304737758120565371053475)
              ·
                refine ⟨4957106637180848056580213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304737758120565371053475 4957106637180848056580213)
                ·
                  refine ⟨464728747235704505304395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4957106637180848056580213 464728747235704505304395)
                  ·
                    rfl

theorem cell20_1018188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_1018188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018188 prefixEnd_1018188 := by exact prefixLift 1018188
  have htrace : WordTrace (prefixWord ++ tailWord_1018188) baseStart_1018188 baseEnd_1018188 := by
    simpa [prefixWord, tailWord_1018188, baseEnd_1018188] using wordTrace_append hprefix tailTrace_1018188
  have hstable : (prefixWord ++ tailWord_1018188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018188).length < 2 ^ (prefixWord ++ tailWord_1018188).sum := by decide
  have hdescent : baseEnd_1018188 < baseStart_1018188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018202 : List Nat := [3, 1, 1, 2, 1, 2, 1, 9]
def baseStart_1018202 : Nat := 118140960795 + 1018202 * 2 ^ 59
def prefixEnd_1018202 : Nat := 4983230072969 + 3 ^ 40 * 1018202 * 2
def baseEnd_1018202 : Nat := 154911712405727559612557

theorem tailTrace_1018202 : CollatzResearch.WordTrace tailWord_1018202 prefixEnd_1018202 154911712405727559612557 := by
  unfold tailWord_1018202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9284219464308880975554215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24757918571490349268144573 9284219464308880975554215)
  ·
    refine ⟨13926329196463321463331323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9284219464308880975554215 13926329196463321463331323)
    ·
      refine ⟨20889493794694982194996985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13926329196463321463331323 20889493794694982194996985)
      ·
        refine ⟨15667120346021236646247739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20889493794694982194996985 15667120346021236646247739)
        ·
          refine ⟨23500680519031854969371609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15667120346021236646247739 23500680519031854969371609)
          ·
            refine ⟨17625510389273891227028707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23500680519031854969371609 17625510389273891227028707)
            ·
              refine ⟨26438265583910836840543061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17625510389273891227028707 26438265583910836840543061)
              ·
                refine ⟨154911712405727559612557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26438265583910836840543061 154911712405727559612557)
                ·
                  rfl

theorem cell20_1018202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_1018202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018202 prefixEnd_1018202 := by exact prefixLift 1018202
  have htrace : WordTrace (prefixWord ++ tailWord_1018202) baseStart_1018202 baseEnd_1018202 := by
    simpa [prefixWord, tailWord_1018202, baseEnd_1018202] using wordTrace_append hprefix tailTrace_1018202
  have hstable : (prefixWord ++ tailWord_1018202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018202).length < 2 ^ (prefixWord ++ tailWord_1018202).sum := by decide
  have hdescent : baseEnd_1018202 < baseStart_1018202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018226 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1018226 : Nat := 118140960795 + 1018226 * 2 ^ 59
def prefixEnd_1018226 : Nat := 4983230072969 + 3 ^ 40 * 1018226 * 2
def baseEnd_1018226 : Nat := 464746091471145262037573

theorem tailTrace_1018226 : CollatzResearch.WordTrace tailWord_1018226 prefixEnd_1018226 464746091471145262037573 := by
  unfold tailWord_1018226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9284438302287144000272633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24758502139432384000727021 9284438302287144000272633)
  ·
    refine ⟨6963328726715358000204475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9284438302287144000272633 6963328726715358000204475)
    ·
      refine ⟨10444993090073037000306713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6963328726715358000204475 10444993090073037000306713)
      ·
        refine ⟨7833744817554777750230035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10444993090073037000306713 7833744817554777750230035)
        ·
          refine ⟨11750617226332166625345053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7833744817554777750230035 11750617226332166625345053)
          ·
            refine ⟨4406481459874562484504395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11750617226332166625345053 4406481459874562484504395)
            ·
              refine ⟨6609722189811843726756593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4406481459874562484504395 6609722189811843726756593)
              ·
                refine ⟨4957291642358882795067445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6609722189811843726756593 4957291642358882795067445)
                ·
                  refine ⟨464746091471145262037573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4957291642358882795067445 464746091471145262037573)
                  ·
                    rfl

theorem cell20_1018226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1018226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018226 prefixEnd_1018226 := by exact prefixLift 1018226
  have htrace : WordTrace (prefixWord ++ tailWord_1018226) baseStart_1018226 baseEnd_1018226 := by
    simpa [prefixWord, tailWord_1018226, baseEnd_1018226] using wordTrace_append hprefix tailTrace_1018226
  have hstable : (prefixWord ++ tailWord_1018226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018226).length < 2 ^ (prefixWord ++ tailWord_1018226).sum := by decide
  have hdescent : baseEnd_1018226 < baseStart_1018226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018242 : List Nat := [3, 4, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1018242 : Nat := 118140960795 + 1018242 * 2 ^ 59
def prefixEnd_1018242 : Nat := 4983230072969 + 3 ^ 40 * 1018242 * 2
def baseEnd_1018242 : Nat := 464753394307120317504175

theorem tailTrace_1018242 : CollatzResearch.WordTrace tailWord_1018242 prefixEnd_1018242 464753394307120317504175 := by
  unfold tailWord_1018242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9284584194272652683418245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24758891184727073822448653 9284584194272652683418245)
  ·
    refine ⟨1740859536426122378140921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9284584194272652683418245 1740859536426122378140921)
    ·
      refine ⟨1305644652319591783605691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1740859536426122378140921 1305644652319591783605691)
      ·
        refine ⟨1958466978479387675408537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305644652319591783605691 1958466978479387675408537)
        ·
          refine ⟨1468850233859540756556403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1958466978479387675408537 1468850233859540756556403)
          ·
            refine ⟨2203275350789311134834605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468850233859540756556403 2203275350789311134834605)
            ·
              refine ⟨826228256545991675562977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2203275350789311134834605 826228256545991675562977)
              ·
                refine ⟨619671192409493756672233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826228256545991675562977 619671192409493756672233)
                ·
                  refine ⟨464753394307120317504175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619671192409493756672233 464753394307120317504175)
                  ·
                    rfl

theorem cell20_1018242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1018242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018242 prefixEnd_1018242 := by exact prefixLift 1018242
  have htrace : WordTrace (prefixWord ++ tailWord_1018242) baseStart_1018242 baseEnd_1018242 := by
    simpa [prefixWord, tailWord_1018242, baseEnd_1018242] using wordTrace_append hprefix tailTrace_1018242
  have hstable : (prefixWord ++ tailWord_1018242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018242).length < 2 ^ (prefixWord ++ tailWord_1018242).sum := by decide
  have hdescent : baseEnd_1018242 < baseStart_1018242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018260 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1018260 : Nat := 118140960795 + 1018260 * 2 ^ 59
def prefixEnd_1018260 : Nat := 4983230072969 + 3 ^ 40 * 1018260 * 2
def baseEnd_1018260 : Nat := 464761609997592254904101

theorem tailTrace_1018260 : CollatzResearch.WordTrace tailWord_1018260 prefixEnd_1018260 464761609997592254904101 := by
  unfold tailWord_1018260
  simp only [CollatzResearch.WordTrace]
  refine ⟨18569496645512699903914117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24759328860683599871885489 18569496645512699903914117)
  ·
    refine ⟨3481780621033631231983897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18569496645512699903914117 3481780621033631231983897)
    ·
      refine ⟨2611335465775223423987923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3481780621033631231983897 2611335465775223423987923)
      ·
        refine ⟨3917003198662835135981885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611335465775223423987923 3917003198662835135981885)
        ·
          refine ⟨1468876199498563175993207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3917003198662835135981885 1468876199498563175993207)
          ·
            refine ⟨2203314299247844763989811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468876199498563175993207 2203314299247844763989811)
            ·
              refine ⟨3304971448871767145984717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203314299247844763989811 3304971448871767145984717)
              ·
                refine ⟨1239364293326912679744269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3304971448871767145984717 1239364293326912679744269)
                ·
                  refine ⟨464761609997592254904101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239364293326912679744269 464761609997592254904101)
                  ·
                    rfl

theorem cell20_1018260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1018260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018260 prefixEnd_1018260 := by exact prefixLift 1018260
  have htrace : WordTrace (prefixWord ++ tailWord_1018260) baseStart_1018260 baseEnd_1018260 := by
    simpa [prefixWord, tailWord_1018260, baseEnd_1018260] using wordTrace_append hprefix tailTrace_1018260
  have hstable : (prefixWord ++ tailWord_1018260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018260).length < 2 ^ (prefixWord ++ tailWord_1018260).sum := by decide
  have hdescent : baseEnd_1018260 < baseStart_1018260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018271 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_1018271 : Nat := 118140960795 + 1018271 * 2 ^ 59
def prefixEnd_1018271 : Nat := 4983230072969 + 3 ^ 40 * 1018271 * 2
def baseEnd_1018271 : Nat := 464766630697325105537389

theorem tailTrace_1018271 : CollatzResearch.WordTrace tailWord_1018271 prefixEnd_1018271 464766630697325105537389 := by
  unfold tailWord_1018271
  simp only [CollatzResearch.WordTrace]
  refine ⟨37139394493985548686478667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24759596329323699124319111 37139394493985548686478667)
  ·
    refine ⟨55709091740978323029718001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37139394493985548686478667 55709091740978323029718001)
    ·
      refine ⟨41781818805733742272288501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55709091740978323029718001 41781818805733742272288501)
      ·
        refine ⟨3917045513037538338027047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41781818805733742272288501 3917045513037538338027047)
        ·
          refine ⟨5875568269556307507040571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917045513037538338027047 5875568269556307507040571)
          ·
            refine ⟨8813352404334461260560857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875568269556307507040571 8813352404334461260560857)
            ·
              refine ⟨6610014303250845945420643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8813352404334461260560857 6610014303250845945420643)
              ·
                refine ⟨9915021454876268918130965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610014303250845945420643 9915021454876268918130965)
                ·
                  refine ⟨464766630697325105537389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9915021454876268918130965 464766630697325105537389)
                  ·
                    rfl

theorem cell20_1018271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_1018271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018271 prefixEnd_1018271 := by exact prefixLift 1018271
  have htrace : WordTrace (prefixWord ++ tailWord_1018271) baseStart_1018271 baseEnd_1018271 := by
    simpa [prefixWord, tailWord_1018271, baseEnd_1018271] using wordTrace_append hprefix tailTrace_1018271
  have hstable : (prefixWord ++ tailWord_1018271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018271).length < 2 ^ (prefixWord ++ tailWord_1018271).sum := by decide
  have hdescent : baseEnd_1018271 < baseStart_1018271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018302 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1018302 : Nat := 118140960795 + 1018302 * 2 ^ 59
def prefixEnd_1018302 : Nat := 4983230072969 + 3 ^ 40 * 1018302 * 2
def baseEnd_1018302 : Nat := 464780779942026775503929

theorem tailTrace_1018302 : CollatzResearch.WordTrace tailWord_1018302 prefixEnd_1018302 464780779942026775503929 := by
  unfold tailWord_1018302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642565644609155122607145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24760350104582160653904773 4642565644609155122607145)
  ·
    refine ⟨3481924233456866341955359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4642565644609155122607145 3481924233456866341955359)
    ·
      refine ⟨5222886350185299512933039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3481924233456866341955359 5222886350185299512933039)
      ·
        refine ⟨7834329525277949269399559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5222886350185299512933039 7834329525277949269399559)
        ·
          refine ⟨11751494287916923904099339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7834329525277949269399559 11751494287916923904099339)
          ·
            refine ⟨17627241431875385856149009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11751494287916923904099339 17627241431875385856149009)
            ·
              refine ⟨13220431073906539392111757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17627241431875385856149009 13220431073906539392111757)
              ·
                refine ⟨4957661652714952272041909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13220431073906539392111757 4957661652714952272041909)
                ·
                  refine ⟨464780779942026775503929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4957661652714952272041909 464780779942026775503929)
                  ·
                    rfl

theorem cell20_1018302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1018302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018302 prefixEnd_1018302 := by exact prefixLift 1018302
  have htrace : WordTrace (prefixWord ++ tailWord_1018302) baseStart_1018302 baseEnd_1018302 := by
    simpa [prefixWord, tailWord_1018302, baseEnd_1018302] using wordTrace_append hprefix tailTrace_1018302
  have hstable : (prefixWord ++ tailWord_1018302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018302).length < 2 ^ (prefixWord ++ tailWord_1018302).sum := by decide
  have hdescent : baseEnd_1018302 < baseStart_1018302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018343 : List Nat := [1, 1, 5, 2, 1, 1, 4, 3, 2]
def baseStart_1018343 : Nat := 118140960795 + 1018343 * 2 ^ 59
def prefixEnd_1018343 : Nat := 4983230072969 + 3 ^ 40 * 1018343 * 2
def baseEnd_1018343 : Nat := 464799493459212855137095

theorem tailTrace_1018343 : CollatzResearch.WordTrace tailWord_1018343 prefixEnd_1018343 464799493459212855137095 := by
  unfold tailWord_1018343
  simp only [CollatzResearch.WordTrace]
  refine ⟨37142020549724704983099683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24761347033149803322066455 37142020549724704983099683)
  ·
    refine ⟨55713030824587057474649525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37142020549724704983099683 55713030824587057474649525)
    ·
      refine ⟨5223096639805036638248393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55713030824587057474649525 5223096639805036638248393)
      ·
        refine ⟨3917322479853777478686295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5223096639805036638248393 3917322479853777478686295)
        ·
          refine ⟨5875983719780666218029443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917322479853777478686295 5875983719780666218029443)
          ·
            refine ⟨8813975579670999327044165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875983719780666218029443 8813975579670999327044165)
            ·
              refine ⟨1652620421188312373820781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8813975579670999327044165 1652620421188312373820781)
              ·
                refine ⟨619732657945617140182793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1652620421188312373820781 619732657945617140182793)
                ·
                  refine ⟨464799493459212855137095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619732657945617140182793 464799493459212855137095)
                  ·
                    rfl

theorem cell20_1018343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 2].length) (baseStart_1018343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018343 prefixEnd_1018343 := by exact prefixLift 1018343
  have htrace : WordTrace (prefixWord ++ tailWord_1018343) baseStart_1018343 baseEnd_1018343 := by
    simpa [prefixWord, tailWord_1018343, baseEnd_1018343] using wordTrace_append hprefix tailTrace_1018343
  have hstable : (prefixWord ++ tailWord_1018343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018343).length < 2 ^ (prefixWord ++ tailWord_1018343).sum := by decide
  have hdescent : baseEnd_1018343 < baseStart_1018343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018388 : List Nat := [2, 4, 3, 1, 1, 2, 1, 6]
def baseStart_1018388 : Nat := 118140960795 + 1018388 * 2 ^ 59
def prefixEnd_1018388 : Nat := 4983230072969 + 3 ^ 40 * 1018388 * 2
def baseEnd_1018388 : Nat := 154940010895130899545637

theorem tailTrace_1018388 : CollatzResearch.WordTrace tailWord_1018388 prefixEnd_1018388 154940010895130899545637 := by
  unfold tailWord_1018388
  simp only [CollatzResearch.WordTrace]
  refine ⟨18571830917280838834243909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24762441223041118445658545 18571830917280838834243909)
  ·
    refine ⟨3482218296990157281420733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18571830917280838834243909 3482218296990157281420733)
    ·
      refine ⟨1305831861371308980532775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3482218296990157281420733 1305831861371308980532775)
      ·
        refine ⟨1958747792056963470799163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305831861371308980532775 1958747792056963470799163)
        ·
          refine ⟨2938121688085445206198745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958747792056963470799163 2938121688085445206198745)
          ·
            refine ⟨2203591266064083904649059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2938121688085445206198745 2203591266064083904649059)
            ·
              refine ⟨3305386899096125856973589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203591266064083904649059 3305386899096125856973589)
              ·
                refine ⟨154940010895130899545637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3305386899096125856973589 154940010895130899545637)
                ·
                  rfl

theorem cell20_1018388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_1018388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018388 prefixEnd_1018388 := by exact prefixLift 1018388
  have htrace : WordTrace (prefixWord ++ tailWord_1018388) baseStart_1018388 baseEnd_1018388 := by
    simpa [prefixWord, tailWord_1018388, baseEnd_1018388] using wordTrace_append hprefix tailTrace_1018388
  have hstable : (prefixWord ++ tailWord_1018388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018388).length < 2 ^ (prefixWord ++ tailWord_1018388).sum := by decide
  have hdescent : baseEnd_1018388 < baseStart_1018388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018419 : List Nat := [1, 1, 1, 2, 4, 2, 5, 2, 2]
def baseStart_1018419 : Nat := 118140960795 + 1018419 * 2 ^ 59
def prefixEnd_1018419 : Nat := 4983230072969 + 3 ^ 40 * 1018419 * 2
def baseEnd_1018419 : Nat := 464834181930094368603451

theorem tailTrace_1018419 : CollatzResearch.WordTrace tailWord_1018419 prefixEnd_1018419 464834181930094368603451 := by
  unfold tailWord_1018419
  simp only [CollatzResearch.WordTrace]
  refine ⟨37144792497449369962866311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24763194998299579975244207 37144792497449369962866311)
  ·
    refine ⟨55717188746174054944299467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37144792497449369962866311 55717188746174054944299467)
    ·
      refine ⟨83575783119261082416449201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55717188746174054944299467 83575783119261082416449201)
      ·
        refine ⟨62681837339445811812336901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83575783119261082416449201 62681837339445811812336901)
        ·
          refine ⟨11752844501146089714813169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62681837339445811812336901 11752844501146089714813169)
          ·
            refine ⟨8814633375859567286109877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11752844501146089714813169 8814633375859567286109877)
            ·
              refine ⟨826371878986834433072801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8814633375859567286109877 826371878986834433072801)
              ·
                refine ⟨619778909240125824804601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826371878986834433072801 619778909240125824804601)
                ·
                  refine ⟨464834181930094368603451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619778909240125824804601 464834181930094368603451)
                  ·
                    rfl

theorem cell20_1018419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 2].length) (baseStart_1018419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018419 prefixEnd_1018419 := by exact prefixLift 1018419
  have htrace : WordTrace (prefixWord ++ tailWord_1018419) baseStart_1018419 baseEnd_1018419 := by
    simpa [prefixWord, tailWord_1018419, baseEnd_1018419] using wordTrace_append hprefix tailTrace_1018419
  have hstable : (prefixWord ++ tailWord_1018419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018419).length < 2 ^ (prefixWord ++ tailWord_1018419).sum := by decide
  have hdescent : baseEnd_1018419 < baseStart_1018419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018433 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 3]
def baseStart_1018433 : Nat := 118140960795 + 1018433 * 2 ^ 59
def prefixEnd_1018433 : Nat := 4983230072969 + 3 ^ 40 * 1018433 * 2
def baseEnd_1018433 : Nat := 464840571911572542136727

theorem tailTrace_1018433 : CollatzResearch.WordTrace tailWord_1018433 prefixEnd_1018433 464840571911572542136727 := by
  unfold tailWord_1018433
  simp only [CollatzResearch.WordTrace]
  refine ⟨37145303119398650353875953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24763535412932433569250635 37145303119398650353875953)
  ·
    refine ⟨27858977339548987765406965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37145303119398650353875953 27858977339548987765406965)
    ·
      refine ⟨2611779125582717603006903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27858977339548987765406965 2611779125582717603006903)
      ·
        refine ⟨3917668688374076404510355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611779125582717603006903 3917668688374076404510355)
        ·
          refine ⟨5876503032561114606765533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917668688374076404510355 5876503032561114606765533)
          ·
            refine ⟨2203688637210417977537075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5876503032561114606765533 2203688637210417977537075)
            ·
              refine ⟨3305532955815626966305613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203688637210417977537075 3305532955815626966305613)
              ·
                refine ⟨1239574858430860112364605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3305532955815626966305613 1239574858430860112364605)
                ·
                  refine ⟨464840571911572542136727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239574858430860112364605 464840571911572542136727)
                  ·
                    rfl

theorem cell20_1018433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_1018433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018433 prefixEnd_1018433 := by exact prefixLift 1018433
  have htrace : WordTrace (prefixWord ++ tailWord_1018433) baseStart_1018433 baseEnd_1018433 := by
    simpa [prefixWord, tailWord_1018433, baseEnd_1018433] using wordTrace_append hprefix tailTrace_1018433
  have hstable : (prefixWord ++ tailWord_1018433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018433).length < 2 ^ (prefixWord ++ tailWord_1018433).sum := by decide
  have hdescent : baseEnd_1018433 < baseStart_1018433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018492 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1018492 : Nat := 118140960795 + 1018492 * 2 ^ 59
def prefixEnd_1018492 : Nat := 4983230072969 + 3 ^ 40 * 1018492 * 2
def baseEnd_1018492 : Nat := 464867501119230559169819

theorem tailTrace_1018492 : CollatzResearch.WordTrace tailWord_1018492 prefixEnd_1018492 464867501119230559169819 := by
  unfold tailWord_1018492
  simp only [CollatzResearch.WordTrace]
  refine ⟨18573727513092451715136865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24764970017456602286849153 18573727513092451715136865)
  ·
    refine ⟨13930295634819338786352649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18573727513092451715136865 13930295634819338786352649)
    ·
      refine ⟨10447721726114504089764487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13930295634819338786352649 10447721726114504089764487)
      ·
        refine ⟨15671582589171756134646731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10447721726114504089764487 15671582589171756134646731)
        ·
          refine ⟨23507373883757634201970097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15671582589171756134646731 23507373883757634201970097)
          ·
            refine ⟨17630530412818225651477573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23507373883757634201970097 17630530412818225651477573)
            ·
              refine ⟨3305724452403417309652045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17630530412818225651477573 3305724452403417309652045)
              ·
                refine ⟨1239646669651281491119517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3305724452403417309652045 1239646669651281491119517)
                ·
                  refine ⟨464867501119230559169819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239646669651281491119517 464867501119230559169819)
                  ·
                    rfl

theorem cell20_1018492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1018492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018492 prefixEnd_1018492 := by exact prefixLift 1018492
  have htrace : WordTrace (prefixWord ++ tailWord_1018492) baseStart_1018492 baseEnd_1018492 := by
    simpa [prefixWord, tailWord_1018492, baseEnd_1018492] using wordTrace_append hprefix tailTrace_1018492
  have hstable : (prefixWord ++ tailWord_1018492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018492).length < 2 ^ (prefixWord ++ tailWord_1018492).sum := by decide
  have hdescent : baseEnd_1018492 < baseStart_1018492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018547 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 3]
def baseStart_1018547 : Nat := 118140960795 + 1018547 * 2 ^ 59
def prefixEnd_1018547 : Nat := 4983230072969 + 3 ^ 40 * 1018547 * 2
def baseEnd_1018547 : Nat := 464892604617894812336261

theorem tailTrace_1018547 : CollatzResearch.WordTrace tailWord_1018547 prefixEnd_1018547 464892604617894812336261 := by
  unfold tailWord_1018547
  simp only [CollatzResearch.WordTrace]
  refine ⟨37149461040985647823525895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24766307360657098549017263 37149461040985647823525895)
  ·
    refine ⟨55724191561478471735288843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37149461040985647823525895 55724191561478471735288843)
    ·
      refine ⟨83586287342217707602933265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55724191561478471735288843 83586287342217707602933265)
      ·
        refine ⟨62689715506663280702199949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83586287342217707602933265 62689715506663280702199949)
        ·
          refine ⟨23508643314998730263324981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62689715506663280702199949 23508643314998730263324981)
          ·
            refine ⟨2203935310781130962186717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23508643314998730263324981 2203935310781130962186717)
            ·
              refine ⟨826475741542924110820019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2203935310781130962186717 826475741542924110820019)
              ·
                refine ⟨1239713612314386166230029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826475741542924110820019 1239713612314386166230029)
                ·
                  refine ⟨464892604617894812336261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239713612314386166230029 464892604617894812336261)
                  ·
                    rfl

theorem cell20_1018547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 3].length) (baseStart_1018547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018547 prefixEnd_1018547 := by exact prefixLift 1018547
  have htrace : WordTrace (prefixWord ++ tailWord_1018547) baseStart_1018547 baseEnd_1018547 := by
    simpa [prefixWord, tailWord_1018547, baseEnd_1018547] using wordTrace_append hprefix tailTrace_1018547
  have hstable : (prefixWord ++ tailWord_1018547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018547).length < 2 ^ (prefixWord ++ tailWord_1018547).sum := by decide
  have hdescent : baseEnd_1018547 < baseStart_1018547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018578 : List Nat := [3, 2, 2, 2, 4, 1, 6]
def baseStart_1018578 : Nat := 118140960795 + 1018578 * 2 ^ 59
def prefixEnd_1018578 : Nat := 4983230072969 + 3 ^ 40 * 1018578 * 2
def baseEnd_1018578 : Nat := 51656305984732942478089

theorem tailTrace_1018578 : CollatzResearch.WordTrace tailWord_1018578 prefixEnd_1018578 51656305984732942478089 := by
  unfold tailWord_1018578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9287647925968335029476097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24767061135915560078602925 9287647925968335029476097)
  ·
    refine ⟨6965735944476251272107073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9287647925968335029476097 6965735944476251272107073)
    ·
      refine ⟨5224301958357188454080305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6965735944476251272107073 5224301958357188454080305)
      ·
        refine ⟨3918226468767891340560229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5224301958357188454080305 3918226468767891340560229)
        ·
          refine ⟨734667462893979626355043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3918226468767891340560229 734667462893979626355043)
          ·
            refine ⟨1102001194340969439532565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734667462893979626355043 1102001194340969439532565)
            ·
              refine ⟨51656305984732942478089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1102001194340969439532565 51656305984732942478089)
              ·
                rfl

theorem cell20_1018578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 6].length) (baseStart_1018578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018578 prefixEnd_1018578 := by exact prefixLift 1018578
  have htrace : WordTrace (prefixWord ++ tailWord_1018578) baseStart_1018578 baseEnd_1018578 := by
    simpa [prefixWord, tailWord_1018578, baseEnd_1018578] using wordTrace_append hprefix tailTrace_1018578
  have hstable : (prefixWord ++ tailWord_1018578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018578).length < 2 ^ (prefixWord ++ tailWord_1018578).sum := by decide
  have hdescent : baseEnd_1018578 < baseStart_1018578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018620 : List Nat := [2, 2, 2, 1, 3, 2, 2, 6]
def baseStart_1018620 : Nat := 118140960795 + 1018620 * 2 ^ 59
def prefixEnd_1018620 : Nat := 4983230072969 + 3 ^ 40 * 1018620 * 2
def baseEnd_1018620 : Nat := 154975307935677000967543

theorem tailTrace_1018620 : CollatzResearch.WordTrace tailWord_1018620 prefixEnd_1018620 154975307935677000967543 := by
  unfold tailWord_1018620
  simp only [CollatzResearch.WordTrace]
  refine ⟨18576061784860590645466657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24768082379814120860622209 18576061784860590645466657)
  ·
    refine ⟨13932046338645442984099993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18576061784860590645466657 13932046338645442984099993)
    ·
      refine ⟨10449034753984082238074995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13932046338645442984099993 10449034753984082238074995)
      ·
        refine ⟨15673552130976123357112493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10449034753984082238074995 15673552130976123357112493)
        ·
          refine ⟨5877582049116046258917185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15673552130976123357112493 5877582049116046258917185)
          ·
            refine ⟨4408186536837034694187889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5877582049116046258917185 4408186536837034694187889)
            ·
              refine ⟨3306139902627776020640917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4408186536837034694187889 3306139902627776020640917)
              ·
                refine ⟨154975307935677000967543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3306139902627776020640917 154975307935677000967543)
                ·
                  rfl

theorem cell20_1018620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_1018620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018620 prefixEnd_1018620 := by exact prefixLift 1018620
  have htrace : WordTrace (prefixWord ++ tailWord_1018620) baseStart_1018620 baseEnd_1018620 := by
    simpa [prefixWord, tailWord_1018620, baseEnd_1018620] using wordTrace_append hprefix tailTrace_1018620
  have hstable : (prefixWord ++ tailWord_1018620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018620).length < 2 ^ (prefixWord ++ tailWord_1018620).sum := by decide
  have hdescent : baseEnd_1018620 < baseStart_1018620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018647 : List Nat := [1, 1, 3, 4, 3, 1, 1, 4, 2]
def baseStart_1018647 : Nat := 118140960795 + 1018647 * 2 ^ 59
def prefixEnd_1018647 : Nat := 4983230072969 + 3 ^ 40 * 1018647 * 2
def baseEnd_1018647 : Nat := 464938247342738909002519

theorem tailTrace_1018647 : CollatzResearch.WordTrace tailWord_1018647 prefixEnd_1018647 464938247342738909002519 := by
  unfold tailWord_1018647
  simp only [CollatzResearch.WordTrace]
  refine ⟨37153108340623364902166195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24768738893748909934777463 37153108340623364902166195)
  ·
    refine ⟨55729662510935047353249293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37153108340623364902166195 55729662510935047353249293)
    ·
      refine ⟨20898623441600642757468485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55729662510935047353249293 20898623441600642757468485)
      ·
        refine ⟨3918491895300120517025341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20898623441600642757468485 3918491895300120517025341)
        ·
          refine ⟨1469434460737545193884503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3918491895300120517025341 1469434460737545193884503)
          ·
            refine ⟨2204151691106317790826755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469434460737545193884503 2204151691106317790826755)
            ·
              refine ⟨3306227536659476686240133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204151691106317790826755 3306227536659476686240133)
              ·
                refine ⟨619917663123651878670025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3306227536659476686240133 619917663123651878670025)
                ·
                  refine ⟨464938247342738909002519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619917663123651878670025 464938247342738909002519)
                  ·
                    rfl

theorem cell20_1018647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 2].length) (baseStart_1018647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018647 prefixEnd_1018647 := by exact prefixLift 1018647
  have htrace : WordTrace (prefixWord ++ tailWord_1018647) baseStart_1018647 baseEnd_1018647 := by
    simpa [prefixWord, tailWord_1018647, baseEnd_1018647] using wordTrace_append hprefix tailTrace_1018647
  have hstable : (prefixWord ++ tailWord_1018647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018647).length < 2 ^ (prefixWord ++ tailWord_1018647).sum := by decide
  have hdescent : baseEnd_1018647 < baseStart_1018647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018675 : List Nat := [1, 1, 1, 2, 6, 2, 3, 4]
def baseStart_1018675 : Nat := 118140960795 + 1018675 * 2 ^ 59
def prefixEnd_1018675 : Nat := 4983230072969 + 3 ^ 40 * 1018675 * 2
def baseEnd_1018675 : Nat := 154983675768565085356357

theorem tailTrace_1018675 : CollatzResearch.WordTrace tailWord_1018675 prefixEnd_1018675 154983675768565085356357 := by
  unfold tailWord_1018675
  simp only [CollatzResearch.WordTrace]
  refine ⟨37154129584521925684185479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24769419723014617122790319 37154129584521925684185479)
  ·
    refine ⟨55731194376782888526278219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37154129584521925684185479 55731194376782888526278219)
    ·
      refine ⟨83596791565174332789417329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55731194376782888526278219 83596791565174332789417329)
      ·
        refine ⟨62697593673880749592062997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83596791565174332789417329 62697593673880749592062997)
        ·
          refine ⟨2938949703463160137127953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62697593673880749592062997 2938949703463160137127953)
          ·
            refine ⟨2204212277597370102845965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2938949703463160137127953 2204212277597370102845965)
            ·
              refine ⟨826579604099013788567237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2204212277597370102845965 826579604099013788567237)
              ·
                refine ⟨154983675768565085356357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 826579604099013788567237 154983675768565085356357)
                ·
                  rfl

theorem cell20_1018675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 4].length) (baseStart_1018675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018675 prefixEnd_1018675 := by exact prefixLift 1018675
  have htrace : WordTrace (prefixWord ++ tailWord_1018675) baseStart_1018675 baseEnd_1018675 := by
    simpa [prefixWord, tailWord_1018675, baseEnd_1018675] using wordTrace_append hprefix tailTrace_1018675
  have hstable : (prefixWord ++ tailWord_1018675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018675).length < 2 ^ (prefixWord ++ tailWord_1018675).sum := by decide
  have hdescent : baseEnd_1018675 < baseStart_1018675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018692 : List Nat := [2, 3, 4, 2, 1, 1, 7]
def baseStart_1018692 : Nat := 118140960795 + 1018692 * 2 ^ 59
def prefixEnd_1018692 : Nat := 4983230072969 + 3 ^ 40 * 1018692 * 2
def baseEnd_1018692 : Nat := 51662087396546528055815

theorem tailTrace_1018692 : CollatzResearch.WordTrace tailWord_1018692 prefixEnd_1018692 51662087396546528055815 := by
  unfold tailWord_1018692
  simp only [CollatzResearch.WordTrace]
  refine ⟨18577374812730168793777165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24769833083640225058369553 18577374812730168793777165)
  ·
    refine ⟨6966515554773813297666437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18577374812730168793777165 6966515554773813297666437)
    ·
      refine ⟨1306221666520089993312457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6966515554773813297666437 1306221666520089993312457)
      ·
        refine ⟨979666249890067494984343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1306221666520089993312457 979666249890067494984343)
        ·
          refine ⟨1469499374835101242476515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979666249890067494984343 1469499374835101242476515)
          ·
            refine ⟨2204249062252651863714773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469499374835101242476515 2204249062252651863714773)
            ·
              refine ⟨51662087396546528055815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2204249062252651863714773 51662087396546528055815)
              ·
                rfl

theorem cell20_1018692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 7].length) (baseStart_1018692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018692 prefixEnd_1018692 := by exact prefixLift 1018692
  have htrace : WordTrace (prefixWord ++ tailWord_1018692) baseStart_1018692 baseEnd_1018692 := by
    simpa [prefixWord, tailWord_1018692, baseEnd_1018692] using wordTrace_append hprefix tailTrace_1018692
  have hstable : (prefixWord ++ tailWord_1018692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018692).length < 2 ^ (prefixWord ++ tailWord_1018692).sum := by decide
  have hdescent : baseEnd_1018692 < baseStart_1018692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018706 : List Nat := [3, 2, 2, 1, 1, 2, 1, 6, 2]
def baseStart_1018706 : Nat := 118140960795 + 1018706 * 2 ^ 59
def prefixEnd_1018706 : Nat := 4983230072969 + 3 ^ 40 * 1018706 * 2
def baseEnd_1018706 : Nat := 464965176550396926035611

theorem tailTrace_1018706 : CollatzResearch.WordTrace tailWord_1018706 prefixEnd_1018706 464965176550396926035611 := by
  unfold tailWord_1018706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9288815061852404494640993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24770173498273078652375981 9288815061852404494640993)
  ·
    refine ⟨6966611296389303370980745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9288815061852404494640993 6966611296389303370980745)
    ·
      refine ⟨5224958472291977528235559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6966611296389303370980745 5224958472291977528235559)
      ·
        refine ⟨7837437708437966292353339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5224958472291977528235559 7837437708437966292353339)
        ·
          refine ⟨11756156562656949438530009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7837437708437966292353339 11756156562656949438530009)
          ·
            refine ⟨8817117421992712078897507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11756156562656949438530009 8817117421992712078897507)
            ·
              refine ⟨13225676132989068118346261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8817117421992712078897507 13225676132989068118346261)
              ·
                refine ⟨619953568733862568047481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13225676132989068118346261 619953568733862568047481)
                ·
                  refine ⟨464965176550396926035611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619953568733862568047481 464965176550396926035611)
                  ·
                    rfl

theorem cell20_1018706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_1018706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018706 prefixEnd_1018706 := by exact prefixLift 1018706
  have htrace : WordTrace (prefixWord ++ tailWord_1018706) baseStart_1018706 baseEnd_1018706 := by
    simpa [prefixWord, tailWord_1018706, baseEnd_1018706] using wordTrace_append hprefix tailTrace_1018706
  have hstable : (prefixWord ++ tailWord_1018706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018706).length < 2 ^ (prefixWord ++ tailWord_1018706).sum := by decide
  have hdescent : baseEnd_1018706 < baseStart_1018706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018716 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 3]
def baseStart_1018716 : Nat := 118140960795 + 1018716 * 2 ^ 59
def prefixEnd_1018716 : Nat := 4983230072969 + 3 ^ 40 * 1018716 * 2
def baseEnd_1018716 : Nat := 464969740822881335702237

theorem tailTrace_1018716 : CollatzResearch.WordTrace tailWord_1018716 prefixEnd_1018716 464969740822881335702237 := by
  unfold tailWord_1018716
  simp only [CollatzResearch.WordTrace]
  refine ⟨18577812488686694843214001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24770416651582259790952001 18577812488686694843214001)
  ·
    refine ⟨13933359366515021132410501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18577812488686694843214001 13933359366515021132410501)
    ·
      refine ⟨2612504881221566462326969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13933359366515021132410501 2612504881221566462326969)
      ·
        refine ⟨1959378660916174846745227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2612504881221566462326969 1959378660916174846745227)
        ·
          refine ⟨2939067991374262270117841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959378660916174846745227 2939067991374262270117841)
          ·
            refine ⟨2204300993530696702588381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2939067991374262270117841 2204300993530696702588381)
            ·
              refine ⟨826612872574011263470643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2204300993530696702588381 826612872574011263470643)
              ·
                refine ⟨1239919308861016895205965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826612872574011263470643 1239919308861016895205965)
                ·
                  refine ⟨464969740822881335702237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239919308861016895205965 464969740822881335702237)
                  ·
                    rfl

theorem cell20_1018716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_1018716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018716 prefixEnd_1018716 := by exact prefixLift 1018716
  have htrace : WordTrace (prefixWord ++ tailWord_1018716) baseStart_1018716 baseEnd_1018716 := by
    simpa [prefixWord, tailWord_1018716, baseEnd_1018716] using wordTrace_append hprefix tailTrace_1018716
  have hstable : (prefixWord ++ tailWord_1018716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018716).length < 2 ^ (prefixWord ++ tailWord_1018716).sum := by decide
  have hdescent : baseEnd_1018716 < baseStart_1018716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018727 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_1018727 : Nat := 118140960795 + 1018727 * 2 ^ 59
def prefixEnd_1018727 : Nat := 4983230072969 + 3 ^ 40 * 1018727 * 2
def baseEnd_1018727 : Nat := 464974761522614186335525

theorem tailTrace_1018727 : CollatzResearch.WordTrace tailWord_1018727 prefixEnd_1018727 464974761522614186335525 := by
  unfold tailWord_1018727
  simp only [CollatzResearch.WordTrace]
  refine ⟨37156026180333538565078435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24770684120222359043385623 37156026180333538565078435)
  ·
    refine ⟨55734039270500307847617653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37156026180333538565078435 55734039270500307847617653)
    ·
      refine ⟨5225066181609403860714155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55734039270500307847617653 5225066181609403860714155)
      ·
        refine ⟨7837599272414105791071233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225066181609403860714155 7837599272414105791071233)
        ·
          refine ⟨5878199454310579343303425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7837599272414105791071233 5878199454310579343303425)
          ·
            refine ⟨4408649590732934507477569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5878199454310579343303425 4408649590732934507477569)
            ·
              refine ⟨3306487193049700880608177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4408649590732934507477569 3306487193049700880608177)
              ·
                refine ⟨2479865394787275660456133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306487193049700880608177 2479865394787275660456133)
                ·
                  refine ⟨464974761522614186335525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2479865394787275660456133 464974761522614186335525)
                  ·
                    rfl

theorem cell20_1018727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_1018727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018727 prefixEnd_1018727 := by exact prefixLift 1018727
  have htrace : WordTrace (prefixWord ++ tailWord_1018727) baseStart_1018727 baseEnd_1018727 := by
    simpa [prefixWord, tailWord_1018727, baseEnd_1018727] using wordTrace_append hprefix tailTrace_1018727
  have hstable : (prefixWord ++ tailWord_1018727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018727).length < 2 ^ (prefixWord ++ tailWord_1018727).sum := by decide
  have hdescent : baseEnd_1018727 < baseStart_1018727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018748 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1018748 : Nat := 118140960795 + 1018748 * 2 ^ 59
def prefixEnd_1018748 : Nat := 4983230072969 + 3 ^ 40 * 1018748 * 2
def baseEnd_1018748 : Nat := 464984346494831446635439

theorem tailTrace_1018748 : CollatzResearch.WordTrace tailWord_1018748 prefixEnd_1018748 464984346494831446635439 := by
  unfold tailWord_1018748
  simp only [CollatzResearch.WordTrace]
  refine ⟨18578396056628729575796449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24771194742171639434395265 18578396056628729575796449)
  ·
    refine ⟨13933797042471547181847337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18578396056628729575796449 13933797042471547181847337)
    ·
      refine ⟨10450347781853660386385503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13933797042471547181847337 10450347781853660386385503)
      ·
        refine ⟨15675521672780490579578255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10450347781853660386385503 15675521672780490579578255)
        ·
          refine ⟨23513282509170735869367383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15675521672780490579578255 23513282509170735869367383)
          ·
            refine ⟨35269923763756103804051075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23513282509170735869367383 35269923763756103804051075)
            ·
              refine ⟨52904885645634155706076613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35269923763756103804051075 52904885645634155706076613)
              ·
                refine ⟨9919666058556404194889365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52904885645634155706076613 9919666058556404194889365)
                ·
                  refine ⟨464984346494831446635439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9919666058556404194889365 464984346494831446635439)
                  ·
                    rfl

theorem cell20_1018748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1018748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018748 prefixEnd_1018748 := by exact prefixLift 1018748
  have htrace : WordTrace (prefixWord ++ tailWord_1018748) baseStart_1018748 baseEnd_1018748 := by
    simpa [prefixWord, tailWord_1018748, baseEnd_1018748] using wordTrace_append hprefix tailTrace_1018748
  have hstable : (prefixWord ++ tailWord_1018748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018748).length < 2 ^ (prefixWord ++ tailWord_1018748).sum := by decide
  have hdescent : baseEnd_1018748 < baseStart_1018748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018761 : List Nat := [1, 2, 1, 1, 5, 3, 3, 2, 2]
def baseStart_1018761 : Nat := 118140960795 + 1018761 * 2 ^ 59
def prefixEnd_1018761 : Nat := 4983230072969 + 3 ^ 40 * 1018761 * 2
def baseEnd_1018761 : Nat := 464990280049061179202053

theorem tailTrace_1018761 : CollatzResearch.WordTrace tailWord_1018761 prefixEnd_1018761 464990280049061179202053 := by
  unfold tailWord_1018761
  simp only [CollatzResearch.WordTrace]
  refine ⟨37157266262210362371816137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24771510841473574914544091 37157266262210362371816137)
  ·
    refine ⟨27867949696657771778862103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37157266262210362371816137 27867949696657771778862103)
    ·
      refine ⟨41801924544986657668293155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27867949696657771778862103 41801924544986657668293155)
      ·
        refine ⟨62702886817479986502439733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41801924544986657668293155 62702886817479986502439733)
        ·
          refine ⟨5878395639138748734603725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62702886817479986502439733 5878395639138748734603725)
          ·
            refine ⟨2204398364677030775476397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5878395639138748734603725 2204398364677030775476397)
            ·
              refine ⟨826649386753886540803649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2204398364677030775476397 826649386753886540803649)
              ·
                refine ⟨619987040065414905602737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826649386753886540803649 619987040065414905602737)
                ·
                  refine ⟨464990280049061179202053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619987040065414905602737 464990280049061179202053)
                  ·
                    rfl

theorem cell20_1018761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_1018761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018761 prefixEnd_1018761 := by exact prefixLift 1018761
  have htrace : WordTrace (prefixWord ++ tailWord_1018761) baseStart_1018761 baseEnd_1018761 := by
    simpa [prefixWord, tailWord_1018761, baseEnd_1018761] using wordTrace_append hprefix tailTrace_1018761
  have hstable : (prefixWord ++ tailWord_1018761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018761).length < 2 ^ (prefixWord ++ tailWord_1018761).sum := by decide
  have hdescent : baseEnd_1018761 < baseStart_1018761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018793 : List Nat := [1, 2, 1, 1, 1, 1, 5, 8]
def baseStart_1018793 : Nat := 118140960795 + 1018793 * 2 ^ 59
def prefixEnd_1018793 : Nat := 4983230072969 + 3 ^ 40 * 1018793 * 2
def baseEnd_1018793 : Nat := 155001628573670430045085

theorem tailTrace_1018793 : CollatzResearch.WordTrace tailWord_1018793 prefixEnd_1018793 155001628573670430045085 := by
  unfold tailWord_1018793
  simp only [CollatzResearch.WordTrace]
  refine ⟨37158433398094431836981033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24772288932062954557987355 37158433398094431836981033)
  ·
    refine ⟨27868825048570823877735775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37158433398094431836981033 27868825048570823877735775)
    ·
      refine ⟨41803237572856235816603663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27868825048570823877735775 41803237572856235816603663)
      ·
        refine ⟨62704856359284353724905495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41803237572856235816603663 62704856359284353724905495)
        ·
          refine ⟨94057284538926530587358243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62704856359284353724905495 94057284538926530587358243)
          ·
            refine ⟨141085926808389795881037365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94057284538926530587358243 141085926808389795881037365)
            ·
              refine ⟨13226805638286543363847253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141085926808389795881037365 13226805638286543363847253)
              ·
                refine ⟨155001628573670430045085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13226805638286543363847253 155001628573670430045085)
                ·
                  rfl

theorem cell20_1018793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_1018793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018793 prefixEnd_1018793 := by exact prefixLift 1018793
  have htrace : WordTrace (prefixWord ++ tailWord_1018793) baseStart_1018793 baseEnd_1018793 := by
    simpa [prefixWord, tailWord_1018793, baseEnd_1018793] using wordTrace_append hprefix tailTrace_1018793
  have hstable : (prefixWord ++ tailWord_1018793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018793).length < 2 ^ (prefixWord ++ tailWord_1018793).sum := by decide
  have hdescent : baseEnd_1018793 < baseStart_1018793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018806 : List Nat := [5, 1, 4, 1, 9]
def baseStart_1018806 : Nat := 118140960795 + 1018806 * 2 ^ 59
def prefixEnd_1018806 : Nat := 4983230072969 + 3 ^ 40 * 1018806 * 2
def baseEnd_1018806 : Nat := 5740874312040012625949

theorem tailTrace_1018806 : CollatzResearch.WordTrace tailWord_1018806 prefixEnd_1018806 5740874312040012625949 := by
  unfold tailWord_1018806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322431721690458441075267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24772605031364890038136181 2322431721690458441075267)
  ·
    refine ⟨3483647582535687661612901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2322431721690458441075267 3483647582535687661612901)
    ·
      refine ⟨653183921725441436552419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3483647582535687661612901 653183921725441436552419)
      ·
        refine ⟨979775882588162154828629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653183921725441436552419 979775882588162154828629)
        ·
          refine ⟨5740874312040012625949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 979775882588162154828629 5740874312040012625949)
          ·
            rfl

theorem cell20_1018806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 9].length) (baseStart_1018806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018806 prefixEnd_1018806 := by exact prefixLift 1018806
  have htrace : WordTrace (prefixWord ++ tailWord_1018806) baseStart_1018806 baseEnd_1018806 := by
    simpa [prefixWord, tailWord_1018806, baseEnd_1018806] using wordTrace_append hprefix tailTrace_1018806
  have hstable : (prefixWord ++ tailWord_1018806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018806).length < 2 ^ (prefixWord ++ tailWord_1018806).sum := by decide
  have hdescent : baseEnd_1018806 < baseStart_1018806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018813 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1018813 : Nat := 118140960795 + 1018813 * 2 ^ 59
def prefixEnd_1018813 : Nat := 4983230072969 + 3 ^ 40 * 1018813 * 2
def baseEnd_1018813 : Nat := 465014014265980109468507

theorem tailTrace_1018813 : CollatzResearch.WordTrace tailWord_1018813 prefixEnd_1018813 465014014265980109468507 := by
  unfold tailWord_1018813
  simp only [CollatzResearch.WordTrace]
  refine ⟨37159162858021975252709093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24772775238681316835139395 37159162858021975252709093)
  ·
    refine ⟨6967343035879120359882955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37159162858021975252709093 6967343035879120359882955)
    ·
      refine ⟨10451014553818680539824433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6967343035879120359882955 10451014553818680539824433)
      ·
        refine ⟨7838260915364010404868325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10451014553818680539824433 7838260915364010404868325)
        ·
          refine ⟨1469673921630751950912811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7838260915364010404868325 1469673921630751950912811)
          ·
            refine ⟨2204510882446127926369217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469673921630751950912811 2204510882446127926369217)
            ·
              refine ⟨1653383161834595944776913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2204510882446127926369217 1653383161834595944776913)
              ·
                refine ⟨1240037371375946958582685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653383161834595944776913 1240037371375946958582685)
                ·
                  refine ⟨465014014265980109468507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240037371375946958582685 465014014265980109468507)
                  ·
                    rfl

theorem cell20_1018813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1018813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018813 prefixEnd_1018813 := by exact prefixLift 1018813
  have htrace : WordTrace (prefixWord ++ tailWord_1018813) baseStart_1018813 baseEnd_1018813 := by
    simpa [prefixWord, tailWord_1018813, baseEnd_1018813] using wordTrace_append hprefix tailTrace_1018813
  have hstable : (prefixWord ++ tailWord_1018813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018813).length < 2 ^ (prefixWord ++ tailWord_1018813).sum := by decide
  have hdescent : baseEnd_1018813 < baseStart_1018813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018841 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 4]
def baseStart_1018841 : Nat := 118140960795 + 1018841 * 2 ^ 59
def prefixEnd_1018841 : Nat := 4983230072969 + 3 ^ 40 * 1018841 * 2
def baseEnd_1018841 : Nat := 465026794228936456535059

theorem tailTrace_1018841 : CollatzResearch.WordTrace tailWord_1018841 prefixEnd_1018841 465026794228936456535059 := by
  unfold tailWord_1018841
  simp only [CollatzResearch.WordTrace]
  refine ⟨37160184101920536034728377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24773456067947024023152251 37160184101920536034728377)
  ·
    refine ⟨27870138076440402026046283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37160184101920536034728377 27870138076440402026046283)
    ·
      refine ⟨41805207114660603039069425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27870138076440402026046283 41805207114660603039069425)
      ·
        refine ⟨31353905335995452279302069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41805207114660603039069425 31353905335995452279302069)
        ·
          refine ⟨2939428625249573651184569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31353905335995452279302069 2939428625249573651184569)
          ·
            refine ⟨2204571468937180238388427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2939428625249573651184569 2204571468937180238388427)
            ·
              refine ⟨3306857203405770357582641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204571468937180238388427 3306857203405770357582641)
              ·
                refine ⟨2480142902554327768186981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306857203405770357582641 2480142902554327768186981)
                ·
                  refine ⟨465026794228936456535059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2480142902554327768186981 465026794228936456535059)
                  ·
                    rfl

theorem cell20_1018841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_1018841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018841 prefixEnd_1018841 := by exact prefixLift 1018841
  have htrace : WordTrace (prefixWord ++ tailWord_1018841) baseStart_1018841 baseEnd_1018841 := by
    simpa [prefixWord, tailWord_1018841, baseEnd_1018841] using wordTrace_append hprefix tailTrace_1018841
  have hstable : (prefixWord ++ tailWord_1018841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018841).length < 2 ^ (prefixWord ++ tailWord_1018841).sum := by decide
  have hdescent : baseEnd_1018841 < baseStart_1018841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018858 : List Nat := [3, 1, 3, 1, 2, 2, 1, 5, 2]
def baseStart_1018858 : Nat := 118140960795 + 1018858 * 2 ^ 59
def prefixEnd_1018858 : Nat := 4983230072969 + 3 ^ 40 * 1018858 * 2
def baseEnd_1018858 : Nat := 465034553492159952968323

theorem tailTrace_1018858 : CollatzResearch.WordTrace tailWord_1018858 prefixEnd_1018858 465034553492159952968323 := by
  unfold tailWord_1018858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290201035714736984524307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24773869428572631958731485 9290201035714736984524307)
  ·
    refine ⟨13935301553572105476786461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9290201035714736984524307 13935301553572105476786461)
    ·
      refine ⟨5225738082589539553794923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13935301553572105476786461 5225738082589539553794923)
      ·
        refine ⟨7838607123884309330692385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225738082589539553794923 7838607123884309330692385)
        ·
          refine ⟨5878955342913231998019289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7838607123884309330692385 5878955342913231998019289)
          ·
            refine ⟨4409216507184923998514467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5878955342913231998019289 4409216507184923998514467)
            ·
              refine ⟨6613824760777385997771701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4409216507184923998514467 6613824760777385997771701)
              ·
                refine ⟨620046071322879937291097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6613824760777385997771701 620046071322879937291097)
                ·
                  refine ⟨465034553492159952968323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620046071322879937291097 465034553492159952968323)
                  ·
                    rfl

theorem cell20_1018858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_1018858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018858 prefixEnd_1018858 := by exact prefixLift 1018858
  have htrace : WordTrace (prefixWord ++ tailWord_1018858) baseStart_1018858 baseEnd_1018858 := by
    simpa [prefixWord, tailWord_1018858, baseEnd_1018858] using wordTrace_append hprefix tailTrace_1018858
  have hstable : (prefixWord ++ tailWord_1018858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018858).length < 2 ^ (prefixWord ++ tailWord_1018858).sum := by decide
  have hdescent : baseEnd_1018858 < baseStart_1018858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018903 : List Nat := [1, 1, 3, 5, 1, 1, 4, 4]
def baseStart_1018903 : Nat := 118140960795 + 1018903 * 2 ^ 59
def prefixEnd_1018903 : Nat := 4983230072969 + 3 ^ 40 * 1018903 * 2
def baseEnd_1018903 : Nat := 155018364239446598822713

theorem tailTrace_1018903 : CollatzResearch.WordTrace tailWord_1018903 prefixEnd_1018903 155018364239446598822713 := by
  unfold tailWord_1018903
  simp only [CollatzResearch.WordTrace]
  refine ⟨37162445427695920623485363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24774963618463947082323575 37162445427695920623485363)
  ·
    refine ⟨55743668141543880935228045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37162445427695920623485363 55743668141543880935228045)
    ·
      refine ⟨20903875553078955350710517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55743668141543880935228045 20903875553078955350710517)
      ·
        refine ⟨1959738333101152064129111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20903875553078955350710517 1959738333101152064129111)
        ·
          refine ⟨2939607499651728096193667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959738333101152064129111 2939607499651728096193667)
          ·
            refine ⟨4409411249477592144290501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939607499651728096193667 4409411249477592144290501)
            ·
              refine ⟨826764609277048527054469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4409411249477592144290501 826764609277048527054469)
              ·
                refine ⟨155018364239446598822713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 826764609277048527054469 155018364239446598822713)
                ·
                  rfl

theorem cell20_1018903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 4].length) (baseStart_1018903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018903 prefixEnd_1018903 := by exact prefixLift 1018903
  have htrace : WordTrace (prefixWord ++ tailWord_1018903) baseStart_1018903 baseEnd_1018903 := by
    simpa [prefixWord, tailWord_1018903, baseEnd_1018903] using wordTrace_append hprefix tailTrace_1018903
  have hstable : (prefixWord ++ tailWord_1018903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018903).length < 2 ^ (prefixWord ++ tailWord_1018903).sum := by decide
  have hdescent : baseEnd_1018903 < baseStart_1018903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018913 : List Nat := [1, 2, 3, 2, 3, 3, 1, 3, 2]
def baseStart_1018913 : Nat := 118140960795 + 1018913 * 2 ^ 59
def prefixEnd_1018913 : Nat := 4983230072969 + 3 ^ 40 * 1018913 * 2
def baseEnd_1018913 : Nat := 465059656990824206134765

theorem tailTrace_1018913 : CollatzResearch.WordTrace tailWord_1018913 prefixEnd_1018913 465059656990824206134765 := by
  unfold tailWord_1018913
  simp only [CollatzResearch.WordTrace]
  refine ⟨37162810157659692331349393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24775206771773128220899595 37162810157659692331349393)
  ·
    refine ⟨27872107618244769248512045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37162810157659692331349393 27872107618244769248512045)
    ·
      refine ⟨10452040356841788468192017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27872107618244769248512045 10452040356841788468192017)
      ·
        refine ⟨7839030267631341351144013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10452040356841788468192017 7839030267631341351144013)
        ·
          refine ⟨2939636350361753006679005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7839030267631341351144013 2939636350361753006679005)
          ·
            refine ⟨1102363631385657377504627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2939636350361753006679005 1102363631385657377504627)
            ·
              refine ⟨1653545447078486066256941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102363631385657377504627 1653545447078486066256941)
              ·
                refine ⟨620079542654432274846353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1653545447078486066256941 620079542654432274846353)
                ·
                  refine ⟨465059656990824206134765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620079542654432274846353 465059656990824206134765)
                  ·
                    rfl

theorem cell20_1018913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_1018913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018913 prefixEnd_1018913 := by exact prefixLift 1018913
  have htrace : WordTrace (prefixWord ++ tailWord_1018913) baseStart_1018913 baseEnd_1018913 := by
    simpa [prefixWord, tailWord_1018913, baseEnd_1018913] using wordTrace_append hprefix tailTrace_1018913
  have hstable : (prefixWord ++ tailWord_1018913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018913).length < 2 ^ (prefixWord ++ tailWord_1018913).sum := by decide
  have hdescent : baseEnd_1018913 < baseStart_1018913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018931 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 3]
def baseStart_1018931 : Nat := 118140960795 + 1018931 * 2 ^ 59
def prefixEnd_1018931 : Nat := 4983230072969 + 3 ^ 40 * 1018931 * 2
def baseEnd_1018931 : Nat := 465067872681296143534691

theorem tailTrace_1018931 : CollatzResearch.WordTrace tailWord_1018931 prefixEnd_1018931 465067872681296143534691 := by
  unfold tailWord_1018931
  simp only [CollatzResearch.WordTrace]
  refine ⟨37163466671594481405504647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24775644447729654270336431 37163466671594481405504647)
  ·
    refine ⟨55745200007391722108256971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37163466671594481405504647 55745200007391722108256971)
    ·
      refine ⟨83617800011087583162385457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55745200007391722108256971 83617800011087583162385457)
      ·
        refine ⟨62713350008315687371789093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83617800011087583162385457 62713350008315687371789093)
        ·
          refine ⟨11758753126559191382210455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62713350008315687371789093 11758753126559191382210455)
          ·
            refine ⟨17638129689838787073315683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11758753126559191382210455 17638129689838787073315683)
            ·
              refine ⟨26457194534758180609973525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17638129689838787073315683 26457194534758180609973525)
              ·
                refine ⟨1240180993816789716092509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26457194534758180609973525 1240180993816789716092509)
                ·
                  refine ⟨465067872681296143534691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240180993816789716092509 465067872681296143534691)
                  ·
                    rfl

theorem cell20_1018931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 3].length) (baseStart_1018931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018931 prefixEnd_1018931 := by exact prefixLift 1018931
  have htrace : WordTrace (prefixWord ++ tailWord_1018931) baseStart_1018931 baseEnd_1018931 := by
    simpa [prefixWord, tailWord_1018931, baseEnd_1018931] using wordTrace_append hprefix tailTrace_1018931
  have hstable : (prefixWord ++ tailWord_1018931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018931).length < 2 ^ (prefixWord ++ tailWord_1018931).sum := by decide
  have hdescent : baseEnd_1018931 < baseStart_1018931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018934 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1018934 : Nat := 118140960795 + 1018934 * 2 ^ 59
def prefixEnd_1018934 : Nat := 4983230072969 + 3 ^ 40 * 1018934 * 2
def baseEnd_1018934 : Nat := 465069241963041466434679

theorem tailTrace_1018934 : CollatzResearch.WordTrace tailWord_1018934 prefixEnd_1018934 465069241963041466434679 := by
  unfold tailWord_1018934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322723505661475807366491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24775717393722408611909237 2322723505661475807366491)
  ·
    refine ⟨3484085258492213711049737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2322723505661475807366491 3484085258492213711049737)
    ·
      refine ⟨2613063943869160283287303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3484085258492213711049737 2613063943869160283287303)
      ·
        refine ⟨3919595915803740424930955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613063943869160283287303 3919595915803740424930955)
        ·
          refine ⟨5879393873705610637396433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3919595915803740424930955 5879393873705610637396433)
          ·
            refine ⟨4409545405279207978047325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5879393873705610637396433 4409545405279207978047325)
            ·
              refine ⟨1653579526979702991767747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4409545405279207978047325 1653579526979702991767747)
              ·
                refine ⟨2480369290469554487651621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653579526979702991767747 2480369290469554487651621)
                ·
                  refine ⟨465069241963041466434679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2480369290469554487651621 465069241963041466434679)
                  ·
                    rfl

theorem cell20_1018934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1018934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018934 prefixEnd_1018934 := by exact prefixLift 1018934
  have htrace : WordTrace (prefixWord ++ tailWord_1018934) baseStart_1018934 baseEnd_1018934 := by
    simpa [prefixWord, tailWord_1018934, baseEnd_1018934] using wordTrace_append hprefix tailTrace_1018934
  have hstable : (prefixWord ++ tailWord_1018934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018934).length < 2 ^ (prefixWord ++ tailWord_1018934).sum := by decide
  have hdescent : baseEnd_1018934 < baseStart_1018934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018962 : List Nat := [3, 2, 2, 1, 3, 1, 2, 6]
def baseStart_1018962 : Nat := 118140960795 + 1018962 * 2 ^ 59
def prefixEnd_1018962 : Nat := 4983230072969 + 3 ^ 40 * 1018962 * 2
def baseEnd_1018962 : Nat := 155027340641999271167077

theorem tailTrace_1018962 : CollatzResearch.WordTrace tailWord_1018962 prefixEnd_1018962 155027340641999271167077 := by
  unfold tailWord_1018962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9291149333620543424970785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24776398222988115799922093 9291149333620543424970785)
  ·
    refine ⟨6968362000215407568728089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9291149333620543424970785 6968362000215407568728089)
    ·
      refine ⟨5226271500161555676546067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6968362000215407568728089 5226271500161555676546067)
      ·
        refine ⟨7839407250242333514819101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5226271500161555676546067 7839407250242333514819101)
        ·
          refine ⟨2939777718840875068057163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7839407250242333514819101 2939777718840875068057163)
          ·
            refine ⟨4409666578261312602085745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939777718840875068057163 4409666578261312602085745)
            ·
              refine ⟨3307249933695984451564309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4409666578261312602085745 3307249933695984451564309)
              ·
                refine ⟨155027340641999271167077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3307249933695984451564309 155027340641999271167077)
                ·
                  rfl

theorem cell20_1018962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_1018962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018962 prefixEnd_1018962 := by exact prefixLift 1018962
  have htrace : WordTrace (prefixWord ++ tailWord_1018962) baseStart_1018962 baseEnd_1018962 := by
    simpa [prefixWord, tailWord_1018962, baseEnd_1018962] using wordTrace_append hprefix tailTrace_1018962
  have hstable : (prefixWord ++ tailWord_1018962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018962).length < 2 ^ (prefixWord ++ tailWord_1018962).sum := by decide
  have hdescent : baseEnd_1018962 < baseStart_1018962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018972 : List Nat := [2, 2, 4, 1, 1, 1, 2, 5, 2]
def baseStart_1018972 : Nat := 118140960795 + 1018972 * 2 ^ 59
def prefixEnd_1018972 : Nat := 4983230072969 + 3 ^ 40 * 1018972 * 2
def baseEnd_1018972 : Nat := 465086586198482223167857

theorem tailTrace_1018972 : CollatzResearch.WordTrace tailWord_1018972 prefixEnd_1018972 465086586198482223167857 := by
  unfold tailWord_1018972
  simp only [CollatzResearch.WordTrace]
  refine ⟨18582481032222972703873585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24776641376297296938498113 18582481032222972703873585)
  ·
    refine ⟨13936860774167229527905189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18582481032222972703873585 13936860774167229527905189)
    ·
      refine ⟨2613161395156355536482223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13936860774167229527905189 2613161395156355536482223)
      ·
        refine ⟨3919742092734533304723335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613161395156355536482223 3919742092734533304723335)
        ·
          refine ⟨5879613139101799957085003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3919742092734533304723335 5879613139101799957085003)
          ·
            refine ⟨8819419708652699935627505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879613139101799957085003 8819419708652699935627505)
            ·
              refine ⟨6614564781489524951720629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8819419708652699935627505 6614564781489524951720629)
              ·
                refine ⟨620115448264642964223809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6614564781489524951720629 620115448264642964223809)
                ·
                  refine ⟨465086586198482223167857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620115448264642964223809 465086586198482223167857)
                  ·
                    rfl

theorem cell20_1018972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_1018972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018972 prefixEnd_1018972 := by exact prefixLift 1018972
  have htrace : WordTrace (prefixWord ++ tailWord_1018972) baseStart_1018972 baseEnd_1018972 := by
    simpa [prefixWord, tailWord_1018972, baseEnd_1018972] using wordTrace_append hprefix tailTrace_1018972
  have hstable : (prefixWord ++ tailWord_1018972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018972).length < 2 ^ (prefixWord ++ tailWord_1018972).sum := by decide
  have hdescent : baseEnd_1018972 < baseStart_1018972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018983 : List Nat := [1, 1, 5, 1, 1, 11]
def baseStart_1018983 : Nat := 118140960795 + 1018983 * 2 ^ 59
def prefixEnd_1018983 : Nat := 4983230072969 + 3 ^ 40 * 1018983 * 2
def baseEnd_1018983 : Nat := 17225615070304261992635

theorem tailTrace_1018983 : CollatzResearch.WordTrace tailWord_1018983 prefixEnd_1018983 17225615070304261992635 := by
  unfold tailWord_1018983
  simp only [CollatzResearch.WordTrace]
  refine ⟨37165363267406094286397603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24776908844937396190931735 37165363267406094286397603)
  ·
    refine ⟨55748044901109141429596405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37165363267406094286397603 55748044901109141429596405)
    ·
      refine ⟨5226379209478982009024663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55748044901109141429596405 5226379209478982009024663)
      ·
        refine ⟨7839568814218473013536995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5226379209478982009024663 7839568814218473013536995)
        ·
          refine ⟨11759353221327709520305493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7839568814218473013536995 11759353221327709520305493)
          ·
            refine ⟨17225615070304261992635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11759353221327709520305493 17225615070304261992635)
            ·
              rfl

theorem cell20_1018983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 11].length) (baseStart_1018983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018983 prefixEnd_1018983 := by exact prefixLift 1018983
  have htrace : WordTrace (prefixWord ++ tailWord_1018983) baseStart_1018983 baseEnd_1018983 := by
    simpa [prefixWord, tailWord_1018983, baseEnd_1018983] using wordTrace_append hprefix tailTrace_1018983
  have hstable : (prefixWord ++ tailWord_1018983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018983).length < 2 ^ (prefixWord ++ tailWord_1018983).sum := by decide
  have hdescent : baseEnd_1018983 < baseStart_1018983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018986 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_1018986 : Nat := 118140960795 + 1018986 * 2 ^ 59
def prefixEnd_1018986 : Nat := 4983230072969 + 3 ^ 40 * 1018986 * 2
def baseEnd_1018986 : Nat := 465092976179960396701133

theorem tailTrace_1018986 : CollatzResearch.WordTrace tailWord_1018986 prefixEnd_1018986 465092976179960396701133 := by
  unfold tailWord_1018986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9291368171598806449689203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24776981790930150532504541 9291368171598806449689203)
  ·
    refine ⟨13937052257398209674533805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9291368171598806449689203 13937052257398209674533805)
    ·
      refine ⟨5226394596524328627950177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13937052257398209674533805 5226394596524328627950177)
      ·
        refine ⟨3919795947393246470962633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5226394596524328627950177 3919795947393246470962633)
        ·
          refine ⟨2939846960544934853221975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3919795947393246470962633 2939846960544934853221975)
          ·
            refine ⟨4409770440817402279832963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939846960544934853221975 4409770440817402279832963)
            ·
              refine ⟨6614655661226103419749445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4409770440817402279832963 6614655661226103419749445)
              ·
                refine ⟨1240247936479894391203021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6614655661226103419749445 1240247936479894391203021)
                ·
                  refine ⟨465092976179960396701133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240247936479894391203021 465092976179960396701133)
                  ·
                    rfl

theorem cell20_1018986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_1018986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018986 prefixEnd_1018986 := by exact prefixLift 1018986
  have htrace : WordTrace (prefixWord ++ tailWord_1018986) baseStart_1018986 baseEnd_1018986 := by
    simpa [prefixWord, tailWord_1018986, baseEnd_1018986] using wordTrace_append hprefix tailTrace_1018986
  have hstable : (prefixWord ++ tailWord_1018986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018986).length < 2 ^ (prefixWord ++ tailWord_1018986).sum := by decide
  have hdescent : baseEnd_1018986 < baseStart_1018986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018989 : List Nat := [1, 5, 1, 1, 2, 2, 4, 2, 2]
def baseStart_1018989 : Nat := 118140960795 + 1018989 * 2 ^ 59
def prefixEnd_1018989 : Nat := 4983230072969 + 3 ^ 40 * 1018989 * 2
def baseEnd_1018989 : Nat := 465094345461705719601121

theorem tailTrace_1018989 : CollatzResearch.WordTrace tailWord_1018989 prefixEnd_1018989 465094345461705719601121 := by
  unfold tailWord_1018989
  simp only [CollatzResearch.WordTrace]
  refine ⟨37165582105384357311116021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24777054736922904874077347 37165582105384357311116021)
  ·
    refine ⟨3484273322379783497917127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37165582105384357311116021 3484273322379783497917127)
    ·
      refine ⟨5226409983569675246875691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3484273322379783497917127 5226409983569675246875691)
      ·
        refine ⟨7839614975354512870313537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5226409983569675246875691 7839614975354512870313537)
        ·
          refine ⟨5879711231515884652735153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7839614975354512870313537 5879711231515884652735153)
          ·
            refine ⟨4409783423636913489551365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5879711231515884652735153 4409783423636913489551365)
            ·
              refine ⟨826834391931921279290881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4409783423636913489551365 826834391931921279290881)
              ·
                refine ⟨620125793948940959468161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826834391931921279290881 620125793948940959468161)
                ·
                  refine ⟨465094345461705719601121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620125793948940959468161 465094345461705719601121)
                  ·
                    rfl

theorem cell20_1018989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_1018989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1018989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1018989 prefixEnd_1018989 := by exact prefixLift 1018989
  have htrace : WordTrace (prefixWord ++ tailWord_1018989) baseStart_1018989 baseEnd_1018989 := by
    simpa [prefixWord, tailWord_1018989, baseEnd_1018989] using wordTrace_append hprefix tailTrace_1018989
  have hstable : (prefixWord ++ tailWord_1018989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018989).length < 2 ^ (prefixWord ++ tailWord_1018989).sum := by decide
  have hdescent : baseEnd_1018989 < baseStart_1018989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019006 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_1019006 : Nat := 118140960795 + 1019006 * 2 ^ 59
def prefixEnd_1019006 : Nat := 4983230072969 + 3 ^ 40 * 1019006 * 2
def baseEnd_1019006 : Nat := 465102104724929216034385

theorem tailTrace_1019006 : CollatzResearch.WordTrace tailWord_1019006 prefixEnd_1019006 465102104724929216034385 := by
  unfold tailWord_1019006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4645775268290346151810609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24777468097548512809656581 4645775268290346151810609)
  ·
    refine ⟨3484331451217759613857957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4645775268290346151810609 3484331451217759613857957)
    ·
      refine ⟨653312147103329927598367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3484331451217759613857957 653312147103329927598367)
      ·
        refine ⟨979968220654994891397551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653312147103329927598367 979968220654994891397551)
        ·
          refine ⟨1469952330982492337096327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979968220654994891397551 1469952330982492337096327)
          ·
            refine ⟨2204928496473738505644491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469952330982492337096327 2204928496473738505644491)
            ·
              refine ⟨3307392744710607758466737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204928496473738505644491 3307392744710607758466737)
              ·
                refine ⟨2480544558532955818850053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307392744710607758466737 2480544558532955818850053)
                ·
                  refine ⟨465102104724929216034385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2480544558532955818850053 465102104724929216034385)
                  ·
                    rfl

theorem cell20_1019006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_1019006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019006 prefixEnd_1019006 := by exact prefixLift 1019006
  have htrace : WordTrace (prefixWord ++ tailWord_1019006) baseStart_1019006 baseEnd_1019006 := by
    simpa [prefixWord, tailWord_1019006, baseEnd_1019006] using wordTrace_append hprefix tailTrace_1019006
  have hstable : (prefixWord ++ tailWord_1019006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019006).length < 2 ^ (prefixWord ++ tailWord_1019006).sum := by decide
  have hdescent : baseEnd_1019006 < baseStart_1019006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019045 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1019045 : Nat := 118140960795 + 1019045 * 2 ^ 59
def prefixEnd_1019045 : Nat := 4983230072969 + 3 ^ 40 * 1019045 * 2
def baseEnd_1019045 : Nat := 465119905387618413734225

theorem tailTrace_1019045 : CollatzResearch.WordTrace tailWord_1019045 prefixEnd_1019045 465119905387618413734225 := by
  unfold tailWord_1019045
  simp only [CollatzResearch.WordTrace]
  refine ⟨37167624593181478875154589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24778416395454319250103059 37167624593181478875154589)
  ·
    refine ⟨13937859222443054578182971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37167624593181478875154589 13937859222443054578182971)
    ·
      refine ⟨20906788833664581867274457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13937859222443054578182971 20906788833664581867274457)
      ·
        refine ⟨15680091625248436400455843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20906788833664581867274457 15680091625248436400455843)
        ·
          refine ⟨23520137437872654600683765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15680091625248436400455843 23520137437872654600683765)
          ·
            refine ⟨2205012884800561368814103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23520137437872654600683765 2205012884800561368814103)
            ·
              refine ⟨3307519327200842053221155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205012884800561368814103 3307519327200842053221155)
              ·
                refine ⟨4961278990801263079831733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307519327200842053221155 4961278990801263079831733)
                ·
                  refine ⟨465119905387618413734225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4961278990801263079831733 465119905387618413734225)
                  ·
                    rfl

theorem cell20_1019045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1019045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019045 prefixEnd_1019045 := by exact prefixLift 1019045
  have htrace : WordTrace (prefixWord ++ tailWord_1019045) baseStart_1019045 baseEnd_1019045 := by
    simpa [prefixWord, tailWord_1019045, baseEnd_1019045] using wordTrace_append hprefix tailTrace_1019045
  have hstable : (prefixWord ++ tailWord_1019045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019045).length < 2 ^ (prefixWord ++ tailWord_1019045).sum := by decide
  have hdescent : baseEnd_1019045 < baseStart_1019045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019072 : List Nat := [2, 1, 1, 2, 7, 1, 2, 4]
def baseStart_1019072 : Nat := 118140960795 + 1019072 * 2 ^ 59
def prefixEnd_1019072 : Nat := 4983230072969 + 3 ^ 40 * 1019072 * 2
def baseEnd_1019072 : Nat := 155044076307775439944705

theorem tailTrace_1019072 : CollatzResearch.WordTrace tailWord_1019072 prefixEnd_1019072 155044076307775439944705 := by
  unfold tailWord_1019072
  simp only [CollatzResearch.WordTrace]
  refine ⟨18584304682041831243193735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24779072909389108324258313 18584304682041831243193735)
  ·
    refine ⟨27876457023062746864790603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18584304682041831243193735 27876457023062746864790603)
    ·
      refine ⟨41814685534594120297185905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27876457023062746864790603 41814685534594120297185905)
      ·
        refine ⟨31361014150945590222889429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41814685534594120297185905 31361014150945590222889429)
        ·
          refine ⟨735023769162787270848971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31361014150945590222889429 735023769162787270848971)
          ·
            refine ⟨1102535653744180906273457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735023769162787270848971 1102535653744180906273457)
            ·
              refine ⟨826901740308135679705093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102535653744180906273457 826901740308135679705093)
              ·
                refine ⟨155044076307775439944705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 826901740308135679705093 155044076307775439944705)
                ·
                  rfl

theorem cell20_1019072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_1019072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019072 prefixEnd_1019072 := by exact prefixLift 1019072
  have htrace : WordTrace (prefixWord ++ tailWord_1019072) baseStart_1019072 baseEnd_1019072 := by
    simpa [prefixWord, tailWord_1019072, baseEnd_1019072] using wordTrace_append hprefix tailTrace_1019072
  have hstable : (prefixWord ++ tailWord_1019072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019072).length < 2 ^ (prefixWord ++ tailWord_1019072).sum := by decide
  have hdescent : baseEnd_1019072 < baseStart_1019072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019078 : List Nat := [6, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_1019078 : Nat := 118140960795 + 1019078 * 2 ^ 59
def prefixEnd_1019078 : Nat := 4983230072969 + 3 ^ 40 * 1019078 * 2
def baseEnd_1019078 : Nat := 465134967486816965634091

theorem tailTrace_1019078 : CollatzResearch.WordTrace tailWord_1019078 prefixEnd_1019078 465134967486816965634091 := by
  unfold tailWord_1019078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161525881314435172222059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24779218801374617007403925 1161525881314435172222059)
  ·
    refine ⟨1742288821971652758333089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1161525881314435172222059 1742288821971652758333089)
    ·
      refine ⟨1306716616478739568749817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1742288821971652758333089 1306716616478739568749817)
      ·
        refine ⟨980037462359054676562363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1306716616478739568749817 980037462359054676562363)
        ·
          refine ⟨1470056193538582014843545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980037462359054676562363 1470056193538582014843545)
          ·
            refine ⟨1102542145153936511132659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1470056193538582014843545 1102542145153936511132659)
            ·
              refine ⟨1653813217730904766698989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102542145153936511132659 1653813217730904766698989)
              ·
                refine ⟨620179956649089287512121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1653813217730904766698989 620179956649089287512121)
                ·
                  refine ⟨465134967486816965634091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620179956649089287512121 465134967486816965634091)
                  ·
                    rfl

theorem cell20_1019078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_1019078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019078 prefixEnd_1019078 := by exact prefixLift 1019078
  have htrace : WordTrace (prefixWord ++ tailWord_1019078) baseStart_1019078 baseEnd_1019078 := by
    simpa [prefixWord, tailWord_1019078, baseEnd_1019078] using wordTrace_append hprefix tailTrace_1019078
  have hstable : (prefixWord ++ tailWord_1019078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019078).length < 2 ^ (prefixWord ++ tailWord_1019078).sum := by decide
  have hdescent : baseEnd_1019078 < baseStart_1019078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019114 : List Nat := [3, 1, 3, 1, 1, 4, 2, 5]
def baseStart_1019114 : Nat := 118140960795 + 1019114 * 2 ^ 59
def prefixEnd_1019114 : Nat := 4983230072969 + 3 ^ 40 * 1019114 * 2
def baseEnd_1019114 : Nat := 155050466289253613477981

theorem tailTrace_1019114 : CollatzResearch.WordTrace tailWord_1019114 prefixEnd_1019114 155050466289253613477981 := by
  unfold tailWord_1019114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292535307482875914854099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24780094153287669106277597 9292535307482875914854099)
  ·
    refine ⟨13938802961224313872281149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9292535307482875914854099 13938802961224313872281149)
    ·
      refine ⟨5227051110459117702105431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13938802961224313872281149 5227051110459117702105431)
      ·
        refine ⟨7840576665688676553158147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227051110459117702105431 7840576665688676553158147)
        ·
          refine ⟨11760864998533014829737221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840576665688676553158147 11760864998533014829737221)
          ·
            refine ⟨2205162187224940280575729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11760864998533014829737221 2205162187224940280575729)
            ·
              refine ⟨1653871640418705210431797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205162187224940280575729 1653871640418705210431797)
              ·
                refine ⟨155050466289253613477981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1653871640418705210431797 155050466289253613477981)
                ·
                  rfl

theorem cell20_1019114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_1019114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019114 prefixEnd_1019114 := by exact prefixLift 1019114
  have htrace : WordTrace (prefixWord ++ tailWord_1019114) baseStart_1019114 baseEnd_1019114 := by
    simpa [prefixWord, tailWord_1019114, baseEnd_1019114] using wordTrace_append hprefix tailTrace_1019114
  have hstable : (prefixWord ++ tailWord_1019114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019114).length < 2 ^ (prefixWord ++ tailWord_1019114).sum := by decide
  have hdescent : baseEnd_1019114 < baseStart_1019114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019117 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1019117 : Nat := 118140960795 + 1019117 * 2 ^ 59
def prefixEnd_1019117 : Nat := 4983230072969 + 3 ^ 40 * 1019117 * 2
def baseEnd_1019117 : Nat := 465152768149506163333931

theorem tailTrace_1019117 : CollatzResearch.WordTrace tailWord_1019117 prefixEnd_1019117 465152768149506163333931 := by
  unfold tailWord_1019117
  simp only [CollatzResearch.WordTrace]
  refine ⟨37170250648920635171775605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24780167099280423447850403 37170250648920635171775605)
  ·
    refine ⟨3484710998336309547353963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37170250648920635171775605 3484710998336309547353963)
    ·
      refine ⟨5227066497504464321030945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3484710998336309547353963 5227066497504464321030945)
      ·
        refine ⟨3920299873128348240773209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5227066497504464321030945 3920299873128348240773209)
        ·
          refine ⟨2940224904846261180579907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3920299873128348240773209 2940224904846261180579907)
          ·
            refine ⟨4410337357269391770869861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940224904846261180579907 4410337357269391770869861)
            ·
              refine ⟨826938254488010957038099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4410337357269391770869861 826938254488010957038099)
              ·
                refine ⟨1240407381732016435557149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826938254488010957038099 1240407381732016435557149)
                ·
                  refine ⟨465152768149506163333931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240407381732016435557149 465152768149506163333931)
                  ·
                    rfl

theorem cell20_1019117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1019117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019117 prefixEnd_1019117 := by exact prefixLift 1019117
  have htrace : WordTrace (prefixWord ++ tailWord_1019117) baseStart_1019117 baseEnd_1019117 := by
    simpa [prefixWord, tailWord_1019117, baseEnd_1019117] using wordTrace_append hprefix tailTrace_1019117
  have hstable : (prefixWord ++ tailWord_1019117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019117).length < 2 ^ (prefixWord ++ tailWord_1019117).sum := by decide
  have hdescent : baseEnd_1019117 < baseStart_1019117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019135 : List Nat := [1, 1, 2, 2, 1, 5, 2, 6]
def baseStart_1019135 : Nat := 118140960795 + 1019135 * 2 ^ 59
def prefixEnd_1019135 : Nat := 4983230072969 + 3 ^ 40 * 1019135 * 2
def baseEnd_1019135 : Nat := 155053661279992700244619

theorem tailTrace_1019135 : CollatzResearch.WordTrace tailWord_1019135 prefixEnd_1019135 155053661279992700244619 := by
  unfold tailWord_1019135
  simp only [CollatzResearch.WordTrace]
  refine ⟨37170907162855424245930859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24780604775236949497287239 37170907162855424245930859)
  ·
    refine ⟨55756360744283136368896289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37170907162855424245930859 55756360744283136368896289)
    ·
      refine ⟨41817270558212352276672217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55756360744283136368896289 41817270558212352276672217)
      ·
        refine ⟨31362952918659264207504163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41817270558212352276672217 31362952918659264207504163)
        ·
          refine ⟨47044429377988896311256245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31362952918659264207504163 47044429377988896311256245)
          ·
            refine ⟨4410415254186459029180273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47044429377988896311256245 4410415254186459029180273)
            ·
              refine ⟨3307811440639844271885205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410415254186459029180273 3307811440639844271885205)
              ·
                refine ⟨155053661279992700244619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3307811440639844271885205 155053661279992700244619)
                ·
                  rfl

theorem cell20_1019135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_1019135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019135 prefixEnd_1019135 := by exact prefixLift 1019135
  have htrace : WordTrace (prefixWord ++ tailWord_1019135) baseStart_1019135 baseEnd_1019135 := by
    simpa [prefixWord, tailWord_1019135, baseEnd_1019135] using wordTrace_append hprefix tailTrace_1019135
  have hstable : (prefixWord ++ tailWord_1019135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019135).length < 2 ^ (prefixWord ++ tailWord_1019135).sum := by decide
  have hdescent : baseEnd_1019135 < baseStart_1019135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019145 : List Nat := [1, 2, 1, 1, 3, 3, 2, 5, 2]
def baseStart_1019145 : Nat := 118140960795 + 1019145 * 2 ^ 59
def prefixEnd_1019145 : Nat := 4983230072969 + 3 ^ 40 * 1019145 * 2
def baseEnd_1019145 : Nat := 465165548112462510400483

theorem tailTrace_1019145 : CollatzResearch.WordTrace tailWord_1019145 prefixEnd_1019145 465165548112462510400483 := by
  unfold tailWord_1019145
  simp only [CollatzResearch.WordTrace]
  refine ⟨37171271892819195953794889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24780847928546130635863259 37171271892819195953794889)
  ·
    refine ⟨27878453919614396965346167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37171271892819195953794889 27878453919614396965346167)
    ·
      refine ⟨41817680879421595448019251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27878453919614396965346167 41817680879421595448019251)
      ·
        refine ⟨62726521319132393172028877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41817680879421595448019251 62726521319132393172028877)
        ·
          refine ⟨23522445494674647439510829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62726521319132393172028877 23522445494674647439510829)
          ·
            refine ⟨8820917060502992789816561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23522445494674647439510829 8820917060502992789816561)
            ·
              refine ⟨6615687795377244592362421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8820917060502992789816561 6615687795377244592362421)
              ·
                refine ⟨620220730816616680533977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6615687795377244592362421 620220730816616680533977)
                ·
                  refine ⟨465165548112462510400483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620220730816616680533977 465165548112462510400483)
                  ·
                    rfl

theorem cell20_1019145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_1019145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019145 prefixEnd_1019145 := by exact prefixLift 1019145
  have htrace : WordTrace (prefixWord ++ tailWord_1019145) baseStart_1019145 baseEnd_1019145 := by
    simpa [prefixWord, tailWord_1019145, baseEnd_1019145] using wordTrace_append hprefix tailTrace_1019145
  have hstable : (prefixWord ++ tailWord_1019145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019145).length < 2 ^ (prefixWord ++ tailWord_1019145).sum := by decide
  have hdescent : baseEnd_1019145 < baseStart_1019145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019154 : List Nat := [3, 2, 4, 2, 2, 1, 2, 2, 2]
def baseStart_1019154 : Nat := 118140960795 + 1019154 * 2 ^ 59
def prefixEnd_1019154 : Nat := 4983230072969 + 3 ^ 40 * 1019154 * 2
def baseEnd_1019154 : Nat := 465169655957698479100447

theorem tailTrace_1019154 : CollatzResearch.WordTrace tailWord_1019154 prefixEnd_1019154 465169655957698479100447 := by
  unfold tailWord_1019154
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292900037446647622718129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24781066766524393660581677 9292900037446647622718129)
  ·
    refine ⟨6969675028084985717038597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9292900037446647622718129 6969675028084985717038597)
    ·
      refine ⟨1306814067765934821944737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6969675028084985717038597 1306814067765934821944737)
      ·
        refine ⟨980110550824451116458553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1306814067765934821944737 980110550824451116458553)
        ·
          refine ⟨735082913118338337343915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980110550824451116458553 735082913118338337343915)
          ·
            refine ⟨1102624369677507506015873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735082913118338337343915 1102624369677507506015873)
            ·
              refine ⟨826968277258130629511905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102624369677507506015873 826968277258130629511905)
              ·
                refine ⟨620226207943597972133929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826968277258130629511905 620226207943597972133929)
                ·
                  refine ⟨465169655957698479100447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620226207943597972133929 465169655957698479100447)
                  ·
                    rfl

theorem cell20_1019154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_1019154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019154 prefixEnd_1019154 := by exact prefixLift 1019154
  have htrace : WordTrace (prefixWord ++ tailWord_1019154) baseStart_1019154 baseEnd_1019154 := by
    simpa [prefixWord, tailWord_1019154, baseEnd_1019154] using wordTrace_append hprefix tailTrace_1019154
  have hstable : (prefixWord ++ tailWord_1019154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019154).length < 2 ^ (prefixWord ++ tailWord_1019154).sum := by decide
  have hdescent : baseEnd_1019154 < baseStart_1019154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019162 : List Nat := [3, 1, 1, 3, 3, 2, 1, 4, 2]
def baseStart_1019162 : Nat := 118140960795 + 1019162 * 2 ^ 59
def prefixEnd_1019162 : Nat := 4983230072969 + 3 ^ 40 * 1019162 * 2
def baseEnd_1019162 : Nat := 465173307375686006833747

theorem tailTrace_1019162 : CollatzResearch.WordTrace tailWord_1019162 prefixEnd_1019162 465173307375686006833747 := by
  unfold tailWord_1019162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292972983439401964290935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24781261289171738571442493 9292972983439401964290935)
  ·
    refine ⟨13939459475159102946436403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9292972983439401964290935 13939459475159102946436403)
    ·
      refine ⟨20909189212738654419654605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13939459475159102946436403 20909189212738654419654605)
      ·
        refine ⟨7840945954776995407370477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20909189212738654419654605 7840945954776995407370477)
        ·
          refine ⟨2940354733041373277763929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7840945954776995407370477 2940354733041373277763929)
          ·
            refine ⟨2205266049781029958322947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2940354733041373277763929 2205266049781029958322947)
            ·
              refine ⟨3307899074671544937484421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205266049781029958322947 3307899074671544937484421)
              ·
                refine ⟨620231076500914675778329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3307899074671544937484421 620231076500914675778329)
                ·
                  refine ⟨465173307375686006833747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620231076500914675778329 465173307375686006833747)
                  ·
                    rfl

theorem cell20_1019162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_1019162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019162 prefixEnd_1019162 := by exact prefixLift 1019162
  have htrace : WordTrace (prefixWord ++ tailWord_1019162) baseStart_1019162 baseEnd_1019162 := by
    simpa [prefixWord, tailWord_1019162, baseEnd_1019162] using wordTrace_append hprefix tailTrace_1019162
  have hstable : (prefixWord ++ tailWord_1019162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019162).length < 2 ^ (prefixWord ++ tailWord_1019162).sum := by decide
  have hdescent : baseEnd_1019162 < baseStart_1019162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019176 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 3]
def baseStart_1019176 : Nat := 118140960795 + 1019176 * 2 ^ 59
def prefixEnd_1019176 : Nat := 4983230072969 + 3 ^ 40 * 1019176 * 2
def baseEnd_1019176 : Nat := 465179697357164180367023

theorem tailTrace_1019176 : CollatzResearch.WordTrace tailWord_1019176 prefixEnd_1019176 465179697357164180367023 := by
  unfold tailWord_1019176
  simp only [CollatzResearch.WordTrace]
  refine ⟨18586201277853444124086691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24781601703804592165448921 18586201277853444124086691)
  ·
    refine ⟨27879301916780166186130037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18586201277853444124086691 27879301916780166186130037)
    ·
      refine ⟨2613684554698140579949691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27879301916780166186130037 2613684554698140579949691)
      ·
        refine ⟨3920526832047210869924537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613684554698140579949691 3920526832047210869924537)
        ·
          refine ⟨2940395124035408152443403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3920526832047210869924537 2940395124035408152443403)
          ·
            refine ⟨4410592686053112228665105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940395124035408152443403 4410592686053112228665105)
            ·
              refine ⟨3307944514539834171498829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410592686053112228665105 3307944514539834171498829)
              ·
                refine ⟨1240479192952437814312061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3307944514539834171498829 1240479192952437814312061)
                ·
                  refine ⟨465179697357164180367023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240479192952437814312061 465179697357164180367023)
                  ·
                    rfl

theorem cell20_1019176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_1019176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019176 prefixEnd_1019176 := by exact prefixLift 1019176
  have htrace : WordTrace (prefixWord ++ tailWord_1019176) baseStart_1019176 baseEnd_1019176 := by
    simpa [prefixWord, tailWord_1019176, baseEnd_1019176] using wordTrace_append hprefix tailTrace_1019176
  have hstable : (prefixWord ++ tailWord_1019176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019176).length < 2 ^ (prefixWord ++ tailWord_1019176).sum := by decide
  have hdescent : baseEnd_1019176 < baseStart_1019176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019180 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1019180 : Nat := 118140960795 + 1019180 * 2 ^ 59
def prefixEnd_1019180 : Nat := 4983230072969 + 3 ^ 40 * 1019180 * 2
def baseEnd_1019180 : Nat := 465181523066157944233673

theorem tailTrace_1019180 : CollatzResearch.WordTrace tailWord_1019180 prefixEnd_1019180 465181523066157944233673 := by
  unfold tailWord_1019180
  simp only [CollatzResearch.WordTrace]
  refine ⟨18586274223846198465659497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24781698965128264620879329 18586274223846198465659497)
  ·
    refine ⟨13939705667884648849244623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18586274223846198465659497 13939705667884648849244623)
    ·
      refine ⟨20909558501826973273866935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13939705667884648849244623 20909558501826973273866935)
      ·
        refine ⟨31364337752740459910800403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20909558501826973273866935 31364337752740459910800403)
        ·
          refine ⟨47046506629110689866200605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31364337752740459910800403 47046506629110689866200605)
          ·
            refine ⟨17642439985916508699825227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47046506629110689866200605 17642439985916508699825227)
            ·
              refine ⟨26463659978874763049737841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17642439985916508699825227 26463659978874763049737841)
              ·
                refine ⟨19847744984156072287303381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26463659978874763049737841 19847744984156072287303381)
                ·
                  refine ⟨465181523066157944233673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19847744984156072287303381 465181523066157944233673)
                  ·
                    rfl

theorem cell20_1019180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1019180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019180 prefixEnd_1019180 := by exact prefixLift 1019180
  have htrace : WordTrace (prefixWord ++ tailWord_1019180) baseStart_1019180 baseEnd_1019180 := by
    simpa [prefixWord, tailWord_1019180, baseEnd_1019180] using wordTrace_append hprefix tailTrace_1019180
  have hstable : (prefixWord ++ tailWord_1019180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019180).length < 2 ^ (prefixWord ++ tailWord_1019180).sum := by decide
  have hdescent : baseEnd_1019180 < baseStart_1019180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019206 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1019206 : Nat := 118140960795 + 1019206 * 2 ^ 59
def prefixEnd_1019206 : Nat := 4983230072969 + 3 ^ 40 * 1019206 * 2
def baseEnd_1019206 : Nat := 465193390174617409366901

theorem tailTrace_1019206 : CollatzResearch.WordTrace tailWord_1019206 prefixEnd_1019206 465193390174617409366901 := by
  unfold tailWord_1019206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161671773299943855367671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24782331163732135581176981 1161671773299943855367671)
  ·
    refine ⟨1742507659949915783051507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1161671773299943855367671 1742507659949915783051507)
    ·
      refine ⟨2613761489924873674577261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1742507659949915783051507 2613761489924873674577261)
      ·
        refine ⟨980160558721827627966473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2613761489924873674577261 980160558721827627966473)
        ·
          refine ⟨735120419041370720974855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980160558721827627966473 735120419041370720974855)
          ·
            refine ⟨1102680628562056081462283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735120419041370720974855 1102680628562056081462283)
            ·
              refine ⟨1654020942843084122193425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102680628562056081462283 1654020942843084122193425)
              ·
                refine ⟨1240515707132313091645069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654020942843084122193425 1240515707132313091645069)
                ·
                  refine ⟨465193390174617409366901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240515707132313091645069 465193390174617409366901)
                  ·
                    rfl

theorem cell20_1019206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1019206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019206 prefixEnd_1019206 := by exact prefixLift 1019206
  have htrace : WordTrace (prefixWord ++ tailWord_1019206) baseStart_1019206 baseEnd_1019206 := by
    simpa [prefixWord, tailWord_1019206, baseEnd_1019206] using wordTrace_append hprefix tailTrace_1019206
  have hstable : (prefixWord ++ tailWord_1019206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019206).length < 2 ^ (prefixWord ++ tailWord_1019206).sum := by decide
  have hdescent : baseEnd_1019206 < baseStart_1019206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019221 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 4]
def baseStart_1019221 : Nat := 118140960795 + 1019221 * 2 ^ 59
def prefixEnd_1019221 : Nat := 4983230072969 + 3 ^ 40 * 1019221 * 2
def baseEnd_1019221 : Nat := 465200236583344023866839

theorem tailTrace_1019221 : CollatzResearch.WordTrace tailWord_1019221 prefixEnd_1019221 465200236583344023866839 := by
  unfold tailWord_1019221
  simp only [CollatzResearch.WordTrace]
  refine ⟨37174043840543860933561517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24782695893695907289041011 37174043840543860933561517)
  ·
    refine ⟨13940266440203947850085569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37174043840543860933561517 13940266440203947850085569)
    ·
      refine ⟨10455199830152960887564177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13940266440203947850085569 10455199830152960887564177)
      ·
        refine ⟨7841399872614720665673133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10455199830152960887564177 7841399872614720665673133)
        ·
          refine ⟨2940524952230520249627425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7841399872614720665673133 2940524952230520249627425)
          ·
            refine ⟨2205393714172890187220569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2940524952230520249627425 2205393714172890187220569)
            ·
              refine ⟨1654045285629667640415427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205393714172890187220569 1654045285629667640415427)
              ·
                refine ⟨2481067928444501460623141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654045285629667640415427 2481067928444501460623141)
                ·
                  refine ⟨465200236583344023866839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2481067928444501460623141 465200236583344023866839)
                  ·
                    rfl

theorem cell20_1019221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_1019221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019221 prefixEnd_1019221 := by exact prefixLift 1019221
  have htrace : WordTrace (prefixWord ++ tailWord_1019221) baseStart_1019221 baseEnd_1019221 := by
    simpa [prefixWord, tailWord_1019221, baseEnd_1019221] using wordTrace_append hprefix tailTrace_1019221
  have hstable : (prefixWord ++ tailWord_1019221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019221).length < 2 ^ (prefixWord ++ tailWord_1019221).sum := by decide
  have hdescent : baseEnd_1019221 < baseStart_1019221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019245 : List Nat := [1, 5, 1, 1, 1, 5, 2, 4]
def baseStart_1019245 : Nat := 118140960795 + 1019245 * 2 ^ 59
def prefixEnd_1019245 : Nat := 4983230072969 + 3 ^ 40 * 1019245 * 2
def baseEnd_1019245 : Nat := 155070396945768869022247

theorem tailTrace_1019245 : CollatzResearch.WordTrace tailWord_1019245 prefixEnd_1019245 155070396945768869022247 := by
  unfold tailWord_1019245
  simp only [CollatzResearch.WordTrace]
  refine ⟨37174919192456913032435189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24783279461637942021623459 37174919192456913032435189)
  ·
    refine ⟨3485148674292835596790799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37174919192456913032435189 3485148674292835596790799)
    ·
      refine ⟨5227723011439253395186199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3485148674292835596790799 5227723011439253395186199)
      ·
        refine ⟨7841584517158880092779299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227723011439253395186199 7841584517158880092779299)
        ·
          refine ⟨11762376775738320139168949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7841584517158880092779299 11762376775738320139168949)
          ·
            refine ⟨1102722822725467513047089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11762376775738320139168949 1102722822725467513047089)
            ·
              refine ⟨827042117044100634785317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102722822725467513047089 827042117044100634785317)
              ·
                refine ⟨155070396945768869022247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 827042117044100634785317 155070396945768869022247)
                ·
                  rfl

theorem cell20_1019245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 4].length) (baseStart_1019245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019245 prefixEnd_1019245 := by exact prefixLift 1019245
  have htrace : WordTrace (prefixWord ++ tailWord_1019245) baseStart_1019245 baseEnd_1019245 := by
    simpa [prefixWord, tailWord_1019245, baseEnd_1019245] using wordTrace_append hprefix tailTrace_1019245
  have hstable : (prefixWord ++ tailWord_1019245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019245).length < 2 ^ (prefixWord ++ tailWord_1019245).sum := by decide
  have hdescent : baseEnd_1019245 < baseStart_1019245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019262 : List Nat := [4, 2, 3, 2, 1, 2, 6]
def baseStart_1019262 : Nat := 118140960795 + 1019262 * 2 ^ 59
def prefixEnd_1019262 : Nat := 4983230072969 + 3 ^ 40 * 1019262 * 2
def baseEnd_1019262 : Nat := 51690994455614455944445

theorem tailTrace_1019262 : CollatzResearch.WordTrace tailWord_1019262 prefixEnd_1019262 51690994455614455944445 := by
  unfold tailWord_1019262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4646942404174415616975505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24783692822263549957202693 4646942404174415616975505)
  ·
    refine ⟨3485206803130811712731629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4646942404174415616975505 3485206803130811712731629)
    ·
      refine ⟨1306952551174054392274361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3485206803130811712731629 1306952551174054392274361)
      ·
        refine ⟨980214413380540794205771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1306952551174054392274361 980214413380540794205771)
        ·
          refine ⟨1470321620070811191308657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980214413380540794205771 1470321620070811191308657)
          ·
            refine ⟨1102741215053108393481493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1470321620070811191308657 1102741215053108393481493)
            ·
              refine ⟨51690994455614455944445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1102741215053108393481493 51690994455614455944445)
              ·
                rfl

theorem cell20_1019262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 6].length) (baseStart_1019262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019262 prefixEnd_1019262 := by exact prefixLift 1019262
  have htrace : WordTrace (prefixWord ++ tailWord_1019262) baseStart_1019262 baseEnd_1019262 := by
    simpa [prefixWord, tailWord_1019262, baseEnd_1019262] using wordTrace_append hprefix tailTrace_1019262
  have hstable : (prefixWord ++ tailWord_1019262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019262).length < 2 ^ (prefixWord ++ tailWord_1019262).sum := by decide
  have hdescent : baseEnd_1019262 < baseStart_1019262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019276 : List Nat := [2, 2, 1, 2, 1, 3, 5, 2, 2]
def baseStart_1019276 : Nat := 118140960795 + 1019276 * 2 ^ 59
def prefixEnd_1019276 : Nat := 4983230072969 + 3 ^ 40 * 1019276 * 2
def baseEnd_1019276 : Nat := 465225340082008277033281

theorem tailTrace_1019276 : CollatzResearch.WordTrace tailWord_1019276 prefixEnd_1019276 465225340082008277033281 := by
  unfold tailWord_1019276
  simp only [CollatzResearch.WordTrace]
  refine ⟨18588024927672302663406841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24784033236896403551209121 18588024927672302663406841)
  ·
    refine ⟨13941018695754226997555131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18588024927672302663406841 13941018695754226997555131)
    ·
      refine ⟨20911528043631340496332697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13941018695754226997555131 20911528043631340496332697)
      ·
        refine ⟨15683646032723505372249523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20911528043631340496332697 15683646032723505372249523)
        ·
          refine ⟨23525469049085258058374285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15683646032723505372249523 23525469049085258058374285)
          ·
            refine ⟨8822050893406971771890357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23525469049085258058374285 8822050893406971771890357)
            ·
              refine ⟨827067271256903603614721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8822050893406971771890357 827067271256903603614721)
              ·
                refine ⟨620300453442677702711041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827067271256903603614721 620300453442677702711041)
                ·
                  refine ⟨465225340082008277033281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620300453442677702711041 465225340082008277033281)
                  ·
                    rfl

theorem cell20_1019276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_1019276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019276 prefixEnd_1019276 := by exact prefixLift 1019276
  have htrace : WordTrace (prefixWord ++ tailWord_1019276) baseStart_1019276 baseEnd_1019276 := by
    simpa [prefixWord, tailWord_1019276, baseEnd_1019276] using wordTrace_append hprefix tailTrace_1019276
  have hstable : (prefixWord ++ tailWord_1019276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019276).length < 2 ^ (prefixWord ++ tailWord_1019276).sum := by decide
  have hdescent : baseEnd_1019276 < baseStart_1019276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019335 : List Nat := [1, 1, 4, 1, 1, 3, 3, 4, 2]
def baseStart_1019335 : Nat := 118140960795 + 1019335 * 2 ^ 59
def prefixEnd_1019335 : Nat := 4983230072969 + 3 ^ 40 * 1019335 * 2
def baseEnd_1019335 : Nat := 465252269289666294066373

theorem tailTrace_1019335 : CollatzResearch.WordTrace tailWord_1019335 prefixEnd_1019335 465252269289666294066373 := by
  unfold tailWord_1019335
  simp only [CollatzResearch.WordTrace]
  refine ⟨37178201762130858403211459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24785467841420572268807639 37178201762130858403211459)
  ·
    refine ⟨55767302643196287604817189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37178201762130858403211459 55767302643196287604817189)
    ·
      refine ⟨10456369245599303925903223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55767302643196287604817189 10456369245599303925903223)
      ·
        refine ⟨15684553868398955888854835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10456369245599303925903223 15684553868398955888854835)
        ·
          refine ⟨23526830802598433833282253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15684553868398955888854835 23526830802598433833282253)
          ·
            refine ⟨8822561550974412687480845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23526830802598433833282253 8822561550974412687480845)
            ·
              refine ⟨3308460581615404757805317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8822561550974412687480845 3308460581615404757805317)
              ·
                refine ⟨620336359052888392088497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3308460581615404757805317 620336359052888392088497)
                ·
                  refine ⟨465252269289666294066373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620336359052888392088497 465252269289666294066373)
                  ·
                    rfl

theorem cell20_1019335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 2].length) (baseStart_1019335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019335 prefixEnd_1019335 := by exact prefixLift 1019335
  have htrace : WordTrace (prefixWord ++ tailWord_1019335) baseStart_1019335 baseEnd_1019335 := by
    simpa [prefixWord, tailWord_1019335, baseEnd_1019335] using wordTrace_append hprefix tailTrace_1019335
  have hstable : (prefixWord ++ tailWord_1019335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019335).length < 2 ^ (prefixWord ++ tailWord_1019335).sum := by decide
  have hdescent : baseEnd_1019335 < baseStart_1019335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019349 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 3]
def baseStart_1019349 : Nat := 118140960795 + 1019349 * 2 ^ 59
def prefixEnd_1019349 : Nat := 4983230072969 + 3 ^ 40 * 1019349 * 2
def baseEnd_1019349 : Nat := 465258659271144467599649

theorem tailTrace_1019349 : CollatzResearch.WordTrace tailWord_1019349 prefixEnd_1019349 465258659271144467599649 := by
  unfold tailWord_1019349
  simp only [CollatzResearch.WordTrace]
  refine ⟨37178712384080138794221101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24785808256053425862814067 37178712384080138794221101)
  ·
    refine ⟨13942017144030052047832913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37178712384080138794221101 13942017144030052047832913)
    ·
      refine ⟨10456512858022539035874685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13942017144030052047832913 10456512858022539035874685)
      ·
        refine ⟨3921192321758452138453007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10456512858022539035874685 3921192321758452138453007)
        ·
          refine ⟨5881788482637678207679511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921192321758452138453007 5881788482637678207679511)
          ·
            refine ⟨8822682723956517311519267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881788482637678207679511 8822682723956517311519267)
            ·
              refine ⟨13234024085934775967278901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822682723956517311519267 13234024085934775967278901)
              ·
                refine ⟨1240689758056385246932397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13234024085934775967278901 1240689758056385246932397)
                ·
                  refine ⟨465258659271144467599649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240689758056385246932397 465258659271144467599649)
                  ·
                    rfl

theorem cell20_1019349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_1019349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019349 prefixEnd_1019349 := by exact prefixLift 1019349
  have htrace : WordTrace (prefixWord ++ tailWord_1019349) baseStart_1019349 baseEnd_1019349 := by
    simpa [prefixWord, tailWord_1019349, baseEnd_1019349] using wordTrace_append hprefix tailTrace_1019349
  have hstable : (prefixWord ++ tailWord_1019349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019349).length < 2 ^ (prefixWord ++ tailWord_1019349).sum := by decide
  have hdescent : baseEnd_1019349 < baseStart_1019349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019449 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 4]
def baseStart_1019449 : Nat := 118140960795 + 1019449 * 2 ^ 59
def prefixEnd_1019449 : Nat := 4983230072969 + 3 ^ 40 * 1019449 * 2
def baseEnd_1019449 : Nat := 465304301995988564265907

theorem tailTrace_1019449 : CollatzResearch.WordTrace tailWord_1019449 prefixEnd_1019449 465304301995988564265907 := by
  unfold tailWord_1019449
  simp only [CollatzResearch.WordTrace]
  refine ⟨37182359683717855872861401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24788239789145237248574267 37182359683717855872861401)
  ·
    refine ⟨27886769762788391904646051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37182359683717855872861401 27886769762788391904646051)
    ·
      refine ⟨41830154644182587856969077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27886769762788391904646051 41830154644182587856969077)
      ·
        refine ⟨3921576997892117611590851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41830154644182587856969077 3921576997892117611590851)
        ·
          refine ⟨5882365496838176417386277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921576997892117611590851 5882365496838176417386277)
          ·
            refine ⟨1102943530657158078259927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5882365496838176417386277 1102943530657158078259927)
            ·
              refine ⟨1654415295985737117389891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102943530657158078259927 1654415295985737117389891)
              ·
                refine ⟨2481622943978605676084837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654415295985737117389891 2481622943978605676084837)
                ·
                  refine ⟨465304301995988564265907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2481622943978605676084837 465304301995988564265907)
                  ·
                    rfl

theorem cell20_1019449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_1019449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019449 prefixEnd_1019449 := by exact prefixLift 1019449
  have htrace : WordTrace (prefixWord ++ tailWord_1019449) baseStart_1019449 baseEnd_1019449 := by
    simpa [prefixWord, tailWord_1019449, baseEnd_1019449] using wordTrace_append hprefix tailTrace_1019449
  have hstable : (prefixWord ++ tailWord_1019449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019449).length < 2 ^ (prefixWord ++ tailWord_1019449).sum := by decide
  have hdescent : baseEnd_1019449 < baseStart_1019449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019504 : List Nat := [2, 1, 1, 1, 6, 1, 4, 2, 2]
def baseStart_1019504 : Nat := 118140960795 + 1019504 * 2 ^ 59
def prefixEnd_1019504 : Nat := 4983230072969 + 3 ^ 40 * 1019504 * 2
def baseEnd_1019504 : Nat := 465329405494652817432349

theorem tailTrace_1019504 : CollatzResearch.WordTrace tailWord_1019504 prefixEnd_1019504 465329405494652817432349 := by
  unfold tailWord_1019504
  simp only [CollatzResearch.WordTrace]
  refine ⟨18592182849259300133056783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24789577132345733510742377 18592182849259300133056783)
  ·
    refine ⟨27888274273888950199585175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18592182849259300133056783 27888274273888950199585175)
    ·
      refine ⟨41832411410833425299377763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27888274273888950199585175 41832411410833425299377763)
      ·
        refine ⟨62748617116250137949066645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41832411410833425299377763 62748617116250137949066645)
        ·
          refine ⟨2941341427324225216362499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62748617116250137949066645 2941341427324225216362499)
          ·
            refine ⟨4412012140986337824543749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2941341427324225216362499 4412012140986337824543749)
            ·
              refine ⟨827252276434938342101953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4412012140986337824543749 827252276434938342101953)
              ·
                refine ⟨620439207326203756576465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827252276434938342101953 620439207326203756576465)
                ·
                  refine ⟨465329405494652817432349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620439207326203756576465 465329405494652817432349)
                  ·
                    rfl

theorem cell20_1019504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_1019504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019504 prefixEnd_1019504 := by exact prefixLift 1019504
  have htrace : WordTrace (prefixWord ++ tailWord_1019504) baseStart_1019504 baseEnd_1019504 := by
    simpa [prefixWord, tailWord_1019504, baseEnd_1019504] using wordTrace_append hprefix tailTrace_1019504
  have hstable : (prefixWord ++ tailWord_1019504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019504).length < 2 ^ (prefixWord ++ tailWord_1019504).sum := by decide
  have hdescent : baseEnd_1019504 < baseStart_1019504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019529 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_1019529 : Nat := 118140960795 + 1019529 * 2 ^ 59
def prefixEnd_1019529 : Nat := 4983230072969 + 3 ^ 40 * 1019529 * 2
def baseEnd_1019529 : Nat := 465340816175863841598913

theorem tailTrace_1019529 : CollatzResearch.WordTrace tailWord_1019529 prefixEnd_1019529 465340816175863841598913 := by
  unfold tailWord_1019529
  simp only [CollatzResearch.WordTrace]
  refine ⟨37185277523428029535773641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24790185015618686357182427 37185277523428029535773641)
  ·
    refine ⟨27888958142571022151830231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37185277523428029535773641 27888958142571022151830231)
    ·
      refine ⟨41833437213856533227745347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27888958142571022151830231 41833437213856533227745347)
      ·
        refine ⟨62750155820784799841618021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41833437213856533227745347 62750155820784799841618021)
        ·
          refine ⟨11765654216397149970303379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62750155820784799841618021 11765654216397149970303379)
          ·
            refine ⟨17648481324595724955455069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11765654216397149970303379 17648481324595724955455069)
            ·
              refine ⟨6618180496723396858295651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17648481324595724955455069 6618180496723396858295651)
              ·
                refine ⟨9927270745085095287443477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6618180496723396858295651 9927270745085095287443477)
                ·
                  refine ⟨465340816175863841598913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9927270745085095287443477 465340816175863841598913)
                  ·
                    rfl

theorem cell20_1019529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_1019529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019529 prefixEnd_1019529 := by exact prefixLift 1019529
  have htrace : WordTrace (prefixWord ++ tailWord_1019529) baseStart_1019529 baseEnd_1019529 := by
    simpa [prefixWord, tailWord_1019529, baseEnd_1019529] using wordTrace_append hprefix tailTrace_1019529
  have hstable : (prefixWord ++ tailWord_1019529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019529).length < 2 ^ (prefixWord ++ tailWord_1019529).sum := by decide
  have hdescent : baseEnd_1019529 < baseStart_1019529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019536 : List Nat := [2, 1, 1, 1, 1, 1, 3, 10]
def baseStart_1019536 : Nat := 118140960795 + 1019536 * 2 ^ 59
def prefixEnd_1019536 : Nat := 4983230072969 + 3 ^ 40 * 1019536 * 2
def baseEnd_1019536 : Nat := 155114670388867642788517

theorem tailTrace_1019536 : CollatzResearch.WordTrace tailWord_1019536 prefixEnd_1019536 155114670388867642788517 := by
  unfold tailWord_1019536
  simp only [CollatzResearch.WordTrace]
  refine ⟨18592766417201334865639231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24790355222935113154185641 18592766417201334865639231)
  ·
    refine ⟨27889149625802002298458847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18592766417201334865639231 27889149625802002298458847)
    ·
      refine ⟨41833724438703003447688271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27889149625802002298458847 41833724438703003447688271)
      ·
        refine ⟨62750586658054505171532407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41833724438703003447688271 62750586658054505171532407)
        ·
          refine ⟨94125879987081757757298611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62750586658054505171532407 94125879987081757757298611)
          ·
            refine ⟨141188819980622636635947917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94125879987081757757298611 141188819980622636635947917)
            ·
              refine ⟨52945807492733488738480469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141188819980622636635947917 52945807492733488738480469)
              ·
                refine ⟨155114670388867642788517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52945807492733488738480469 155114670388867642788517)
                ·
                  rfl

theorem cell20_1019536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_1019536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019536 prefixEnd_1019536 := by exact prefixLift 1019536
  have htrace : WordTrace (prefixWord ++ tailWord_1019536) baseStart_1019536 baseEnd_1019536 := by
    simpa [prefixWord, tailWord_1019536, baseEnd_1019536] using wordTrace_append hprefix tailTrace_1019536
  have hstable : (prefixWord ++ tailWord_1019536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019536).length < 2 ^ (prefixWord ++ tailWord_1019536).sum := by decide
  have hdescent : baseEnd_1019536 < baseStart_1019536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019553 : List Nat := [1, 2, 3, 3, 2, 2, 7]
def baseStart_1019553 : Nat := 118140960795 + 1019553 * 2 ^ 59
def prefixEnd_1019553 : Nat := 4983230072969 + 3 ^ 40 * 1019553 * 2
def baseEnd_1019553 : Nat := 51705752269980713866535

theorem tailTrace_1019553 : CollatzResearch.WordTrace tailWord_1019553 prefixEnd_1019553 51705752269980713866535 := by
  unfold tailWord_1019553
  simp only [CollatzResearch.WordTrace]
  refine ⟨37186152875341081634647313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24790768583560721089764875 37186152875341081634647313)
  ·
    refine ⟨27889614656505811225985485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37186152875341081634647313 27889614656505811225985485)
    ·
      refine ⟨10458605496189679209744557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27889614656505811225985485 10458605496189679209744557)
      ·
        refine ⟨3921977061071129703654209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10458605496189679209744557 3921977061071129703654209)
        ·
          refine ⟨2941482795803347277740657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3921977061071129703654209 2941482795803347277740657)
          ·
            refine ⟨2206112096852510458305493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2941482795803347277740657 2206112096852510458305493)
            ·
              refine ⟨51705752269980713866535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2206112096852510458305493 51705752269980713866535)
              ·
                rfl

theorem cell20_1019553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 7].length) (baseStart_1019553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019553 prefixEnd_1019553 := by exact prefixLift 1019553
  have htrace : WordTrace (prefixWord ++ tailWord_1019553) baseStart_1019553 baseEnd_1019553 := by
    simpa [prefixWord, tailWord_1019553, baseEnd_1019553] using wordTrace_append hprefix tailTrace_1019553
  have hstable : (prefixWord ++ tailWord_1019553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019553).length < 2 ^ (prefixWord ++ tailWord_1019553).sum := by decide
  have hdescent : baseEnd_1019553 < baseStart_1019553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019556 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 3]
def baseStart_1019556 : Nat := 118140960795 + 1019556 * 2 ^ 59
def prefixEnd_1019556 : Nat := 4983230072969 + 3 ^ 40 * 1019556 * 2
def baseEnd_1019556 : Nat := 465353139711571747698803

theorem tailTrace_1019556 : CollatzResearch.WordTrace tailWord_1019556 prefixEnd_1019556 465353139711571747698803 := by
  unfold tailWord_1019556
  simp only [CollatzResearch.WordTrace]
  refine ⟨18593131147165106573503261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24790841529553475431337681 18593131147165106573503261)
  ·
    refine ⟨6972424180186914965063723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18593131147165106573503261 6972424180186914965063723)
    ·
      refine ⟨10458636270280372447595585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6972424180186914965063723 10458636270280372447595585)
      ·
        refine ⟨7843977202710279335696689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10458636270280372447595585 7843977202710279335696689)
        ·
          refine ⟨5882982902032709501772517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7843977202710279335696689 5882982902032709501772517)
          ·
            refine ⟨1103059294131133031582347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5882982902032709501772517 1103059294131133031582347)
            ·
              refine ⟨1654588941196699547373521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103059294131133031582347 1654588941196699547373521)
              ·
                refine ⟨1240941705897524660530141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654588941196699547373521 1240941705897524660530141)
                ·
                  refine ⟨465353139711571747698803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240941705897524660530141 465353139711571747698803)
                  ·
                    rfl

theorem cell20_1019556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_1019556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019556 prefixEnd_1019556 := by exact prefixLift 1019556
  have htrace : WordTrace (prefixWord ++ tailWord_1019556) baseStart_1019556 baseEnd_1019556 := by
    simpa [prefixWord, tailWord_1019556, baseEnd_1019556] using wordTrace_append hprefix tailTrace_1019556
  have hstable : (prefixWord ++ tailWord_1019556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019556).length < 2 ^ (prefixWord ++ tailWord_1019556).sum := by decide
  have hdescent : baseEnd_1019556 < baseStart_1019556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019573 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 3]
def baseStart_1019573 : Nat := 118140960795 + 1019573 * 2 ^ 59
def prefixEnd_1019573 : Nat := 4983230072969 + 3 ^ 40 * 1019573 * 2
def baseEnd_1019573 : Nat := 465360898974795244132067

theorem tailTrace_1019573 : CollatzResearch.WordTrace tailWord_1019573 prefixEnd_1019573 465360898974795244132067 := by
  unfold tailWord_1019573
  simp only [CollatzResearch.WordTrace]
  refine ⟨37186882335268625050375373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24791254890179083366916915 37186882335268625050375373)
  ·
    refine ⟨13945080875725734393890765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37186882335268625050375373 13945080875725734393890765)
    ·
      refine ⟨5229405328397150397709037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13945080875725734393890765 5229405328397150397709037)
      ·
        refine ⟨1961026998148931399140889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5229405328397150397709037 1961026998148931399140889)
        ·
          refine ⟨1470770248611698549355667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961026998148931399140889 1470770248611698549355667)
          ·
            refine ⟨2206155372917547824033501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470770248611698549355667 2206155372917547824033501)
            ·
              refine ⟨827308264844080434012563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2206155372917547824033501 827308264844080434012563)
              ·
                refine ⟨1240962397266120651018845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827308264844080434012563 1240962397266120651018845)
                ·
                  refine ⟨465360898974795244132067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240962397266120651018845 465360898974795244132067)
                  ·
                    rfl

theorem cell20_1019573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_1019573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019573 prefixEnd_1019573 := by exact prefixLift 1019573
  have htrace : WordTrace (prefixWord ++ tailWord_1019573) baseStart_1019573 baseEnd_1019573 := by
    simpa [prefixWord, tailWord_1019573, baseEnd_1019573] using wordTrace_append hprefix tailTrace_1019573
  have hstable : (prefixWord ++ tailWord_1019573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019573).length < 2 ^ (prefixWord ++ tailWord_1019573).sum := by decide
  have hdescent : baseEnd_1019573 < baseStart_1019573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019597 : List Nat := [1, 6, 2, 1, 1, 1, 3, 3, 2]
def baseStart_1019597 : Nat := 118140960795 + 1019597 * 2 ^ 59
def prefixEnd_1019597 : Nat := 4983230072969 + 3 ^ 40 * 1019597 * 2
def baseEnd_1019597 : Nat := 465371853228757827331969

theorem tailTrace_1019597 : CollatzResearch.WordTrace tailWord_1019597 prefixEnd_1019597 465371853228757827331969 := by
  unfold tailWord_1019597
  simp only [CollatzResearch.WordTrace]
  refine ⟨37187757687181677149249045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24791838458121118099499363 37187757687181677149249045)
  ·
    refine ⟨1743176141586641116371049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37187757687181677149249045 1743176141586641116371049)
    ·
      refine ⟨1307382106189980837278287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1743176141586641116371049 1307382106189980837278287)
      ·
        refine ⟨1961073159284971255917431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307382106189980837278287 1961073159284971255917431)
        ·
          refine ⟨2941609738927456883876147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961073159284971255917431 2941609738927456883876147)
          ·
            refine ⟨4412414608391185325814221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2941609738927456883876147 4412414608391185325814221)
            ·
              refine ⟨1654655478146694497180333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4412414608391185325814221 1654655478146694497180333)
              ·
                refine ⟨620495804305010436442625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1654655478146694497180333 620495804305010436442625)
                ·
                  refine ⟨465371853228757827331969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620495804305010436442625 465371853228757827331969)
                  ·
                    rfl

theorem cell20_1019597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_1019597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019597 prefixEnd_1019597 := by exact prefixLift 1019597
  have htrace : WordTrace (prefixWord ++ tailWord_1019597) baseStart_1019597 baseEnd_1019597 := by
    simpa [prefixWord, tailWord_1019597, baseEnd_1019597] using wordTrace_append hprefix tailTrace_1019597
  have hstable : (prefixWord ++ tailWord_1019597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019597).length < 2 ^ (prefixWord ++ tailWord_1019597).sum := by decide
  have hdescent : baseEnd_1019597 < baseStart_1019597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019598 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1019598 : Nat := 118140960795 + 1019598 * 2 ^ 59
def prefixEnd_1019598 : Nat := 4983230072969 + 3 ^ 40 * 1019598 * 2
def baseEnd_1019598 : Nat := 465372309656006268298631

theorem tailTrace_1019598 : CollatzResearch.WordTrace tailWord_1019598 prefixEnd_1019598 465372309656006268298631 := by
  unfold tailWord_1019598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4648474270022256790004431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24791862773452036213356965 4648474270022256790004431)
  ·
    refine ⟨6972711405033385185006647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4648474270022256790004431 6972711405033385185006647)
    ·
      refine ⟨10459067107550077777509971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6972711405033385185006647 10459067107550077777509971)
      ·
        refine ⟨15688600661325116666264957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10459067107550077777509971 15688600661325116666264957)
        ·
          refine ⟨5883225247996918749849359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15688600661325116666264957 5883225247996918749849359)
          ·
            refine ⟨8824837871995378124774039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5883225247996918749849359 8824837871995378124774039)
            ·
              refine ⟨13237256807993067187161059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8824837871995378124774039 13237256807993067187161059)
              ·
                refine ⟨19855885211989600780741589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13237256807993067187161059 19855885211989600780741589)
                ·
                  refine ⟨465372309656006268298631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19855885211989600780741589 465372309656006268298631)
                  ·
                    rfl

theorem cell20_1019598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1019598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019598 prefixEnd_1019598 := by exact prefixLift 1019598
  have htrace : WordTrace (prefixWord ++ tailWord_1019598) baseStart_1019598 baseEnd_1019598 := by
    simpa [prefixWord, tailWord_1019598, baseEnd_1019598] using wordTrace_append hprefix tailTrace_1019598
  have hstable : (prefixWord ++ tailWord_1019598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019598).length < 2 ^ (prefixWord ++ tailWord_1019598).sum := by decide
  have hdescent : baseEnd_1019598 < baseStart_1019598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019601 : List Nat := [1, 2, 2, 1, 2, 4, 3, 3, 2]
def baseStart_1019601 : Nat := 118140960795 + 1019601 * 2 ^ 59
def prefixEnd_1019601 : Nat := 4983230072969 + 3 ^ 40 * 1019601 * 2
def baseEnd_1019601 : Nat := 465373678937751591198619

theorem tailTrace_1019601 : CollatzResearch.WordTrace tailWord_1019601 prefixEnd_1019601 465373678937751591198619 := by
  unfold tailWord_1019601
  simp only [CollatzResearch.WordTrace]
  refine ⟨37187903579167185832394657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24791935719444790554929771 37187903579167185832394657)
  ·
    refine ⟨27890927684375389374295993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37187903579167185832394657 27890927684375389374295993)
    ·
      refine ⟨20918195763281542030721995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27890927684375389374295993 20918195763281542030721995)
      ·
        refine ⟨31377293644922313046082993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20918195763281542030721995 31377293644922313046082993)
        ·
          refine ⟨23532970233691734784562245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31377293644922313046082993 23532970233691734784562245)
          ·
            refine ⟨4412431918817200272105421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23532970233691734784562245 4412431918817200272105421)
            ·
              refine ⟨1654661969556450102039533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4412431918817200272105421 1654661969556450102039533)
              ·
                refine ⟨620498238583668788264825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1654661969556450102039533 620498238583668788264825)
                ·
                  refine ⟨465373678937751591198619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620498238583668788264825 465373678937751591198619)
                  ·
                    rfl

theorem cell20_1019601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_1019601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019601 prefixEnd_1019601 := by exact prefixLift 1019601
  have htrace : WordTrace (prefixWord ++ tailWord_1019601) baseStart_1019601 baseEnd_1019601 := by
    simpa [prefixWord, tailWord_1019601, baseEnd_1019601] using wordTrace_append hprefix tailTrace_1019601
  have hstable : (prefixWord ++ tailWord_1019601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019601).length < 2 ^ (prefixWord ++ tailWord_1019601).sum := by decide
  have hdescent : baseEnd_1019601 < baseStart_1019601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019629 : List Nat := [1, 5, 1, 2, 1, 2, 1, 7]
def baseStart_1019629 : Nat := 118140960795 + 1019629 * 2 ^ 59
def prefixEnd_1019629 : Nat := 4983230072969 + 3 ^ 40 * 1019629 * 2
def baseEnd_1019629 : Nat := 155128819633569312755057

theorem tailTrace_1019629 : CollatzResearch.WordTrace tailWord_1019629 prefixEnd_1019629 155128819633569312755057 := by
  unfold tailWord_1019629
  simp only [CollatzResearch.WordTrace]
  refine ⟨37188924823065746614413941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24792616548710497742942627 37188924823065746614413941)
  ·
    refine ⟨3486461702162413745101307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37188924823065746614413941 3486461702162413745101307)
    ·
      refine ⟨5229692553243620617651961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3486461702162413745101307 5229692553243620617651961)
      ·
        refine ⟨3922269414932715463238971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5229692553243620617651961 3922269414932715463238971)
        ·
          refine ⟨5883404122399073194858457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3922269414932715463238971 5883404122399073194858457)
          ·
            refine ⟨4412553091799304896143843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5883404122399073194858457 4412553091799304896143843)
            ·
              refine ⟨6618829637698957344215765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4412553091799304896143843 6618829637698957344215765)
              ·
                refine ⟨155128819633569312755057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6618829637698957344215765 155128819633569312755057)
                ·
                  rfl

theorem cell20_1019629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_1019629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019629 prefixEnd_1019629 := by exact prefixLift 1019629
  have htrace : WordTrace (prefixWord ++ tailWord_1019629) baseStart_1019629 baseEnd_1019629 := by
    simpa [prefixWord, tailWord_1019629, baseEnd_1019629] using wordTrace_append hprefix tailTrace_1019629
  have hstable : (prefixWord ++ tailWord_1019629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019629).length < 2 ^ (prefixWord ++ tailWord_1019629).sum := by decide
  have hdescent : baseEnd_1019629 < baseStart_1019629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019684 : List Nat := [2, 3, 1, 3, 2, 3, 1, 5]
def baseStart_1019684 : Nat := 118140960795 + 1019684 * 2 ^ 59
def prefixEnd_1019684 : Nat := 4983230072969 + 3 ^ 40 * 1019684 * 2
def baseEnd_1019684 : Nat := 155137187466457397143871

theorem tailTrace_1019684 : CollatzResearch.WordTrace tailWord_1019684 prefixEnd_1019684 155137187466457397143871 := by
  unfold tailWord_1019684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18595465418933245503833053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24793953891910994005110737 18595465418933245503833053)
  ·
    refine ⟨6973299532099967063937395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18595465418933245503833053 6973299532099967063937395)
    ·
      refine ⟨10459949298149950595906093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6973299532099967063937395 10459949298149950595906093)
      ·
        refine ⟨3922480986806231473464785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10459949298149950595906093 3922480986806231473464785)
        ·
          refine ⟨2941860740104673605098589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3922480986806231473464785 2941860740104673605098589)
          ·
            refine ⟨1103197777539252601911971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2941860740104673605098589 1103197777539252601911971)
            ·
              refine ⟨1654796666308878902867957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103197777539252601911971 1654796666308878902867957)
              ·
                refine ⟨155137187466457397143871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1654796666308878902867957 155137187466457397143871)
                ·
                  rfl

theorem cell20_1019684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_1019684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019684 prefixEnd_1019684 := by exact prefixLift 1019684
  have htrace : WordTrace (prefixWord ++ tailWord_1019684) baseStart_1019684 baseEnd_1019684 := by
    simpa [prefixWord, tailWord_1019684, baseEnd_1019684] using wordTrace_append hprefix tailTrace_1019684
  have hstable : (prefixWord ++ tailWord_1019684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019684).length < 2 ^ (prefixWord ++ tailWord_1019684).sum := by decide
  have hdescent : baseEnd_1019684 < baseStart_1019684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019698 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1019698 : Nat := 118140960795 + 1019698 * 2 ^ 59
def prefixEnd_1019698 : Nat := 4983230072969 + 3 ^ 40 * 1019698 * 2
def baseEnd_1019698 : Nat := 465417952380850364964889

theorem tailTrace_1019698 : CollatzResearch.WordTrace tailWord_1019698 prefixEnd_1019698 465417952380850364964889 := by
  unfold tailWord_1019698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9297860364953942849668937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24794294306543847599117165 9297860364953942849668937)
  ·
    refine ⟨6973395273715457137251703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9297860364953942849668937 6973395273715457137251703)
    ·
      refine ⟨10460092910573185705877555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6973395273715457137251703 10460092910573185705877555)
      ·
        refine ⟨15690139365859778558816333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10460092910573185705877555 15690139365859778558816333)
        ·
          refine ⟨5883802262197416959556125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15690139365859778558816333 5883802262197416959556125)
          ·
            refine ⟨2206425848324031359833547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5883802262197416959556125 2206425848324031359833547)
            ·
              refine ⟨3309638772486047039750321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206425848324031359833547 3309638772486047039750321)
              ·
                refine ⟨2482229079364535279812741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3309638772486047039750321 2482229079364535279812741)
                ·
                  refine ⟨465417952380850364964889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2482229079364535279812741 465417952380850364964889)
                  ·
                    rfl

theorem cell20_1019698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1019698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019698 prefixEnd_1019698 := by exact prefixLift 1019698
  have htrace : WordTrace (prefixWord ++ tailWord_1019698) baseStart_1019698 baseEnd_1019698 := by
    simpa [prefixWord, tailWord_1019698, baseEnd_1019698] using wordTrace_append hprefix tailTrace_1019698
  have hstable : (prefixWord ++ tailWord_1019698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019698).length < 2 ^ (prefixWord ++ tailWord_1019698).sum := by decide
  have hdescent : baseEnd_1019698 < baseStart_1019698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019715 : List Nat := [1, 1, 1, 3, 1, 6, 2, 3, 2]
def baseStart_1019715 : Nat := 118140960795 + 1019715 * 2 ^ 59
def prefixEnd_1019715 : Nat := 4983230072969 + 3 ^ 40 * 1019715 * 2
def baseEnd_1019715 : Nat := 465425711644073861398153

theorem tailTrace_1019715 : CollatzResearch.WordTrace tailWord_1019715 prefixEnd_1019715 465425711644073861398153 := by
  unfold tailWord_1019715
  simp only [CollatzResearch.WordTrace]
  refine ⟨37192061500754183302044599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24794707667169455534696399 37192061500754183302044599)
  ·
    refine ⟨55788092251131274953066899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37192061500754183302044599 55788092251131274953066899)
    ·
      refine ⟨83682138376696912429600349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55788092251131274953066899 83682138376696912429600349)
      ·
        refine ⟨31380801891261342161100131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83682138376696912429600349 31380801891261342161100131)
        ·
          refine ⟨47071202836892013241650197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31380801891261342161100131 47071202836892013241650197)
          ·
            refine ⟨2206462632979313120702353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47071202836892013241650197 2206462632979313120702353)
            ·
              refine ⟨1654846974734484840526765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206462632979313120702353 1654846974734484840526765)
              ·
                refine ⟨620567615525431815197537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1654846974734484840526765 620567615525431815197537)
                ·
                  refine ⟨465425711644073861398153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620567615525431815197537 465425711644073861398153)
                  ·
                    rfl

theorem cell20_1019715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 2].length) (baseStart_1019715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019715 prefixEnd_1019715 := by exact prefixLift 1019715
  have htrace : WordTrace (prefixWord ++ tailWord_1019715) baseStart_1019715 baseEnd_1019715 := by
    simpa [prefixWord, tailWord_1019715, baseEnd_1019715] using wordTrace_append hprefix tailTrace_1019715
  have hstable : (prefixWord ++ tailWord_1019715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019715).length < 2 ^ (prefixWord ++ tailWord_1019715).sum := by decide
  have hdescent : baseEnd_1019715 < baseStart_1019715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019725 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1019725 : Nat := 118140960795 + 1019725 * 2 ^ 59
def prefixEnd_1019725 : Nat := 4983230072969 + 3 ^ 40 * 1019725 * 2
def baseEnd_1019725 : Nat := 465430275916558271064779

theorem tailTrace_1019725 : CollatzResearch.WordTrace tailWord_1019725 prefixEnd_1019725 465430275916558271064779 := by
  unfold tailWord_1019725
  simp only [CollatzResearch.WordTrace]
  refine ⟨37192426230717955009908629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24794950820478636673272419 37192426230717955009908629)
  ·
    refine ⟨1743394979564904141089467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37192426230717955009908629 1743394979564904141089467)
    ·
      refine ⟨2615092469347356211634201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743394979564904141089467 2615092469347356211634201)
      ·
        refine ⟨1961319352010517158725651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2615092469347356211634201 1961319352010517158725651)
        ·
          refine ⟨2941979028015775738088477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961319352010517158725651 2941979028015775738088477)
          ·
            refine ⟨1103242135505915901783179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2941979028015775738088477 1103242135505915901783179)
            ·
              refine ⟨1654863203258873852674769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103242135505915901783179 1654863203258873852674769)
              ·
                refine ⟨1241147402444155389506077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654863203258873852674769 1241147402444155389506077)
                ·
                  refine ⟨465430275916558271064779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241147402444155389506077 465430275916558271064779)
                  ·
                    rfl

theorem cell20_1019725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1019725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019725 prefixEnd_1019725 := by exact prefixLift 1019725
  have htrace : WordTrace (prefixWord ++ tailWord_1019725) baseStart_1019725 baseEnd_1019725 := by
    simpa [prefixWord, tailWord_1019725, baseEnd_1019725] using wordTrace_append hprefix tailTrace_1019725
  have hstable : (prefixWord ++ tailWord_1019725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019725).length < 2 ^ (prefixWord ++ tailWord_1019725).sum := by decide
  have hdescent : baseEnd_1019725 < baseStart_1019725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019729 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 3]
def baseStart_1019729 : Nat := 118140960795 + 1019729 * 2 ^ 59
def prefixEnd_1019729 : Nat := 4983230072969 + 3 ^ 40 * 1019729 * 2
def baseEnd_1019729 : Nat := 465432101625552034931429

theorem tailTrace_1019729 : CollatzResearch.WordTrace tailWord_1019729 prefixEnd_1019729 465432101625552034931429 := by
  unfold tailWord_1019729
  simp only [CollatzResearch.WordTrace]
  refine ⟨37192572122703463693054241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24795048081802309128702827 37192572122703463693054241)
  ·
    refine ⟨27894429092027597769790681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37192572122703463693054241 27894429092027597769790681)
    ·
      refine ⟨20920821819020698327343011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27894429092027597769790681 20920821819020698327343011)
      ·
        refine ⟨31381232728531047491014517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20920821819020698327343011 31381232728531047491014517)
        ·
          refine ⟨2941990568299785702282611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31381232728531047491014517 2941990568299785702282611)
          ·
            refine ⟨4412985852449678553423917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2941990568299785702282611 4412985852449678553423917)
            ·
              refine ⟨1654869694668629457533969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4412985852449678553423917 1654869694668629457533969)
              ·
                refine ⟨1241152271001472093150477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654869694668629457533969 1241152271001472093150477)
                ·
                  refine ⟨465432101625552034931429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241152271001472093150477 465432101625552034931429)
                  ·
                    rfl

theorem cell20_1019729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_1019729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019729 prefixEnd_1019729 := by exact prefixLift 1019729
  have htrace : WordTrace (prefixWord ++ tailWord_1019729) baseStart_1019729 baseEnd_1019729 := by
    simpa [prefixWord, tailWord_1019729, baseEnd_1019729] using wordTrace_append hprefix tailTrace_1019729
  have hstable : (prefixWord ++ tailWord_1019729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019729).length < 2 ^ (prefixWord ++ tailWord_1019729).sum := by decide
  have hdescent : baseEnd_1019729 < baseStart_1019729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019766 : List Nat := [5, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_1019766 : Nat := 118140960795 + 1019766 * 2 ^ 59
def prefixEnd_1019766 : Nat := 4983230072969 + 3 ^ 40 * 1019766 * 2
def baseEnd_1019766 : Nat := 465448989433744350697945

theorem tailTrace_1019766 : CollatzResearch.WordTrace tailWord_1019766 prefixEnd_1019766 465448989433744350697945 := by
  unfold tailWord_1019766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324620101473088688259447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24795947749046279341434101 2324620101473088688259447)
  ·
    refine ⟨3486930152209633032389171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2324620101473088688259447 3486930152209633032389171)
    ·
      refine ⟨5230395228314449548583757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3486930152209633032389171 5230395228314449548583757)
      ·
        refine ⟨1961398210617918580718909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5230395228314449548583757 1961398210617918580718909)
        ·
          refine ⟨735524328981719467769591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1961398210617918580718909 735524328981719467769591)
          ·
            refine ⟨1103286493472579201654387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735524328981719467769591 1103286493472579201654387)
            ·
              refine ⟨1654929740208868802481581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103286493472579201654387 1654929740208868802481581)
              ·
                refine ⟨620598652578325800930593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1654929740208868802481581 620598652578325800930593)
                ·
                  refine ⟨465448989433744350697945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620598652578325800930593 465448989433744350697945)
                  ·
                    rfl

theorem cell20_1019766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_1019766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019766 prefixEnd_1019766 := by exact prefixLift 1019766
  have htrace : WordTrace (prefixWord ++ tailWord_1019766) baseStart_1019766 baseEnd_1019766 := by
    simpa [prefixWord, tailWord_1019766, baseEnd_1019766] using wordTrace_append hprefix tailTrace_1019766
  have hstable : (prefixWord ++ tailWord_1019766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019766).length < 2 ^ (prefixWord ++ tailWord_1019766).sum := by decide
  have hdescent : baseEnd_1019766 < baseStart_1019766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019777 : List Nat := [1, 2, 4, 4, 2, 1, 6]
def baseStart_1019777 : Nat := 118140960795 + 1019777 * 2 ^ 59
def prefixEnd_1019777 : Nat := 4983230072969 + 3 ^ 40 * 1019777 * 2
def baseEnd_1019777 : Nat := 51717112237053022370137

theorem tailTrace_1019777 : CollatzResearch.WordTrace tailWord_1019777 prefixEnd_1019777 51717112237053022370137 := by
  unfold tailWord_1019777
  simp only [CollatzResearch.WordTrace]
  refine ⟨37194322826529567890801585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24796215217686378593867723 37194322826529567890801585)
  ·
    refine ⟨27895742119897175918101189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37194322826529567890801585 27895742119897175918101189)
    ·
      refine ⟨5230451647480720484643973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27895742119897175918101189 5230451647480720484643973)
      ·
        refine ⟨980709683902635090870745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5230451647480720484643973 980709683902635090870745)
        ·
          refine ⟨735532262926976318153059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980709683902635090870745 735532262926976318153059)
          ·
            refine ⟨1103298394390464477229589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735532262926976318153059 1103298394390464477229589)
            ·
              refine ⟨51717112237053022370137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1103298394390464477229589 51717112237053022370137)
              ·
                rfl

theorem cell20_1019777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 6].length) (baseStart_1019777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019777 prefixEnd_1019777 := by exact prefixLift 1019777
  have htrace : WordTrace (prefixWord ++ tailWord_1019777) baseStart_1019777 baseEnd_1019777 := by
    simpa [prefixWord, tailWord_1019777, baseEnd_1019777] using wordTrace_append hprefix tailTrace_1019777
  have hstable : (prefixWord ++ tailWord_1019777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019777).length < 2 ^ (prefixWord ++ tailWord_1019777).sum := by decide
  have hdescent : baseEnd_1019777 < baseStart_1019777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019788 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1019788 : Nat := 118140960795 + 1019788 * 2 ^ 59
def prefixEnd_1019788 : Nat := 4983230072969 + 3 ^ 40 * 1019788 * 2
def baseEnd_1019788 : Nat := 465459030833210051964521

theorem tailTrace_1019788 : CollatzResearch.WordTrace tailWord_1019788 prefixEnd_1019788 465459030833210051964521 := by
  unfold tailWord_1019788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18597362014744858384726009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24796482686326477846301345 18597362014744858384726009)
  ·
    refine ⟨13948021511058643788544507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18597362014744858384726009 13948021511058643788544507)
    ·
      refine ⟨20922032266587965682816761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13948021511058643788544507 20922032266587965682816761)
      ·
        refine ⟨15691524199940974262112571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20922032266587965682816761 15691524199940974262112571)
        ·
          refine ⟨23537286299911461393168857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15691524199940974262112571 23537286299911461393168857)
          ·
            refine ⟨17652964724933596044876643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23537286299911461393168857 17652964724933596044876643)
            ·
              refine ⟨26479447087400394067314965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17652964724933596044876643 26479447087400394067314965)
              ·
                refine ⟨1241224082221893471905389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26479447087400394067314965 1241224082221893471905389)
                ·
                  refine ⟨465459030833210051964521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241224082221893471905389 465459030833210051964521)
                  ·
                    rfl

theorem cell20_1019788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1019788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019788 prefixEnd_1019788 := by exact prefixLift 1019788
  have htrace : WordTrace (prefixWord ++ tailWord_1019788) baseStart_1019788 baseEnd_1019788 := by
    simpa [prefixWord, tailWord_1019788, baseEnd_1019788] using wordTrace_append hprefix tailTrace_1019788
  have hstable : (prefixWord ++ tailWord_1019788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019788).length < 2 ^ (prefixWord ++ tailWord_1019788).sum := by decide
  have hdescent : baseEnd_1019788 < baseStart_1019788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019805 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 3]
def baseStart_1019805 : Nat := 118140960795 + 1019805 * 2 ^ 59
def prefixEnd_1019805 : Nat := 4983230072969 + 3 ^ 40 * 1019805 * 2
def baseEnd_1019805 : Nat := 465466790096433548397785

theorem tailTrace_1019805 : CollatzResearch.WordTrace tailWord_1019805 prefixEnd_1019805 465466790096433548397785 := by
  unfold tailWord_1019805
  simp only [CollatzResearch.WordTrace]
  refine ⟨37195344070428128672820869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24796896046952085781880579 37195344070428128672820869)
  ·
    refine ⟨6974127013205274126153913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37195344070428128672820869 6974127013205274126153913)
    ·
      refine ⟨5230595259903955594615435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6974127013205274126153913 5230595259903955594615435)
      ·
        refine ⟨7845892889855933391923153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230595259903955594615435 7845892889855933391923153)
        ·
          refine ⟨5884419667391950043942365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7845892889855933391923153 5884419667391950043942365)
          ·
            refine ⟨2206657375271981266478387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5884419667391950043942365 2206657375271981266478387)
            ·
              refine ⟨3309986062907971899717581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206657375271981266478387 3309986062907971899717581)
              ·
                refine ⟨1241244773590489462394093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3309986062907971899717581 1241244773590489462394093)
                ·
                  refine ⟨465466790096433548397785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241244773590489462394093 465466790096433548397785)
                  ·
                    rfl

theorem cell20_1019805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_1019805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019805 prefixEnd_1019805 := by exact prefixLift 1019805
  have htrace : WordTrace (prefixWord ++ tailWord_1019805) baseStart_1019805 baseEnd_1019805 := by
    simpa [prefixWord, tailWord_1019805, baseEnd_1019805] using wordTrace_append hprefix tailTrace_1019805
  have hstable : (prefixWord ++ tailWord_1019805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019805).length < 2 ^ (prefixWord ++ tailWord_1019805).sum := by decide
  have hdescent : baseEnd_1019805 < baseStart_1019805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019836 : List Nat := [2, 2, 2, 5, 2, 7]
def baseStart_1019836 : Nat := 118140960795 + 1019836 * 2 ^ 59
def prefixEnd_1019836 : Nat := 4983230072969 + 3 ^ 40 * 1019836 * 2
def baseEnd_1019836 : Nat := 17240034790412415494975

theorem tailTrace_1019836 : CollatzResearch.WordTrace tailWord_1019836 prefixEnd_1019836 17240034790412415494975 := by
  unfold tailWord_1019836
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598237366657910483599681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24797649822210547311466241 18598237366657910483599681)
  ·
    refine ⟨13948678024993432862699761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18598237366657910483599681 13948678024993432862699761)
    ·
      refine ⟨10461508518745074647024821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13948678024993432862699761 10461508518745074647024821)
      ·
        refine ⟨980766423632350748158577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10461508518745074647024821 980766423632350748158577)
        ·
          refine ⟨735574817724263061118933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980766423632350748158577 735574817724263061118933)
          ·
            refine ⟨17240034790412415494975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 735574817724263061118933 17240034790412415494975)
            ·
              rfl

theorem cell20_1019836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 7].length) (baseStart_1019836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019836 prefixEnd_1019836 := by exact prefixLift 1019836
  have htrace : WordTrace (prefixWord ++ tailWord_1019836) baseStart_1019836 baseEnd_1019836 := by
    simpa [prefixWord, tailWord_1019836, baseEnd_1019836] using wordTrace_append hprefix tailTrace_1019836
  have hstable : (prefixWord ++ tailWord_1019836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019836).length < 2 ^ (prefixWord ++ tailWord_1019836).sum := by decide
  have hdescent : baseEnd_1019836 < baseStart_1019836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019864 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 3]
def baseStart_1019864 : Nat := 118140960795 + 1019864 * 2 ^ 59
def prefixEnd_1019864 : Nat := 4983230072969 + 3 ^ 40 * 1019864 * 2
def baseEnd_1019864 : Nat := 465493719304091565430877

theorem tailTrace_1019864 : CollatzResearch.WordTrace tailWord_1019864 prefixEnd_1019864 465493719304091565430877 := by
  unfold tailWord_1019864
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598747988607190874609323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24798330651476254499479097 18598747988607190874609323)
  ·
    refine ⟨27898121982910786311913985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18598747988607190874609323 27898121982910786311913985)
    ·
      refine ⟨20923591487183089733935489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27898121982910786311913985 20923591487183089733935489)
      ·
        refine ⟨15692693615387317300451617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20923591487183089733935489 15692693615387317300451617)
        ·
          refine ⟨11769520211540487975338713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15692693615387317300451617 11769520211540487975338713)
          ·
            refine ⟨8827140158655365981504035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11769520211540487975338713 8827140158655365981504035)
            ·
              refine ⟨13240710237983048972256053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827140158655365981504035 13240710237983048972256053)
              ·
                refine ⟨1241316584810910841149005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13240710237983048972256053 1241316584810910841149005)
                ·
                  refine ⟨465493719304091565430877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241316584810910841149005 465493719304091565430877)
                  ·
                    rfl

theorem cell20_1019864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_1019864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019864 prefixEnd_1019864 := by exact prefixLift 1019864
  have htrace : WordTrace (prefixWord ++ tailWord_1019864) baseStart_1019864 baseEnd_1019864 := by
    simpa [prefixWord, tailWord_1019864, baseEnd_1019864] using wordTrace_append hprefix tailTrace_1019864
  have hstable : (prefixWord ++ tailWord_1019864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019864).length < 2 ^ (prefixWord ++ tailWord_1019864).sum := by decide
  have hdescent : baseEnd_1019864 < baseStart_1019864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019871 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_1019871 : Nat := 118140960795 + 1019871 * 2 ^ 59
def prefixEnd_1019871 : Nat := 4983230072969 + 3 ^ 40 * 1019871 * 2
def baseEnd_1019871 : Nat := 465496914294830652197515

theorem tailTrace_1019871 : CollatzResearch.WordTrace tailWord_1019871 prefixEnd_1019871 465496914294830652197515 := by
  unfold tailWord_1019871
  simp only [CollatzResearch.WordTrace]
  refine ⟨37197751288189021944723467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24798500858792681296482311 37197751288189021944723467)
  ·
    refine ⟨55796626932283532917085201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37197751288189021944723467 55796626932283532917085201)
    ·
      refine ⟨41847470199212649687813901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55796626932283532917085201 41847470199212649687813901)
      ·
        refine ⟨15692801324704743632930213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41847470199212649687813901 15692801324704743632930213)
        ·
          refine ⟨2942400248382139431174415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15692801324704743632930213 2942400248382139431174415)
          ·
            refine ⟨4413600372573209146761623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942400248382139431174415 4413600372573209146761623)
            ·
              refine ⟨6620400558859813720142435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413600372573209146761623 6620400558859813720142435)
              ·
                refine ⟨9930600838289720580213653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6620400558859813720142435 9930600838289720580213653)
                ·
                  refine ⟨465496914294830652197515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9930600838289720580213653 465496914294830652197515)
                  ·
                    rfl

theorem cell20_1019871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_1019871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019871 prefixEnd_1019871 := by exact prefixLift 1019871
  have htrace : WordTrace (prefixWord ++ tailWord_1019871) baseStart_1019871 baseEnd_1019871 := by
    simpa [prefixWord, tailWord_1019871, baseEnd_1019871] using wordTrace_append hprefix tailTrace_1019871
  have hstable : (prefixWord ++ tailWord_1019871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019871).length < 2 ^ (prefixWord ++ tailWord_1019871).sum := by decide
  have hdescent : baseEnd_1019871 < baseStart_1019871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019888 : List Nat := [2, 1, 1, 1, 3, 2, 3, 5, 2]
def baseStart_1019888 : Nat := 118140960795 + 1019888 * 2 ^ 59
def prefixEnd_1019888 : Nat := 4983230072969 + 3 ^ 40 * 1019888 * 2
def baseEnd_1019888 : Nat := 465504673558054148630779

theorem tailTrace_1019888 : CollatzResearch.WordTrace tailWord_1019888 prefixEnd_1019888 465504673558054148630779 := by
  unfold tailWord_1019888
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599185664563716924046159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24798914219418289232061545 18599185664563716924046159)
  ·
    refine ⟨27898778496845575386069239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18599185664563716924046159 27898778496845575386069239)
    ·
      refine ⟨41848167745268363079103859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27898778496845575386069239 41848167745268363079103859)
      ·
        refine ⟨62772251617902544618655789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41848167745268363079103859 62772251617902544618655789)
        ·
          refine ⟨23539594356713454231995921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62772251617902544618655789 23539594356713454231995921)
          ·
            refine ⟨17654695767535090673996941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23539594356713454231995921 17654695767535090673996941)
            ·
              refine ⟨6620510912825659002748853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17654695767535090673996941 6620510912825659002748853)
              ·
                refine ⟨620672898077405531507705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6620510912825659002748853 620672898077405531507705)
                ·
                  refine ⟨465504673558054148630779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620672898077405531507705 465504673558054148630779)
                  ·
                    rfl

theorem cell20_1019888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_1019888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019888 prefixEnd_1019888 := by exact prefixLift 1019888
  have htrace : WordTrace (prefixWord ++ tailWord_1019888) baseStart_1019888 baseEnd_1019888 := by
    simpa [prefixWord, tailWord_1019888, baseEnd_1019888] using wordTrace_append hprefix tailTrace_1019888
  have hstable : (prefixWord ++ tailWord_1019888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019888).length < 2 ^ (prefixWord ++ tailWord_1019888).sum := by decide
  have hdescent : baseEnd_1019888 < baseStart_1019888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019909 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1019909 : Nat := 118140960795 + 1019909 * 2 ^ 59
def prefixEnd_1019909 : Nat := 4983230072969 + 3 ^ 40 * 1019909 * 2
def baseEnd_1019909 : Nat := 465514258530271408930693

theorem tailTrace_1019909 : CollatzResearch.WordTrace tailWord_1019909 prefixEnd_1019909 465514258530271408930693 := by
  unfold tailWord_1019909
  simp only [CollatzResearch.WordTrace]
  refine ⟨37199137262051354434606781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24799424841367569623071187 37199137262051354434606781)
  ·
    refine ⟨13949676473269257912977543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37199137262051354434606781 13949676473269257912977543)
    ·
      refine ⟨20924514709903886869466315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13949676473269257912977543 20924514709903886869466315)
      ·
        refine ⟨31386772064855830304199473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20924514709903886869466315 31386772064855830304199473)
        ·
          refine ⟨23540079048641872728149605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31386772064855830304199473 23540079048641872728149605)
          ·
            refine ⟨4413764821620351136528051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23540079048641872728149605 4413764821620351136528051)
            ·
              refine ⟨6620647232430526704792077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413764821620351136528051 6620647232430526704792077)
              ·
                refine ⟨2482742712161447514297029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6620647232430526704792077 2482742712161447514297029)
                ·
                  refine ⟨465514258530271408930693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2482742712161447514297029 465514258530271408930693)
                  ·
                    rfl

theorem cell20_1019909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1019909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019909 prefixEnd_1019909 := by exact prefixLift 1019909
  have htrace : WordTrace (prefixWord ++ tailWord_1019909) baseStart_1019909 baseEnd_1019909 := by
    simpa [prefixWord, tailWord_1019909, baseEnd_1019909] using wordTrace_append hprefix tailTrace_1019909
  have hstable : (prefixWord ++ tailWord_1019909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019909).length < 2 ^ (prefixWord ++ tailWord_1019909).sum := by decide
  have hdescent : baseEnd_1019909 < baseStart_1019909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019916 : List Nat := [2, 2, 1, 2, 3, 1, 2, 7]
def baseStart_1019916 : Nat := 118140960795 + 1019916 * 2 ^ 59
def prefixEnd_1019916 : Nat := 4983230072969 + 3 ^ 40 * 1019916 * 2
def baseEnd_1019916 : Nat := 155172484507003498565777

theorem tailTrace_1019916 : CollatzResearch.WordTrace tailWord_1019916 prefixEnd_1019916 155172484507003498565777 := by
  unfold tailWord_1019916
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599696286512997315055801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24799595048683996420074401 18599696286512997315055801)
  ·
    refine ⟨13949772214884747986291851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18599696286512997315055801 13949772214884747986291851)
    ·
      refine ⟨20924658322327121979437777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13949772214884747986291851 20924658322327121979437777)
      ·
        refine ⟨15693493741745341484578333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20924658322327121979437777 15693493741745341484578333)
        ·
          refine ⟨5885060153154503056716875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15693493741745341484578333 5885060153154503056716875)
          ·
            refine ⟨8827590229731754585075313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885060153154503056716875 8827590229731754585075313)
            ·
              refine ⟨6620692672298815938806485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8827590229731754585075313 6620692672298815938806485)
              ·
                refine ⟨155172484507003498565777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6620692672298815938806485 155172484507003498565777)
                ·
                  rfl

theorem cell20_1019916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_1019916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019916 prefixEnd_1019916 := by exact prefixLift 1019916
  have htrace : WordTrace (prefixWord ++ tailWord_1019916) baseStart_1019916 baseEnd_1019916 := by
    simpa [prefixWord, tailWord_1019916, baseEnd_1019916] using wordTrace_append hprefix tailTrace_1019916
  have hstable : (prefixWord ++ tailWord_1019916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019916).length < 2 ^ (prefixWord ++ tailWord_1019916).sum := by decide
  have hdescent : baseEnd_1019916 < baseStart_1019916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019933 : List Nat := [1, 4, 2, 2, 2, 2, 1, 6]
def baseStart_1019933 : Nat := 118140960795 + 1019933 * 2 ^ 59
def prefixEnd_1019933 : Nat := 4983230072969 + 3 ^ 40 * 1019933 * 2
def baseEnd_1019933 : Nat := 155175070928077997376865

theorem tailTrace_1019933 : CollatzResearch.WordTrace tailWord_1019933 prefixEnd_1019933 155175070928077997376865 := by
  unfold tailWord_1019933
  simp only [CollatzResearch.WordTrace]
  refine ⟨37200012613964406533480453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24800008409309604355653635 37200012613964406533480453)
  ·
    refine ⟨6975002365118326225027585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37200012613964406533480453 6975002365118326225027585)
    ·
      refine ⟨5231251773838744668770689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6975002365118326225027585 5231251773838744668770689)
      ·
        refine ⟨3923438830379058501578017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5231251773838744668770689 3923438830379058501578017)
        ·
          refine ⟨2942579122784293876183513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3923438830379058501578017 2942579122784293876183513)
          ·
            refine ⟨2206934342088220407137635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2942579122784293876183513 2206934342088220407137635)
            ·
              refine ⟨3310401513132330610706453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206934342088220407137635 3310401513132330610706453)
              ·
                refine ⟨155175070928077997376865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3310401513132330610706453 155175070928077997376865)
                ·
                  rfl

theorem cell20_1019933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_1019933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019933 prefixEnd_1019933 := by exact prefixLift 1019933
  have htrace : WordTrace (prefixWord ++ tailWord_1019933) baseStart_1019933 baseEnd_1019933 := by
    simpa [prefixWord, tailWord_1019933, baseEnd_1019933] using wordTrace_append hprefix tailTrace_1019933
  have hstable : (prefixWord ++ tailWord_1019933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019933).length < 2 ^ (prefixWord ++ tailWord_1019933).sum := by decide
  have hdescent : baseEnd_1019933 < baseStart_1019933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019954 : List Nat := [3, 2, 1, 1, 2, 3, 8]
def baseStart_1019954 : Nat := 118140960795 + 1019954 * 2 ^ 59
def prefixEnd_1019954 : Nat := 4983230072969 + 3 ^ 40 * 1019954 * 2
def baseEnd_1019954 : Nat := 51726088639605694714501

theorem tailTrace_1019954 : CollatzResearch.WordTrace tailWord_1019954 prefixEnd_1019954 51726088639605694714501 := by
  unfold tailWord_1019954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9300194636722081779998729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24800519031258884746663277 9300194636722081779998729)
  ·
    refine ⟨6975145977541561334999047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9300194636722081779998729 6975145977541561334999047)
    ·
      refine ⟨10462718966312342002498571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6975145977541561334999047 10462718966312342002498571)
      ·
        refine ⟨15694078449468513003747857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10462718966312342002498571 15694078449468513003747857)
        ·
          refine ⟨11770558837101384752810893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15694078449468513003747857 11770558837101384752810893)
          ·
            refine ⟨4413959563913019282304085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11770558837101384752810893 4413959563913019282304085)
            ·
              refine ⟨51726088639605694714501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4413959563913019282304085 51726088639605694714501)
              ·
                rfl

theorem cell20_1019954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 8].length) (baseStart_1019954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019954 prefixEnd_1019954 := by exact prefixLift 1019954
  have htrace : WordTrace (prefixWord ++ tailWord_1019954) baseStart_1019954 baseEnd_1019954 := by
    simpa [prefixWord, tailWord_1019954, baseEnd_1019954] using wordTrace_append hprefix tailTrace_1019954
  have hstable : (prefixWord ++ tailWord_1019954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019954).length < 2 ^ (prefixWord ++ tailWord_1019954).sum := by decide
  have hdescent : baseEnd_1019954 < baseStart_1019954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019960 : List Nat := [2, 1, 2, 1, 6, 1, 3, 2, 2]
def baseStart_1019960 : Nat := 118140960795 + 1019960 * 2 ^ 59
def prefixEnd_1019960 : Nat := 4983230072969 + 3 ^ 40 * 1019960 * 2
def baseEnd_1019960 : Nat := 465537536319941898230485

theorem tailTrace_1019960 : CollatzResearch.WordTrace tailWord_1019960 prefixEnd_1019960 465537536319941898230485 := by
  unfold tailWord_1019960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18600498692433295072356667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24800664923244393429808889 18600498692433295072356667)
  ·
    refine ⟨27900748038649942608535001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18600498692433295072356667 27900748038649942608535001)
    ·
      refine ⟨20925561028987456956401251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27900748038649942608535001 20925561028987456956401251)
      ·
        refine ⟨31388341543481185434601877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20925561028987456956401251 31388341543481185434601877)
        ·
          refine ⟨1471328509850680567246963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31388341543481185434601877 1471328509850680567246963)
          ·
            refine ⟨2206992764776020850870445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471328509850680567246963 2206992764776020850870445)
            ·
              refine ⟨827622286791007819076417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2206992764776020850870445 827622286791007819076417)
              ·
                refine ⟨620716715093255864307313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827622286791007819076417 620716715093255864307313)
                ·
                  refine ⟨465537536319941898230485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620716715093255864307313 465537536319941898230485)
                  ·
                    rfl

theorem cell20_1019960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_1019960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019960 prefixEnd_1019960 := by exact prefixLift 1019960
  have htrace : WordTrace (prefixWord ++ tailWord_1019960) baseStart_1019960 baseEnd_1019960 := by
    simpa [prefixWord, tailWord_1019960, baseEnd_1019960] using wordTrace_append hprefix tailTrace_1019960
  have hstable : (prefixWord ++ tailWord_1019960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019960).length < 2 ^ (prefixWord ++ tailWord_1019960).sum := by decide
  have hdescent : baseEnd_1019960 < baseStart_1019960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019974 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1019974 : Nat := 118140960795 + 1019974 * 2 ^ 59
def prefixEnd_1019974 : Nat := 4983230072969 + 3 ^ 40 * 1019974 * 2
def baseEnd_1019974 : Nat := 465543926301420071763761

theorem tailTrace_1019974 : CollatzResearch.WordTrace tailWord_1019974 prefixEnd_1019974 465543926301420071763761 := by
  unfold tailWord_1019974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162547125212995954241343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24801005337877247023815317 1162547125212995954241343)
  ·
    refine ⟨1743820687819493931362015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1162547125212995954241343 1743820687819493931362015)
    ·
      refine ⟨2615731031729240897043023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743820687819493931362015 2615731031729240897043023)
      ·
        refine ⟨3923596547593861345564535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2615731031729240897043023 3923596547593861345564535)
        ·
          refine ⟨5885394821390792018346803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3923596547593861345564535 5885394821390792018346803)
          ·
            refine ⟨8828092232086188027520205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885394821390792018346803 8828092232086188027520205)
            ·
              refine ⟨3310534587032320510320077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8828092232086188027520205 3310534587032320510320077)
              ·
                refine ⟨1241450470137120191370029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3310534587032320510320077 1241450470137120191370029)
                ·
                  refine ⟨465543926301420071763761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241450470137120191370029 465543926301420071763761)
                  ·
                    rfl

theorem cell20_1019974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1019974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019974 prefixEnd_1019974 := by exact prefixLift 1019974
  have htrace : WordTrace (prefixWord ++ tailWord_1019974) baseStart_1019974 baseEnd_1019974 := by
    simpa [prefixWord, tailWord_1019974, baseEnd_1019974] using wordTrace_append hprefix tailTrace_1019974
  have hstable : (prefixWord ++ tailWord_1019974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019974).length < 2 ^ (prefixWord ++ tailWord_1019974).sum := by decide
  have hdescent : baseEnd_1019974 < baseStart_1019974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019992 : List Nat := [2, 1, 2, 2, 1, 4, 2, 6]
def baseStart_1019992 : Nat := 118140960795 + 1019992 * 2 ^ 59
def prefixEnd_1019992 : Nat := 4983230072969 + 3 ^ 40 * 1019992 * 2
def baseEnd_1019992 : Nat := 155184047330630669721229

theorem tailTrace_1019992 : CollatzResearch.WordTrace tailWord_1019992 prefixEnd_1019992 155184047330630669721229 := by
  unfold tailWord_1019992
  simp only [CollatzResearch.WordTrace]
  refine ⟨18601082260375329804939115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24801443013833773073252153 18601082260375329804939115)
  ·
    refine ⟨27901623390562994707408673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18601082260375329804939115 27901623390562994707408673)
    ·
      refine ⟨20926217542922246030556505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27901623390562994707408673 20926217542922246030556505)
      ·
        refine ⟨15694663157191684522917379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20926217542922246030556505 15694663157191684522917379)
        ·
          refine ⟨23541994735787526784376069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15694663157191684522917379 23541994735787526784376069)
          ·
            refine ⟨4414124012960161272070513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23541994735787526784376069 4414124012960161272070513)
            ·
              refine ⟨3310593009720120954052885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4414124012960161272070513 3310593009720120954052885)
              ·
                refine ⟨155184047330630669721229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3310593009720120954052885 155184047330630669721229)
                ·
                  rfl

theorem cell20_1019992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_1019992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019992 prefixEnd_1019992 := by exact prefixLift 1019992
  have htrace : WordTrace (prefixWord ++ tailWord_1019992) baseStart_1019992 baseEnd_1019992 := by
    simpa [prefixWord, tailWord_1019992, baseEnd_1019992] using wordTrace_append hprefix tailTrace_1019992
  have hstable : (prefixWord ++ tailWord_1019992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019992).length < 2 ^ (prefixWord ++ tailWord_1019992).sum := by decide
  have hdescent : baseEnd_1019992 < baseStart_1019992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019999 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_1019999 : Nat := 118140960795 + 1019999 * 2 ^ 59
def prefixEnd_1019999 : Nat := 4983230072969 + 3 ^ 40 * 1019999 * 2
def baseEnd_1019999 : Nat := 465555336982631095930325

theorem tailTrace_1019999 : CollatzResearch.WordTrace tailWord_1019999 prefixEnd_1019999 465555336982631095930325 := by
  unfold tailWord_1019999
  simp only [CollatzResearch.WordTrace]
  refine ⟨37202419831725299805383051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24801613221150199870255367 37202419831725299805383051)
  ·
    refine ⟨55803629747587949708074577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37202419831725299805383051 55803629747587949708074577)
    ·
      refine ⟨41852722310690962281055933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55803629747587949708074577 41852722310690962281055933)
      ·
        refine ⟨15694770866509110855395975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41852722310690962281055933 15694770866509110855395975)
        ·
          refine ⟨23542156299763666283093963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15694770866509110855395975 23542156299763666283093963)
          ·
            refine ⟨35313234449645499424640945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23542156299763666283093963 35313234449645499424640945)
            ·
              refine ⟨26484925837234124568480709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35313234449645499424640945 26484925837234124568480709)
              ·
                refine ⟨4965923594481398356590133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26484925837234124568480709 4965923594481398356590133)
                ·
                  refine ⟨465555336982631095930325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4965923594481398356590133 465555336982631095930325)
                  ·
                    rfl

theorem cell20_1019999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_1019999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1019999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1019999 prefixEnd_1019999 := by exact prefixLift 1019999
  have htrace : WordTrace (prefixWord ++ tailWord_1019999) baseStart_1019999 baseEnd_1019999 := by
    simpa [prefixWord, tailWord_1019999, baseEnd_1019999] using wordTrace_append hprefix tailTrace_1019999
  have hstable : (prefixWord ++ tailWord_1019999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019999).length < 2 ^ (prefixWord ++ tailWord_1019999).sum := by decide
  have hdescent : baseEnd_1019999 < baseStart_1019999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020016 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 3]
def baseStart_1020016 : Nat := 118140960795 + 1020016 * 2 ^ 59
def prefixEnd_1020016 : Nat := 4983230072969 + 3 ^ 40 * 1020016 * 2
def baseEnd_1020016 : Nat := 465563096245854592363589

theorem tailTrace_1020016 : CollatzResearch.WordTrace tailWord_1020016 prefixEnd_1020016 465563096245854592363589 := by
  unfold tailWord_1020016
  simp only [CollatzResearch.WordTrace]
  refine ⟨18601519936331855854375951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24802026581775807805834601 18601519936331855854375951)
  ·
    refine ⟨27902279904497783781563927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18601519936331855854375951 27902279904497783781563927)
    ·
      refine ⟨41853419856746675672345891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27902279904497783781563927 41853419856746675672345891)
      ·
        refine ⟨62780129785120013508518837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41853419856746675672345891 62780129785120013508518837)
        ·
          refine ⟨5885637167355001266423641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62780129785120013508518837 5885637167355001266423641)
          ·
            refine ⟨4414227875516250949817731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5885637167355001266423641 4414227875516250949817731)
            ·
              refine ⟨6621341813274376424726597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4414227875516250949817731 6621341813274376424726597)
              ·
                refine ⟨1241501589988945579636237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6621341813274376424726597 1241501589988945579636237)
                ·
                  refine ⟨465563096245854592363589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241501589988945579636237 465563096245854592363589)
                  ·
                    rfl

theorem cell20_1020016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_1020016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020016 prefixEnd_1020016 := by exact prefixLift 1020016
  have htrace : WordTrace (prefixWord ++ tailWord_1020016) baseStart_1020016 baseEnd_1020016 := by
    simpa [prefixWord, tailWord_1020016, baseEnd_1020016] using wordTrace_append hprefix tailTrace_1020016
  have hstable : (prefixWord ++ tailWord_1020016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020016).length < 2 ^ (prefixWord ++ tailWord_1020016).sum := by decide
  have hdescent : baseEnd_1020016 < baseStart_1020016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020040 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_1020040 : Nat := 118140960795 + 1020040 * 2 ^ 59
def prefixEnd_1020040 : Nat := 4983230072969 + 3 ^ 40 * 1020040 * 2
def baseEnd_1020040 : Nat := 465574050499817175563491

theorem tailTrace_1020040 : CollatzResearch.WordTrace tailWord_1020040 prefixEnd_1020040 465574050499817175563491 := by
  unfold tailWord_1020040
  simp only [CollatzResearch.WordTrace]
  refine ⟨18601957612288381903812787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24802610149717842538417049 18601957612288381903812787)
  ·
    refine ⟨27902936418432572855719181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18601957612288381903812787 27902936418432572855719181)
    ·
      refine ⟨10463601156912214820894693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27902936418432572855719181 10463601156912214820894693)
      ·
        refine ⟨1961925216921040278917755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10463601156912214820894693 1961925216921040278917755)
        ·
          refine ⟨2942887825381560418376633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961925216921040278917755 2942887825381560418376633)
          ·
            refine ⟨2207165869036170313782475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2942887825381560418376633 2207165869036170313782475)
            ·
              refine ⟨3310748803554255470673713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207165869036170313782475 3310748803554255470673713)
              ·
                refine ⟨2483061602665691603005285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3310748803554255470673713 2483061602665691603005285)
                ·
                  refine ⟨465574050499817175563491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483061602665691603005285 465574050499817175563491)
                  ·
                    rfl

theorem cell20_1020040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_1020040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020040 prefixEnd_1020040 := by exact prefixLift 1020040
  have htrace : WordTrace (prefixWord ++ tailWord_1020040) baseStart_1020040 baseEnd_1020040 := by
    simpa [prefixWord, tailWord_1020040, baseEnd_1020040] using wordTrace_append hprefix tailTrace_1020040
  have hstable : (prefixWord ++ tailWord_1020040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020040).length < 2 ^ (prefixWord ++ tailWord_1020040).sum := by decide
  have hdescent : baseEnd_1020040 < baseStart_1020040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020071 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 5]
def baseStart_1020071 : Nat := 118140960795 + 1020071 * 2 ^ 59
def prefixEnd_1020071 : Nat := 4983230072969 + 3 ^ 40 * 1020071 * 2
def baseEnd_1020071 : Nat := 465588199744518845530031

theorem tailTrace_1020071 : CollatzResearch.WordTrace tailWord_1020071 prefixEnd_1020071 465588199744518845530031 := by
  unfold tailWord_1020071
  simp only [CollatzResearch.WordTrace]
  refine ⟨37205045887464456102004067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24803363924976304068002711 37205045887464456102004067)
  ·
    refine ⟨55807568831196684153006101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37205045887464456102004067 55807568831196684153006101)
    ·
      refine ⟨2615979788962344569672161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55807568831196684153006101 2615979788962344569672161)
      ·
        refine ⟨1961984841721758427254121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2615979788962344569672161 1961984841721758427254121)
        ·
          refine ⟨1471488631291318820440591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961984841721758427254121 1471488631291318820440591)
          ·
            refine ⟨2207232946936978230660887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471488631291318820440591 2207232946936978230660887)
            ·
              refine ⟨3310849420405467345991331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207232946936978230660887 3310849420405467345991331)
              ·
                refine ⟨4966274130608201018986997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310849420405467345991331 4966274130608201018986997)
                ·
                  refine ⟨465588199744518845530031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4966274130608201018986997 465588199744518845530031)
                  ·
                    rfl

theorem cell20_1020071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 5].length) (baseStart_1020071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020071 prefixEnd_1020071 := by exact prefixLift 1020071
  have htrace : WordTrace (prefixWord ++ tailWord_1020071) baseStart_1020071 baseEnd_1020071 := by
    simpa [prefixWord, tailWord_1020071, baseEnd_1020071] using wordTrace_append hprefix tailTrace_1020071
  have hstable : (prefixWord ++ tailWord_1020071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020071).length < 2 ^ (prefixWord ++ tailWord_1020071).sum := by decide
  have hdescent : baseEnd_1020071 < baseStart_1020071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020098 : List Nat := [3, 5, 1, 1, 1, 3, 2, 4]
def baseStart_1020098 : Nat := 118140960795 + 1020098 * 2 ^ 59
def prefixEnd_1020098 : Nat := 4983230072969 + 3 ^ 40 * 1020098 * 2
def baseEnd_1020098 : Nat := 155200174426742250543307

theorem tailTrace_1020098 : CollatzResearch.WordTrace tailWord_1020098 prefixEnd_1020098 155200174426742250543307 := by
  unfold tailWord_1020098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9301507664591659928309237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24804020438911093142157965 9301507664591659928309237)
  ·
    refine ⟨872016343555468118278991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9301507664591659928309237 872016343555468118278991)
    ·
      refine ⟨1308024515333202177418487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 872016343555468118278991 1308024515333202177418487)
      ·
        refine ⟨1962036772999803266127731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1308024515333202177418487 1962036772999803266127731)
        ·
          refine ⟨2943055159499704899191597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962036772999803266127731 2943055159499704899191597)
          ·
            refine ⟨1103645684812389337196849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2943055159499704899191597 1103645684812389337196849)
            ·
              refine ⟨827734263609292002897637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103645684812389337196849 827734263609292002897637)
              ·
                refine ⟨155200174426742250543307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 827734263609292002897637 155200174426742250543307)
                ·
                  rfl

theorem cell20_1020098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_1020098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020098 prefixEnd_1020098 := by exact prefixLift 1020098
  have htrace : WordTrace (prefixWord ++ tailWord_1020098) baseStart_1020098 baseEnd_1020098 := by
    simpa [prefixWord, tailWord_1020098, baseEnd_1020098] using wordTrace_append hprefix tailTrace_1020098
  have hstable : (prefixWord ++ tailWord_1020098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020098).length < 2 ^ (prefixWord ++ tailWord_1020098).sum := by decide
  have hdescent : baseEnd_1020098 < baseStart_1020098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020106 : List Nat := [3, 1, 2, 1, 3, 1, 3, 6]
def baseStart_1020106 : Nat := 118140960795 + 1020106 * 2 ^ 59
def prefixEnd_1020106 : Nat := 4983230072969 + 3 ^ 40 * 1020106 * 2
def baseEnd_1020106 : Nat := 155201391566071426454407

theorem tailTrace_1020106 : CollatzResearch.WordTrace tailWord_1020106 prefixEnd_1020106 155201391566071426454407 := by
  unfold tailWord_1020106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9301580610584414269882043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24804214961558438053018781 9301580610584414269882043)
  ·
    refine ⟨13952370915876621404823065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9301580610584414269882043 13952370915876621404823065)
    ·
      refine ⟨10464278186907466053617299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13952370915876621404823065 10464278186907466053617299)
      ·
        refine ⟨15696417280361199080425949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10464278186907466053617299 15696417280361199080425949)
        ·
          refine ⟨5886156480135449655159731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15696417280361199080425949 5886156480135449655159731)
          ·
            refine ⟨8829234720203174482739597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886156480135449655159731 8829234720203174482739597)
            ·
              refine ⟨3310963020076190431027349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8829234720203174482739597 3310963020076190431027349)
              ·
                refine ⟨155201391566071426454407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3310963020076190431027349 155201391566071426454407)
                ·
                  rfl

theorem cell20_1020106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_1020106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020106 prefixEnd_1020106 := by exact prefixLift 1020106
  have htrace : WordTrace (prefixWord ++ tailWord_1020106) baseStart_1020106 baseEnd_1020106 := by
    simpa [prefixWord, tailWord_1020106, baseEnd_1020106] using wordTrace_append hprefix tailTrace_1020106
  have hstable : (prefixWord ++ tailWord_1020106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020106).length < 2 ^ (prefixWord ++ tailWord_1020106).sum := by decide
  have hdescent : baseEnd_1020106 < baseStart_1020106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020113 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1020113 : Nat := 118140960795 + 1020113 * 2 ^ 59
def prefixEnd_1020113 : Nat := 4983230072969 + 3 ^ 40 * 1020113 * 2
def baseEnd_1020113 : Nat := 465607369688953366129859

theorem tailTrace_1020113 : CollatzResearch.WordTrace tailWord_1020113 prefixEnd_1020113 465607369688953366129859 := by
  unfold tailWord_1020113
  simp only [CollatzResearch.WordTrace]
  refine ⟨37206577753312297275032993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24804385168874864850021995 37206577753312297275032993)
  ·
    refine ⟨27904933314984222956274745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37206577753312297275032993 27904933314984222956274745)
    ·
      refine ⟨20928699986238167217206059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27904933314984222956274745 20928699986238167217206059)
      ·
        refine ⟨31393049979357250825809089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20928699986238167217206059 31393049979357250825809089)
        ·
          refine ⟨23544787484517938119356817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31393049979357250825809089 23544787484517938119356817)
          ·
            refine ⟨17658590613388453589517613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23544787484517938119356817 17658590613388453589517613)
            ·
              refine ⟨6621971480020670096069105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17658590613388453589517613 6621971480020670096069105)
              ·
                refine ⟨4966478610015502572051829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6621971480020670096069105 4966478610015502572051829)
                ·
                  refine ⟨465607369688953366129859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4966478610015502572051829 465607369688953366129859)
                  ·
                    rfl

theorem cell20_1020113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1020113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020113 prefixEnd_1020113 := by exact prefixLift 1020113
  have htrace : WordTrace (prefixWord ++ tailWord_1020113) baseStart_1020113 baseEnd_1020113 := by
    simpa [prefixWord, tailWord_1020113, baseEnd_1020113] using wordTrace_append hprefix tailTrace_1020113
  have hstable : (prefixWord ++ tailWord_1020113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020113).length < 2 ^ (prefixWord ++ tailWord_1020113).sum := by decide
  have hdescent : baseEnd_1020113 < baseStart_1020113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020213 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1020213 : Nat := 118140960795 + 1020213 * 2 ^ 59
def prefixEnd_1020213 : Nat := 4983230072969 + 3 ^ 40 * 1020213 * 2
def baseEnd_1020213 : Nat := 465653012413797462796117

theorem tailTrace_1020213 : CollatzResearch.WordTrace tailWord_1020213 prefixEnd_1020213 465653012413797462796117 := by
  unfold tailWord_1020213
  simp only [CollatzResearch.WordTrace]
  refine ⟨37210225052950014353673293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24806816701966676235782195 37210225052950014353673293)
  ·
    refine ⟨13953834394856255382627485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37210225052950014353673293 13953834394856255382627485)
    ·
      refine ⟨5232687898071095768485307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13953834394856255382627485 5232687898071095768485307)
      ·
        refine ⟨7849031847106643652727961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5232687898071095768485307 7849031847106643652727961)
        ·
          refine ⟨5886773885329982739545971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7849031847106643652727961 5886773885329982739545971)
          ·
            refine ⟨8830160827994974109318957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886773885329982739545971 8830160827994974109318957)
            ·
              refine ⟨3311310310498115290994609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8830160827994974109318957 3311310310498115290994609)
              ·
                refine ⟨2483482732873586468245957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311310310498115290994609 2483482732873586468245957)
                ·
                  refine ⟨465653012413797462796117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483482732873586468245957 465653012413797462796117)
                  ·
                    rfl

theorem cell20_1020213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1020213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020213 prefixEnd_1020213 := by exact prefixLift 1020213
  have htrace : WordTrace (prefixWord ++ tailWord_1020213) baseStart_1020213 baseEnd_1020213 := by
    simpa [prefixWord, tailWord_1020213, baseEnd_1020213] using wordTrace_append hprefix tailTrace_1020213
  have hstable : (prefixWord ++ tailWord_1020213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020213).length < 2 ^ (prefixWord ++ tailWord_1020213).sum := by decide
  have hdescent : baseEnd_1020213 < baseStart_1020213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020244 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1020244 : Nat := 118140960795 + 1020244 * 2 ^ 59
def prefixEnd_1020244 : Nat := 4983230072969 + 3 ^ 40 * 1020244 * 2
def baseEnd_1020244 : Nat := 465667161658499132762657

theorem tailTrace_1020244 : CollatzResearch.WordTrace tailWord_1020244 prefixEnd_1020244 465667161658499132762657 := by
  unfold tailWord_1020244
  simp only [CollatzResearch.WordTrace]
  refine ⟨18605677857918853324025893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24807570477225137765367857 18605677857918853324025893)
  ·
    refine ⟨3488564598359784998254855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18605677857918853324025893 3488564598359784998254855)
    ·
      refine ⟨5232846897539677497382283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3488564598359784998254855 5232846897539677497382283)
      ·
        refine ⟨7849270346309516246073425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5232846897539677497382283 7849270346309516246073425)
        ·
          refine ⟨5886952759732137184555069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7849270346309516246073425 5886952759732137184555069)
          ·
            refine ⟨2207607284899551444208151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5886952759732137184555069 2207607284899551444208151)
            ·
              refine ⟨3311410927349327166312227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207607284899551444208151 3311410927349327166312227)
              ·
                refine ⟨4967116391023990749468341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3311410927349327166312227 4967116391023990749468341)
                ·
                  refine ⟨465667161658499132762657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4967116391023990749468341 465667161658499132762657)
                  ·
                    rfl

theorem cell20_1020244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1020244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020244 prefixEnd_1020244 := by exact prefixLift 1020244
  have htrace : WordTrace (prefixWord ++ tailWord_1020244) baseStart_1020244 baseEnd_1020244 := by
    simpa [prefixWord, tailWord_1020244, baseEnd_1020244] using wordTrace_append hprefix tailTrace_1020244
  have hstable : (prefixWord ++ tailWord_1020244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020244).length < 2 ^ (prefixWord ++ tailWord_1020244).sum := by decide
  have hdescent : baseEnd_1020244 < baseStart_1020244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020261 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 3]
def baseStart_1020261 : Nat := 118140960795 + 1020261 * 2 ^ 59
def prefixEnd_1020261 : Nat := 4983230072969 + 3 ^ 40 * 1020261 * 2
def baseEnd_1020261 : Nat := 465674920921722629195921

theorem tailTrace_1020261 : CollatzResearch.WordTrace tailWord_1020261 prefixEnd_1020261 465674920921722629195921 := by
  unfold tailWord_1020261
  simp only [CollatzResearch.WordTrace]
  refine ⟨37211975756776118551420637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24807983837850745700947091 37211975756776118551420637)
  ·
    refine ⟨13954490908791044456782739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37211975756776118551420637 13954490908791044456782739)
    ·
      refine ⟨20931736363186566685174109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13954490908791044456782739 20931736363186566685174109)
      ·
        refine ⟨7849401136194962506940291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20931736363186566685174109 7849401136194962506940291)
        ·
          refine ⟨11774101704292443760410437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7849401136194962506940291 11774101704292443760410437)
          ·
            refine ⟨2207644069554833205076957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11774101704292443760410437 2207644069554833205076957)
            ·
              refine ⟨827866526083062451903859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2207644069554833205076957 827866526083062451903859)
              ·
                refine ⟨1241799789124593677855789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827866526083062451903859 1241799789124593677855789)
                ·
                  refine ⟨465674920921722629195921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241799789124593677855789 465674920921722629195921)
                  ·
                    rfl

theorem cell20_1020261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_1020261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020261 prefixEnd_1020261 := by exact prefixLift 1020261
  have htrace : WordTrace (prefixWord ++ tailWord_1020261) baseStart_1020261 baseEnd_1020261 := by
    simpa [prefixWord, tailWord_1020261, baseEnd_1020261] using wordTrace_append hprefix tailTrace_1020261
  have hstable : (prefixWord ++ tailWord_1020261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020261).length < 2 ^ (prefixWord ++ tailWord_1020261).sum := by decide
  have hdescent : baseEnd_1020261 < baseStart_1020261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020285 : List Nat := [1, 4, 1, 1, 2, 5, 1, 3, 2]
def baseStart_1020285 : Nat := 118140960795 + 1020285 * 2 ^ 59
def prefixEnd_1020285 : Nat := 4983230072969 + 3 ^ 40 * 1020285 * 2
def baseEnd_1020285 : Nat := 465685875175685212395823

theorem tailTrace_1020285 : CollatzResearch.WordTrace tailWord_1020285 prefixEnd_1020285 465685875175685212395823 := by
  unfold tailWord_1020285
  simp only [CollatzResearch.WordTrace]
  refine ⟨37212851108689170650294309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24808567405792780433529539 37212851108689170650294309)
  ·
    refine ⟨6977409582879219496930183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37212851108689170650294309 6977409582879219496930183)
    ·
      refine ⟨10466114374318829245395275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6977409582879219496930183 10466114374318829245395275)
      ·
        refine ⟨15699171561478243868092913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10466114374318829245395275 15699171561478243868092913)
        ·
          refine ⟨11774378671108682901069685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15699171561478243868092913 11774378671108682901069685)
          ·
            refine ⟨1103848000416439021975283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11774378671108682901069685 1103848000416439021975283)
            ·
              refine ⟨1655772000624658532962925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103848000416439021975283 1655772000624658532962925)
              ·
                refine ⟨620914500234246949861097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1655772000624658532962925 620914500234246949861097)
                ·
                  refine ⟨465685875175685212395823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620914500234246949861097 465685875175685212395823)
                  ·
                    rfl

theorem cell20_1020285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_1020285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020285 prefixEnd_1020285 := by exact prefixLift 1020285
  have htrace : WordTrace (prefixWord ++ tailWord_1020285) baseStart_1020285 baseEnd_1020285 := by
    simpa [prefixWord, tailWord_1020285, baseEnd_1020285] using wordTrace_append hprefix tailTrace_1020285
  have hstable : (prefixWord ++ tailWord_1020285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020285).length < 2 ^ (prefixWord ++ tailWord_1020285).sum := by decide
  have hdescent : baseEnd_1020285 < baseStart_1020285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020302 : List Nat := [4, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_1020302 : Nat := 118140960795 + 1020302 * 2 ^ 59
def prefixEnd_1020302 : Nat := 4983230072969 + 3 ^ 40 * 1020302 * 2
def baseEnd_1020302 : Nat := 465693634438908708829087

theorem tailTrace_1020302 : CollatzResearch.WordTrace tailWord_1020302 prefixEnd_1020302 465693634438908708829087 := by
  unfold tailWord_1020302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4651683893703447819207895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24808980766418388369108773 4651683893703447819207895)
  ·
    refine ⟨6977525840555171728811843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4651683893703447819207895 6977525840555171728811843)
    ·
      refine ⟨10466288760832757593217765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6977525840555171728811843 10466288760832757593217765)
      ·
        refine ⟨1962429142656142048728331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10466288760832757593217765 1962429142656142048728331)
        ·
          refine ⟨2943643713984213073092497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962429142656142048728331 2943643713984213073092497)
          ·
            refine ⟨2207732785488159804819373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2943643713984213073092497 2207732785488159804819373)
            ·
              refine ⟨827899794558059926807265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2207732785488159804819373 827899794558059926807265)
              ·
                refine ⟨620924845918544945105449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827899794558059926807265 620924845918544945105449)
                ·
                  refine ⟨465693634438908708829087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620924845918544945105449 465693634438908708829087)
                  ·
                    rfl

theorem cell20_1020302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_1020302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020302 prefixEnd_1020302 := by exact prefixLift 1020302
  have htrace : WordTrace (prefixWord ++ tailWord_1020302) baseStart_1020302 baseEnd_1020302 := by
    simpa [prefixWord, tailWord_1020302, baseEnd_1020302] using wordTrace_append hprefix tailTrace_1020302
  have hstable : (prefixWord ++ tailWord_1020302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020302).length < 2 ^ (prefixWord ++ tailWord_1020302).sum := by decide
  have hdescent : baseEnd_1020302 < baseStart_1020302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020320 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 3]
def baseStart_1020320 : Nat := 118140960795 + 1020320 * 2 ^ 59
def prefixEnd_1020320 : Nat := 4983230072969 + 3 ^ 40 * 1020320 * 2
def baseEnd_1020320 : Nat := 465701850129380646229013

theorem tailTrace_1020320 : CollatzResearch.WordTrace tailWord_1020320 prefixEnd_1020320 465701850129380646229013 := by
  unfold tailWord_1020320
  simp only [CollatzResearch.WordTrace]
  refine ⟨18607063831781185813909207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24809418442374914418545609 18607063831781185813909207)
  ·
    refine ⟨27910595747671778720863811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18607063831781185813909207 27910595747671778720863811)
    ·
      refine ⟨41865893621507668081295717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27910595747671778720863811 41865893621507668081295717)
      ·
        refine ⟨7849855054032687765242947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41865893621507668081295717 7849855054032687765242947)
        ·
          refine ⟨11774782581049031647864421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7849855054032687765242947 11774782581049031647864421)
          ·
            refine ⟨2207771733946693433974579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11774782581049031647864421 2207771733946693433974579)
            ·
              refine ⟨3311657600920040150961869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207771733946693433974579 3311657600920040150961869)
              ·
                refine ⟨1241871600345015056610701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3311657600920040150961869 1241871600345015056610701)
                ·
                  refine ⟨465701850129380646229013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241871600345015056610701 465701850129380646229013)
                  ·
                    rfl

theorem cell20_1020320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_1020320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020320 prefixEnd_1020320 := by exact prefixLift 1020320
  have htrace : WordTrace (prefixWord ++ tailWord_1020320) baseStart_1020320 baseEnd_1020320 := by
    simpa [prefixWord, tailWord_1020320, baseEnd_1020320] using wordTrace_append hprefix tailTrace_1020320
  have hstable : (prefixWord ++ tailWord_1020320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020320).length < 2 ^ (prefixWord ++ tailWord_1020320).sum := by decide
  have hdescent : baseEnd_1020320 < baseStart_1020320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020353 : List Nat := [1, 2, 7, 1, 2, 1, 2, 2, 2]
def baseStart_1020353 : Nat := 118140960795 + 1020353 * 2 ^ 59
def prefixEnd_1020353 : Nat := 4983230072969 + 3 ^ 40 * 1020353 * 2
def baseEnd_1020353 : Nat := 465716912228579198128879

theorem tailTrace_1020353 : CollatzResearch.WordTrace tailWord_1020353 prefixEnd_1020353 465716912228579198128879 := by
  unfold tailWord_1020353
  simp only [CollatzResearch.WordTrace]
  refine ⟨37215331272442818263769713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24810220848295212175846475 37215331272442818263769713)
  ·
    refine ⟨27911498454332113697827285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37215331272442818263769713 27911498454332113697827285)
    ·
      refine ⟨654175745023408914792827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 27911498454332113697827285 654175745023408914792827)
      ·
        refine ⟨981263617535113372189241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654175745023408914792827 981263617535113372189241)
        ·
          refine ⟨735947713151335029141931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981263617535113372189241 735947713151335029141931)
          ·
            refine ⟨1103921569727002543712897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735947713151335029141931 1103921569727002543712897)
            ·
              refine ⟨827941177295251907784673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103921569727002543712897 827941177295251907784673)
              ·
                refine ⟨620955882971438930838505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827941177295251907784673 620955882971438930838505)
                ·
                  refine ⟨465716912228579198128879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620955882971438930838505 465716912228579198128879)
                  ·
                    rfl

theorem cell20_1020353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_1020353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020353 prefixEnd_1020353 := by exact prefixLift 1020353
  have htrace : WordTrace (prefixWord ++ tailWord_1020353) baseStart_1020353 baseEnd_1020353 := by
    simpa [prefixWord, tailWord_1020353, baseEnd_1020353] using wordTrace_append hprefix tailTrace_1020353
  have hstable : (prefixWord ++ tailWord_1020353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020353).length < 2 ^ (prefixWord ++ tailWord_1020353).sum := by decide
  have hdescent : baseEnd_1020353 < baseStart_1020353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020420 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1020420 : Nat := 118140960795 + 1020420 * 2 ^ 59
def prefixEnd_1020420 : Nat := 4983230072969 + 3 ^ 40 * 1020420 * 2
def baseEnd_1020420 : Nat := 465747492854224742895271

theorem tailTrace_1020420 : CollatzResearch.WordTrace tailWord_1020420 prefixEnd_1020420 465747492854224742895271 := by
  unfold tailWord_1020420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18608887481600044353229357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24811849975466725804305809 18608887481600044353229357)
  ·
    refine ⟨6978332805600016632461009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18608887481600044353229357 6978332805600016632461009)
    ·
      refine ⟨5233749604200012474345757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6978332805600016632461009 5233749604200012474345757)
      ·
        refine ⟨1962656101575004677879659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5233749604200012474345757 1962656101575004677879659)
        ·
          refine ⟨2943984152362507016819489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962656101575004677879659 2943984152362507016819489)
          ·
            refine ⟨2207988114271880262614617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2943984152362507016819489 2207988114271880262614617)
            ·
              refine ⟨1655991085703910196960963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207988114271880262614617 1655991085703910196960963)
              ·
                refine ⟨2483986628555865295441445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655991085703910196960963 2483986628555865295441445)
                ·
                  refine ⟨465747492854224742895271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483986628555865295441445 465747492854224742895271)
                  ·
                    rfl

theorem cell20_1020420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1020420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020420 prefixEnd_1020420 := by exact prefixLift 1020420
  have htrace : WordTrace (prefixWord ++ tailWord_1020420) baseStart_1020420 baseEnd_1020420 := by
    simpa [prefixWord, tailWord_1020420, baseEnd_1020420] using wordTrace_append hprefix tailTrace_1020420
  have hstable : (prefixWord ++ tailWord_1020420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020420).length < 2 ^ (prefixWord ++ tailWord_1020420).sum := by decide
  have hdescent : baseEnd_1020420 < baseStart_1020420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020461 : List Nat := [1, 5, 4, 1, 1, 2, 6]
def baseStart_1020461 : Nat := 118140960795 + 1020461 * 2 ^ 59
def prefixEnd_1020461 : Nat := 4983230072969 + 3 ^ 40 * 1020461 * 2
def baseEnd_1020461 : Nat := 51751800707934535836493

theorem tailTrace_1020461 : CollatzResearch.WordTrace tailWord_1020461 prefixEnd_1020461 51751800707934535836493 := by
  unfold tailWord_1020461
  simp only [CollatzResearch.WordTrace]
  refine ⟨37219270356051552708701237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24812846904034368472467491 37219270356051552708701237)
  ·
    refine ⟨3489306595879833066440741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37219270356051552708701237 3489306595879833066440741)
    ·
      refine ⟨654244986727468699957639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3489306595879833066440741 654244986727468699957639)
      ·
        refine ⟨981367480091203049936459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654244986727468699957639 981367480091203049936459)
        ·
          refine ⟨1472051220136804574904689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981367480091203049936459 1472051220136804574904689)
          ·
            refine ⟨1104038415102603431178517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472051220136804574904689 1104038415102603431178517)
            ·
              refine ⟨51751800707934535836493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1104038415102603431178517 51751800707934535836493)
              ·
                rfl

theorem cell20_1020461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 6].length) (baseStart_1020461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020461 prefixEnd_1020461 := by exact prefixLift 1020461
  have htrace : WordTrace (prefixWord ++ tailWord_1020461) baseStart_1020461 baseEnd_1020461 := by
    simpa [prefixWord, tailWord_1020461, baseEnd_1020461] using wordTrace_append hprefix tailTrace_1020461
  have hstable : (prefixWord ++ tailWord_1020461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020461).length < 2 ^ (prefixWord ++ tailWord_1020461).sum := by decide
  have hdescent : baseEnd_1020461 < baseStart_1020461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020530 : List Nat := [3, 2, 1, 2, 4, 2, 2, 2, 2]
def baseStart_1020530 : Nat := 118140960795 + 1020530 * 2 ^ 59
def prefixEnd_1020530 : Nat := 4983230072969 + 3 ^ 40 * 1020530 * 2
def baseEnd_1020530 : Nat := 465797699851553249228155

theorem tailTrace_1020530 : CollatzResearch.WordTrace tailWord_1020530 prefixEnd_1020530 465797699851553249228155 := by
  unfold tailWord_1020530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9305446748200394373240761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24814524661867718328642029 9305446748200394373240761)
  ·
    refine ⟨6979085061150295779930571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9305446748200394373240761 6979085061150295779930571)
    ·
      refine ⟨10468627591725443669895857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6979085061150295779930571 10468627591725443669895857)
      ·
        refine ⟨7851470693794082752421893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10468627591725443669895857 7851470693794082752421893)
        ·
          refine ⟨1472150755086390516079105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7851470693794082752421893 1472150755086390516079105)
          ·
            refine ⟨1104113066314792887059329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472150755086390516079105 1104113066314792887059329)
            ·
              refine ⟨828084799736094665294497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104113066314792887059329 828084799736094665294497)
              ·
                refine ⟨621063599802070998970873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828084799736094665294497 621063599802070998970873)
                ·
                  refine ⟨465797699851553249228155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621063599802070998970873 465797699851553249228155)
                  ·
                    rfl

theorem cell20_1020530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_1020530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020530 prefixEnd_1020530 := by exact prefixLift 1020530
  have htrace : WordTrace (prefixWord ++ tailWord_1020530) baseStart_1020530 baseEnd_1020530 := by
    simpa [prefixWord, tailWord_1020530, baseEnd_1020530] using wordTrace_append hprefix tailTrace_1020530
  have hstable : (prefixWord ++ tailWord_1020530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020530).length < 2 ^ (prefixWord ++ tailWord_1020530).sum := by decide
  have hdescent : baseEnd_1020530 < baseStart_1020530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020541 : List Nat := [1, 4, 1, 1, 5, 2, 1, 5]
def baseStart_1020541 : Nat := 118140960795 + 1020541 * 2 ^ 59
def prefixEnd_1020541 : Nat := 4983230072969 + 3 ^ 40 * 1020541 * 2
def baseEnd_1020541 : Nat := 155267573517095366620481

theorem tailTrace_1020541 : CollatzResearch.WordTrace tailWord_1020541 prefixEnd_1020541 155267573517095366620481 := by
  unfold tailWord_1020541
  simp only [CollatzResearch.WordTrace]
  refine ⟨37222188195761726371613477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24814792130507817581075651 37222188195761726371613477)
  ·
    refine ⟨6979160286705323694677527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37222188195761726371613477 6979160286705323694677527)
    ·
      refine ⟨10468740430057985542016291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6979160286705323694677527 10468740430057985542016291)
      ·
        refine ⟨15703110645086978313024437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10468740430057985542016291 15703110645086978313024437)
        ·
          refine ⟨1472166622976904216846041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15703110645086978313024437 1472166622976904216846041)
          ·
            refine ⟨1104124967232678162634531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472166622976904216846041 1104124967232678162634531)
            ·
              refine ⟨1656187450849017243951797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104124967232678162634531 1656187450849017243951797)
              ·
                refine ⟨155267573517095366620481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1656187450849017243951797 155267573517095366620481)
                ·
                  rfl

theorem cell20_1020541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 5].length) (baseStart_1020541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020541 prefixEnd_1020541 := by exact prefixLift 1020541
  have htrace : WordTrace (prefixWord ++ tailWord_1020541) baseStart_1020541 baseEnd_1020541 := by
    simpa [prefixWord, tailWord_1020541, baseEnd_1020541] using wordTrace_append hprefix tailTrace_1020541
  have hstable : (prefixWord ++ tailWord_1020541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020541).length < 2 ^ (prefixWord ++ tailWord_1020541).sum := by decide
  have hdescent : baseEnd_1020541 < baseStart_1020541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020548 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1020548 : Nat := 118140960795 + 1020548 * 2 ^ 59
def prefixEnd_1020548 : Nat := 4983230072969 + 3 ^ 40 * 1020548 * 2
def baseEnd_1020548 : Nat := 465805915542025186628081

theorem tailTrace_1020548 : CollatzResearch.WordTrace tailWord_1020548 prefixEnd_1020548 465805915542025186628081 := by
  unfold tailWord_1020548
  simp only [CollatzResearch.WordTrace]
  refine ⟨18611221753368183283559149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24814962337824244378078865 18611221753368183283559149)
  ·
    refine ⟨6979208157513068731334681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18611221753368183283559149 6979208157513068731334681)
    ·
      refine ⟨5234406118134801548501011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6979208157513068731334681 5234406118134801548501011)
      ·
        refine ⟨7851609177202202322751517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5234406118134801548501011 7851609177202202322751517)
        ·
          refine ⟨2944353441450825871031819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7851609177202202322751517 2944353441450825871031819)
          ·
            refine ⟨4416530162176238806547729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944353441450825871031819 4416530162176238806547729)
            ·
              refine ⟨3312397621632179104910797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416530162176238806547729 3312397621632179104910797)
              ·
                refine ⟨1242149108112067164341549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3312397621632179104910797 1242149108112067164341549)
                ·
                  refine ⟨465805915542025186628081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1242149108112067164341549 465805915542025186628081)
                  ·
                    rfl

theorem cell20_1020548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1020548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020548 prefixEnd_1020548 := by exact prefixLift 1020548
  have htrace : WordTrace (prefixWord ++ tailWord_1020548) baseStart_1020548 baseEnd_1020548 := by
    simpa [prefixWord, tailWord_1020548, baseEnd_1020548] using wordTrace_append hprefix tailTrace_1020548
  have hstable : (prefixWord ++ tailWord_1020548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020548).length < 2 ^ (prefixWord ++ tailWord_1020548).sum := by decide
  have hdescent : baseEnd_1020548 < baseStart_1020548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020572 : List Nat := [2, 2, 3, 2, 2, 1, 1, 5, 2]
def baseStart_1020572 : Nat := 118140960795 + 1020572 * 2 ^ 59
def prefixEnd_1020572 : Nat := 4983230072969 + 3 ^ 40 * 1020572 * 2
def baseEnd_1020572 : Nat := 465816869795987769827983

theorem tailTrace_1020572 : CollatzResearch.WordTrace tailWord_1020572 prefixEnd_1020572 465816869795987769827983 := by
  unfold tailWord_1020572
  simp only [CollatzResearch.WordTrace]
  refine ⟨18611659429324709332995985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24815545905766279110661313 18611659429324709332995985)
  ·
    refine ⟨13958744571993531999746989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18611659429324709332995985 13958744571993531999746989)
    ·
      refine ⟨5234529214497574499905121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13958744571993531999746989 5234529214497574499905121)
      ·
        refine ⟨3925896910873180874928841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5234529214497574499905121 3925896910873180874928841)
        ·
          refine ⟨2944422683154885656196631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3925896910873180874928841 2944422683154885656196631)
          ·
            refine ⟨4416634024732328484294947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944422683154885656196631 4416634024732328484294947)
            ·
              refine ⟨6624951037098492726442421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4416634024732328484294947 6624951037098492726442421)
              ·
                refine ⟨621089159727983693103977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6624951037098492726442421 621089159727983693103977)
                ·
                  refine ⟨465816869795987769827983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621089159727983693103977 465816869795987769827983)
                  ·
                    rfl

theorem cell20_1020572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_1020572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020572 prefixEnd_1020572 := by exact prefixLift 1020572
  have htrace : WordTrace (prefixWord ++ tailWord_1020572) baseStart_1020572 baseEnd_1020572 := by
    simpa [prefixWord, tailWord_1020572, baseEnd_1020572] using wordTrace_append hprefix tailTrace_1020572
  have hstable : (prefixWord ++ tailWord_1020572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020572).length < 2 ^ (prefixWord ++ tailWord_1020572).sum := by decide
  have hdescent : baseEnd_1020572 < baseStart_1020572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020645 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1020645 : Nat := 118140960795 + 1020645 * 2 ^ 59
def prefixEnd_1020645 : Nat := 4983230072969 + 3 ^ 40 * 1020645 * 2
def baseEnd_1020645 : Nat := 465850188985123960394351

theorem tailTrace_1020645 : CollatzResearch.WordTrace tailWord_1020645 prefixEnd_1020645 465850188985123960394351 := by
  unfold tailWord_1020645
  simp only [CollatzResearch.WordTrace]
  refine ⟨37225981387384952133399389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24817320924923301422266259 37225981387384952133399389)
  ·
    refine ⟨13959743020269357050024771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37225981387384952133399389 13959743020269357050024771)
    ·
      refine ⟨20939614530404035575037157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13959743020269357050024771 20939614530404035575037157)
      ·
        refine ⟨3926177724450756670319467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20939614530404035575037157 3926177724450756670319467)
        ·
          refine ⟨5889266586676135005479201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3926177724450756670319467 5889266586676135005479201)
          ·
            refine ⟨4416949940007101254109401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5889266586676135005479201 4416949940007101254109401)
            ·
              refine ⟨3312712455005325940582051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416949940007101254109401 3312712455005325940582051)
              ·
                refine ⟨4969068682507988910873077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312712455005325940582051 4969068682507988910873077)
                ·
                  refine ⟨465850188985123960394351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4969068682507988910873077 465850188985123960394351)
                  ·
                    rfl

theorem cell20_1020645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1020645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020645 prefixEnd_1020645 := by exact prefixLift 1020645
  have htrace : WordTrace (prefixWord ++ tailWord_1020645) baseStart_1020645 baseEnd_1020645 := by
    simpa [prefixWord, tailWord_1020645, baseEnd_1020645] using wordTrace_append hprefix tailTrace_1020645
  have hstable : (prefixWord ++ tailWord_1020645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020645).length < 2 ^ (prefixWord ++ tailWord_1020645).sum := by decide
  have hdescent : baseEnd_1020645 < baseStart_1020645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020648 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 4]
def baseStart_1020648 : Nat := 118140960795 + 1020648 * 2 ^ 59
def prefixEnd_1020648 : Nat := 4983230072969 + 3 ^ 40 * 1020648 * 2
def baseEnd_1020648 : Nat := 465851558266869283294339

theorem tailTrace_1020648 : CollatzResearch.WordTrace tailWord_1020648 prefixEnd_1020648 465851558266869283294339 := by
  unfold tailWord_1020648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18613045403187041822879299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24817393870916055763839065 18613045403187041822879299)
  ·
    refine ⟨27919568104780562734318949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18613045403187041822879299 27919568104780562734318949)
    ·
      refine ⟨5234919019646355512684803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27919568104780562734318949 5234919019646355512684803)
      ·
        refine ⟨7852378529469533269027205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5234919019646355512684803 7852378529469533269027205)
        ·
          refine ⟨1472320974275537487942601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7852378529469533269027205 1472320974275537487942601)
          ·
            refine ⟨1104240730706653115956951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472320974275537487942601 1104240730706653115956951)
            ·
              refine ⟨1656361096059979673935427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104240730706653115956951 1656361096059979673935427)
              ·
                refine ⟨2484541644089969510903141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656361096059979673935427 2484541644089969510903141)
                ·
                  refine ⟨465851558266869283294339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2484541644089969510903141 465851558266869283294339)
                  ·
                    rfl

theorem cell20_1020648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_1020648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020648 prefixEnd_1020648 := by exact prefixLift 1020648
  have htrace : WordTrace (prefixWord ++ tailWord_1020648) baseStart_1020648 baseEnd_1020648 := by
    simpa [prefixWord, tailWord_1020648, baseEnd_1020648] using wordTrace_append hprefix tailTrace_1020648
  have hstable : (prefixWord ++ tailWord_1020648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020648).length < 2 ^ (prefixWord ++ tailWord_1020648).sum := by decide
  have hdescent : baseEnd_1020648 < baseStart_1020648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020662 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1020662 : Nat := 118140960795 + 1020662 * 2 ^ 59
def prefixEnd_1020662 : Nat := 4983230072969 + 3 ^ 40 * 1020662 * 2
def baseEnd_1020662 : Nat := 465857948248347456827615

theorem tailTrace_1020662 : CollatzResearch.WordTrace tailWord_1020662 prefixEnd_1020662 465857948248347456827615 := by
  unfold tailWord_1020662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2326662589270210252298015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24817734285548909357845493 2326662589270210252298015)
  ·
    refine ⟨3489993883905315378447023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2326662589270210252298015 3489993883905315378447023)
    ·
      refine ⟨5234990825857973067670535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3489993883905315378447023 5234990825857973067670535)
      ·
        refine ⟨7852486238786959601505803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5234990825857973067670535 7852486238786959601505803)
        ·
          refine ⟨11778729358180439402258705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852486238786959601505803 11778729358180439402258705)
          ·
            refine ⟨8834047018635329551694029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11778729358180439402258705 8834047018635329551694029)
            ·
              refine ⟨3312767631988248581885261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8834047018635329551694029 3312767631988248581885261)
              ·
                refine ⟨1242287861995593218206973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3312767631988248581885261 1242287861995593218206973)
                ·
                  refine ⟨465857948248347456827615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1242287861995593218206973 465857948248347456827615)
                  ·
                    rfl

theorem cell20_1020662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1020662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020662 prefixEnd_1020662 := by exact prefixLift 1020662
  have htrace : WordTrace (prefixWord ++ tailWord_1020662) baseStart_1020662 baseEnd_1020662 := by
    simpa [prefixWord, tailWord_1020662, baseEnd_1020662] using wordTrace_append hprefix tailTrace_1020662
  have hstable : (prefixWord ++ tailWord_1020662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020662).length < 2 ^ (prefixWord ++ tailWord_1020662).sum := by decide
  have hdescent : baseEnd_1020662 < baseStart_1020662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020700 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 3]
def baseStart_1020700 : Nat := 118140960795 + 1020700 * 2 ^ 59
def prefixEnd_1020700 : Nat := 4983230072969 + 3 ^ 40 * 1020700 * 2
def baseEnd_1020700 : Nat := 465875292483788213560793

theorem tailTrace_1020700 : CollatzResearch.WordTrace tailWord_1020700 prefixEnd_1020700 465875292483788213560793 := by
  unfold tailWord_1020700
  simp only [CollatzResearch.WordTrace]
  refine ⟨18613993701092848263325777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24818658268123797684434369 18613993701092848263325777)
  ·
    refine ⟨13960495275819636197494333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18613993701092848263325777 13960495275819636197494333)
    ·
      refine ⟨5235185728432363574060375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13960495275819636197494333 5235185728432363574060375)
      ·
        refine ⟨7852778592648545361090563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5235185728432363574060375 7852778592648545361090563)
        ·
          refine ⟨11779167888972818041635845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852778592648545361090563 11779167888972818041635845)
          ·
            refine ⟨2208593979182403382806721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11779167888972818041635845 2208593979182403382806721)
            ·
              refine ⟨1656445484386802537105041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2208593979182403382806721 1656445484386802537105041)
              ·
                refine ⟨1242334113290101902828781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1656445484386802537105041 1242334113290101902828781)
                ·
                  refine ⟨465875292483788213560793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1242334113290101902828781 465875292483788213560793)
                  ·
                    rfl

theorem cell20_1020700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_1020700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020700 prefixEnd_1020700 := by exact prefixLift 1020700
  have htrace : WordTrace (prefixWord ++ tailWord_1020700) baseStart_1020700 baseEnd_1020700 := by
    simpa [prefixWord, tailWord_1020700, baseEnd_1020700] using wordTrace_append hprefix tailTrace_1020700
  have hstable : (prefixWord ++ tailWord_1020700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020700).length < 2 ^ (prefixWord ++ tailWord_1020700).sum := by decide
  have hdescent : baseEnd_1020700 < baseStart_1020700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020703 : List Nat := [1, 1, 2, 4, 2, 4, 2, 2, 2]
def baseStart_1020703 : Nat := 118140960795 + 1020703 * 2 ^ 59
def prefixEnd_1020703 : Nat := 4983230072969 + 3 ^ 40 * 1020703 * 2
def baseEnd_1020703 : Nat := 465876661765533536460781

theorem tailTrace_1020703 : CollatzResearch.WordTrace tailWord_1020703 prefixEnd_1020703 465876661765533536460781 := by
  unfold tailWord_1020703
  simp only [CollatzResearch.WordTrace]
  refine ⟨37228096821174828039010763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24818731214116552026007175 37228096821174828039010763)
  ·
    refine ⟨55842145231762242058516145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37228096821174828039010763 55842145231762242058516145)
    ·
      refine ⟨41881608923821681543887109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55842145231762242058516145 41881608923821681543887109)
      ·
        refine ⟨7852801673216565289478833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41881608923821681543887109 7852801673216565289478833)
        ·
          refine ⟨5889601254912423967109125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7852801673216565289478833 5889601254912423967109125)
          ·
            refine ⟨1104300235296079493832961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5889601254912423967109125 1104300235296079493832961)
            ·
              refine ⟨828225176472059620374721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104300235296079493832961 828225176472059620374721)
              ·
                refine ⟨621168882354044715281041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828225176472059620374721 621168882354044715281041)
                ·
                  refine ⟨465876661765533536460781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621168882354044715281041 465876661765533536460781)
                  ·
                    rfl

theorem cell20_1020703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 2].length) (baseStart_1020703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020703 prefixEnd_1020703 := by exact prefixLift 1020703
  have htrace : WordTrace (prefixWord ++ tailWord_1020703) baseStart_1020703 baseEnd_1020703 := by
    simpa [prefixWord, tailWord_1020703, baseEnd_1020703] using wordTrace_append hprefix tailTrace_1020703
  have hstable : (prefixWord ++ tailWord_1020703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020703).length < 2 ^ (prefixWord ++ tailWord_1020703).sum := by decide
  have hdescent : baseEnd_1020703 < baseStart_1020703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020721 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 3]
def baseStart_1020721 : Nat := 118140960795 + 1020721 * 2 ^ 59
def prefixEnd_1020721 : Nat := 4983230072969 + 3 ^ 40 * 1020721 * 2
def baseEnd_1020721 : Nat := 465884877456005473860707

theorem tailTrace_1020721 : CollatzResearch.WordTrace tailWord_1020721 prefixEnd_1020721 465884877456005473860707 := by
  unfold tailWord_1020721
  simp only [CollatzResearch.WordTrace]
  refine ⟨37228753335109617113166017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24819168890073078075444011 37228753335109617113166017)
  ·
    refine ⟨27921565001332212834874513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37228753335109617113166017 27921565001332212834874513)
    ·
      refine ⟨20941173750999159626155885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27921565001332212834874513 20941173750999159626155885)
      ·
        refine ⟨7852940156624684859808457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20941173750999159626155885 7852940156624684859808457)
        ·
          refine ⟨5889705117468513644856343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7852940156624684859808457 5889705117468513644856343)
          ·
            refine ⟨8834557676202770467284515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889705117468513644856343 8834557676202770467284515)
            ·
              refine ⟨13251836514304155700926773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834557676202770467284515 13251836514304155700926773)
              ·
                refine ⟨1242359673216014596961885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13251836514304155700926773 1242359673216014596961885)
                ·
                  refine ⟨465884877456005473860707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1242359673216014596961885 465884877456005473860707)
                  ·
                    rfl

theorem cell20_1020721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_1020721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020721 prefixEnd_1020721 := by exact prefixLift 1020721
  have htrace : WordTrace (prefixWord ++ tailWord_1020721) baseStart_1020721 baseEnd_1020721 := by
    simpa [prefixWord, tailWord_1020721, baseEnd_1020721] using wordTrace_append hprefix tailTrace_1020721
  have hstable : (prefixWord ++ tailWord_1020721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020721).length < 2 ^ (prefixWord ++ tailWord_1020721).sum := by decide
  have hdescent : baseEnd_1020721 < baseStart_1020721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020724 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1020724 : Nat := 118140960795 + 1020724 * 2 ^ 59
def prefixEnd_1020724 : Nat := 4983230072969 + 3 ^ 40 * 1020724 * 2
def baseEnd_1020724 : Nat := 465886246737750796760695

theorem tailTrace_1020724 : CollatzResearch.WordTrace tailWord_1020724 prefixEnd_1020724 465886246737750796760695 := by
  unfold tailWord_1020724
  simp only [CollatzResearch.WordTrace]
  refine ⟨18614431377049374312762613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24819241836065832417016817 18614431377049374312762613)
  ·
    refine ⟨1745102941598378841821495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18614431377049374312762613 1745102941598378841821495)
    ·
      refine ⟨2617654412397568262732243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745102941598378841821495 2617654412397568262732243)
      ·
        refine ⟨3926481618596352394098365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617654412397568262732243 3926481618596352394098365)
        ·
          refine ⟨1472430606973632147786887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3926481618596352394098365 1472430606973632147786887)
          ·
            refine ⟨2208645910460448221680331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472430606973632147786887 2208645910460448221680331)
            ·
              refine ⟨3312968865690672332520497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208645910460448221680331 3312968865690672332520497)
              ·
                refine ⟨2484726649268004249390373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312968865690672332520497 2484726649268004249390373)
                ·
                  refine ⟨465886246737750796760695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2484726649268004249390373 465886246737750796760695)
                  ·
                    rfl

theorem cell20_1020724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1020724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020724 prefixEnd_1020724 := by exact prefixLift 1020724
  have htrace : WordTrace (prefixWord ++ tailWord_1020724) baseStart_1020724 baseEnd_1020724 := by
    simpa [prefixWord, tailWord_1020724, baseEnd_1020724] using wordTrace_append hprefix tailTrace_1020724
  have hstable : (prefixWord ++ tailWord_1020724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020724).length < 2 ^ (prefixWord ++ tailWord_1020724).sum := by decide
  have hdescent : baseEnd_1020724 < baseStart_1020724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020728 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_1020728 : Nat := 118140960795 + 1020728 * 2 ^ 59
def prefixEnd_1020728 : Nat := 4983230072969 + 3 ^ 40 * 1020728 * 2
def baseEnd_1020728 : Nat := 465888072446744560627345

theorem tailTrace_1020728 : CollatzResearch.WordTrace tailWord_1020728 prefixEnd_1020728 465888072446744560627345 := by
  unfold tailWord_1020728
  simp only [CollatzResearch.WordTrace]
  refine ⟨18614504323042128654335419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24819339097389504872447225 18614504323042128654335419)
  ·
    refine ⟨27921756484563192981503129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18614504323042128654335419 27921756484563192981503129)
    ·
      refine ⟨20941317363422394736127347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27921756484563192981503129 20941317363422394736127347)
      ·
        refine ⟨31411976045133592104191021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20941317363422394736127347 31411976045133592104191021)
        ·
          refine ⟨11779491016925097039071633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31411976045133592104191021 11779491016925097039071633)
          ·
            refine ⟨8834618262693822779303725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11779491016925097039071633 8834618262693822779303725)
            ·
              refine ⟨3312981848510183542238897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8834618262693822779303725 3312981848510183542238897)
              ·
                refine ⟨2484736386382637656679173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312981848510183542238897 2484736386382637656679173)
                ·
                  refine ⟨465888072446744560627345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2484736386382637656679173 465888072446744560627345)
                  ·
                    rfl

theorem cell20_1020728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_1020728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020728 prefixEnd_1020728 := by exact prefixLift 1020728
  have htrace : WordTrace (prefixWord ++ tailWord_1020728) baseStart_1020728 baseEnd_1020728 := by
    simpa [prefixWord, tailWord_1020728, baseEnd_1020728] using wordTrace_append hprefix tailTrace_1020728
  have hstable : (prefixWord ++ tailWord_1020728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020728).length < 2 ^ (prefixWord ++ tailWord_1020728).sum := by decide
  have hdescent : baseEnd_1020728 < baseStart_1020728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020745 : List Nat := [1, 2, 1, 1, 2, 5, 1, 5, 2]
def baseStart_1020745 : Nat := 118140960795 + 1020745 * 2 ^ 59
def prefixEnd_1020745 : Nat := 4983230072969 + 3 ^ 40 * 1020745 * 2
def baseEnd_1020745 : Nat := 465895831709968057060609

theorem tailTrace_1020745 : CollatzResearch.WordTrace tailWord_1020745 prefixEnd_1020745 465895831709968057060609 := by
  unfold tailWord_1020745
  simp only [CollatzResearch.WordTrace]
  refine ⟨37229628687022669212039689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24819752458015112808026459 37229628687022669212039689)
  ·
    refine ⟨27922221515267001909029767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37229628687022669212039689 27922221515267001909029767)
    ·
      refine ⟨41883332272900502863544651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27922221515267001909029767 41883332272900502863544651)
      ·
        refine ⟨62824998409350754295316977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41883332272900502863544651 62824998409350754295316977)
        ·
          refine ⟨47118748807013065721487733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62824998409350754295316977 47118748807013065721487733)
          ·
            refine ⟨4417382700657474911389475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47118748807013065721487733 4417382700657474911389475)
            ·
              refine ⟨6626074050986212367084213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417382700657474911389475 6626074050986212367084213)
              ·
                refine ⟨621194442279957409414145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6626074050986212367084213 621194442279957409414145)
                ·
                  refine ⟨465895831709968057060609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621194442279957409414145 465895831709968057060609)
                  ·
                    rfl

theorem cell20_1020745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_1020745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020745 prefixEnd_1020745 := by exact prefixLift 1020745
  have htrace : WordTrace (prefixWord ++ tailWord_1020745) baseStart_1020745 baseEnd_1020745 := by
    simpa [prefixWord, tailWord_1020745, baseEnd_1020745] using wordTrace_append hprefix tailTrace_1020745
  have hstable : (prefixWord ++ tailWord_1020745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020745).length < 2 ^ (prefixWord ++ tailWord_1020745).sum := by decide
  have hdescent : baseEnd_1020745 < baseStart_1020745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020759 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 5]
def baseStart_1020759 : Nat := 118140960795 + 1020759 * 2 ^ 59
def prefixEnd_1020759 : Nat := 4983230072969 + 3 ^ 40 * 1020759 * 2
def baseEnd_1020759 : Nat := 465902221691446230593885

theorem tailTrace_1020759 : CollatzResearch.WordTrace tailWord_1020759 prefixEnd_1020759 465902221691446230593885 := by
  unfold tailWord_1020759
  simp only [CollatzResearch.WordTrace]
  refine ⟨37230139308971949603049331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24820092872647966402032887 37230139308971949603049331)
  ·
    refine ⟨55845208963457924404573997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37230139308971949603049331 55845208963457924404573997)
    ·
      refine ⟨20941953361296721651715249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55845208963457924404573997 20941953361296721651715249)
      ·
        refine ⟨15706465020972541238786437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20941953361296721651715249 15706465020972541238786437)
        ·
          refine ⟨2944962191432351482272457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15706465020972541238786437 2944962191432351482272457)
          ·
            refine ⟨2208721643574263611704343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2944962191432351482272457 2208721643574263611704343)
            ·
              refine ⟨3313082465361395417556515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208721643574263611704343 3313082465361395417556515)
              ·
                refine ⟨4969623698042093126334773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313082465361395417556515 4969623698042093126334773)
                ·
                  refine ⟨465902221691446230593885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4969623698042093126334773 465902221691446230593885)
                  ·
                    rfl

theorem cell20_1020759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_1020759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020759 prefixEnd_1020759 := by exact prefixLift 1020759
  have htrace : WordTrace (prefixWord ++ tailWord_1020759) baseStart_1020759 baseEnd_1020759 := by
    simpa [prefixWord, tailWord_1020759, baseEnd_1020759] using wordTrace_append hprefix tailTrace_1020759
  have hstable : (prefixWord ++ tailWord_1020759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020759).length < 2 ^ (prefixWord ++ tailWord_1020759).sum := by decide
  have hdescent : baseEnd_1020759 < baseStart_1020759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020821 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 4]
def baseStart_1020821 : Nat := 118140960795 + 1020821 * 2 ^ 59
def prefixEnd_1020821 : Nat := 4983230072969 + 3 ^ 40 * 1020821 * 2
def baseEnd_1020821 : Nat := 465930520180849570526965

theorem tailTrace_1020821 : CollatzResearch.WordTrace tailWord_1020821 prefixEnd_1020821 465930520180849570526965 := by
  unfold tailWord_1020821
  simp only [CollatzResearch.WordTrace]
  refine ⟨37232400634747334191806317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24821600423164889461204211 37232400634747334191806317)
  ·
    refine ⟨13962150238030250321927369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37232400634747334191806317 13962150238030250321927369)
    ·
      refine ⟨10471612678522687741445527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13962150238030250321927369 10471612678522687741445527)
      ·
        refine ⟨15707419017784031612168291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10471612678522687741445527 15707419017784031612168291)
        ·
          refine ⟨23561128526676047418252437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15707419017784031612168291 23561128526676047418252437)
          ·
            refine ⟨1104427899687939722730583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23561128526676047418252437 1104427899687939722730583)
            ·
              refine ⟨1656641849531909584095875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104427899687939722730583 1656641849531909584095875)
              ·
                refine ⟨2484962774297864376143813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656641849531909584095875 2484962774297864376143813)
                ·
                  refine ⟨465930520180849570526965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2484962774297864376143813 465930520180849570526965)
                  ·
                    rfl

theorem cell20_1020821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_1020821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020821 prefixEnd_1020821 := by exact prefixLift 1020821
  have htrace : WordTrace (prefixWord ++ tailWord_1020821) baseStart_1020821 baseEnd_1020821 := by
    simpa [prefixWord, tailWord_1020821, baseEnd_1020821] using wordTrace_append hprefix tailTrace_1020821
  have hstable : (prefixWord ++ tailWord_1020821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020821).length < 2 ^ (prefixWord ++ tailWord_1020821).sum := by decide
  have hdescent : baseEnd_1020821 < baseStart_1020821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020831 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 3]
def baseStart_1020831 : Nat := 118140960795 + 1020831 * 2 ^ 59
def prefixEnd_1020831 : Nat := 4983230072969 + 3 ^ 40 * 1020831 * 2
def baseEnd_1020831 : Nat := 465935084453333980193591

theorem tailTrace_1020831 : CollatzResearch.WordTrace tailWord_1020831 prefixEnd_1020831 465935084453333980193591 := by
  unfold tailWord_1020831
  simp only [CollatzResearch.WordTrace]
  refine ⟨37232765364711105899670347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24821843576474070599780231 37232765364711105899670347)
  ·
    refine ⟨55849148047066658849505521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37232765364711105899670347 55849148047066658849505521)
    ·
      refine ⟨41886861035299994137129141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55849148047066658849505521 41886861035299994137129141)
      ·
        refine ⟨3926893222059374450355857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41886861035299994137129141 3926893222059374450355857)
        ·
          refine ⟨2945169916544530837766893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3926893222059374450355857 2945169916544530837766893)
          ·
            refine ⟨1104438718704199064162585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2945169916544530837766893 1104438718704199064162585)
            ·
              refine ⟨828329039028149298121939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104438718704199064162585 828329039028149298121939)
              ·
                refine ⟨1242493558542223947182909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828329039028149298121939 1242493558542223947182909)
                ·
                  refine ⟨465935084453333980193591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1242493558542223947182909 465935084453333980193591)
                  ·
                    rfl

theorem cell20_1020831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 3].length) (baseStart_1020831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020831 prefixEnd_1020831 := by exact prefixLift 1020831
  have htrace : WordTrace (prefixWord ++ tailWord_1020831) baseStart_1020831 baseEnd_1020831 := by
    simpa [prefixWord, tailWord_1020831, baseEnd_1020831] using wordTrace_append hprefix tailTrace_1020831
  have hstable : (prefixWord ++ tailWord_1020831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020831).length < 2 ^ (prefixWord ++ tailWord_1020831).sum := by decide
  have hdescent : baseEnd_1020831 < baseStart_1020831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020863 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_1020863 : Nat := 118140960795 + 1020863 * 2 ^ 59
def prefixEnd_1020863 : Nat := 4983230072969 + 3 ^ 40 * 1020863 * 2
def baseEnd_1020863 : Nat := 465949690125284091126793

theorem tailTrace_1020863 : CollatzResearch.WordTrace tailWord_1020863 prefixEnd_1020863 465949690125284091126793 := by
  unfold tailWord_1020863
  simp only [CollatzResearch.WordTrace]
  refine ⟨37233932500595175364835243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24822621667063450243223495 37233932500595175364835243)
  ·
    refine ⟨55850898750892763047252865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37233932500595175364835243 55850898750892763047252865)
    ·
      refine ⟨41888174063169572285439649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55850898750892763047252865 41888174063169572285439649)
      ·
        refine ⟨31416130547377179214079737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41888174063169572285439649 31416130547377179214079737)
        ·
          refine ⟨23562097910532884410559803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31416130547377179214079737 23562097910532884410559803)
          ·
            refine ⟨35343146865799326615839705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23562097910532884410559803 35343146865799326615839705)
            ·
              refine ⟨26507360149349494961879779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35343146865799326615839705 26507360149349494961879779)
              ·
                refine ⟨39761040224024242442819669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26507360149349494961879779 39761040224024242442819669)
                ·
                  refine ⟨465949690125284091126793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39761040224024242442819669 465949690125284091126793)
                  ·
                    rfl

theorem cell20_1020863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_1020863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020863 prefixEnd_1020863 := by exact prefixLift 1020863
  have htrace : WordTrace (prefixWord ++ tailWord_1020863) baseStart_1020863 baseEnd_1020863 := by
    simpa [prefixWord, tailWord_1020863, baseEnd_1020863] using wordTrace_append hprefix tailTrace_1020863
  have hstable : (prefixWord ++ tailWord_1020863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020863).length < 2 ^ (prefixWord ++ tailWord_1020863).sum := by decide
  have hdescent : baseEnd_1020863 < baseStart_1020863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020872 : List Nat := [2, 1, 3, 1, 6, 1, 2, 2, 2]
def baseStart_1020872 : Nat := 118140960795 + 1020872 * 2 ^ 59
def prefixEnd_1020872 : Nat := 4983230072969 + 3 ^ 40 * 1020872 * 2
def baseEnd_1020872 : Nat := 465953797970520059826757

theorem tailTrace_1020872 : CollatzResearch.WordTrace tailWord_1020872 prefixEnd_1020872 465953797970520059826757 := by
  unfold tailWord_1020872
  simp only [CollatzResearch.WordTrace]
  refine ⟨18617130378781284950956435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24822840505041713267941913 18617130378781284950956435)
  ·
    refine ⟨27925695568171927426434653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18617130378781284950956435 27925695568171927426434653)
    ·
      refine ⟨10472135838064472784912995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27925695568171927426434653 10472135838064472784912995)
      ·
        refine ⟨15708203757096709177369493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10472135838064472784912995 15708203757096709177369493)
        ·
          refine ⟨736322051113908242689195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15708203757096709177369493 736322051113908242689195)
          ·
            refine ⟨1104483076670862364033793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736322051113908242689195 1104483076670862364033793)
            ·
              refine ⟨828362307503146773025345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104483076670862364033793 828362307503146773025345)
              ·
                refine ⟨621271730627360079769009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828362307503146773025345 621271730627360079769009)
                ·
                  refine ⟨465953797970520059826757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621271730627360079769009 465953797970520059826757)
                  ·
                    rfl

theorem cell20_1020872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_1020872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020872 prefixEnd_1020872 := by exact prefixLift 1020872
  have htrace : WordTrace (prefixWord ++ tailWord_1020872) baseStart_1020872 baseEnd_1020872 := by
    simpa [prefixWord, tailWord_1020872, baseEnd_1020872] using wordTrace_append hprefix tailTrace_1020872
  have hstable : (prefixWord ++ tailWord_1020872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020872).length < 2 ^ (prefixWord ++ tailWord_1020872).sum := by decide
  have hdescent : baseEnd_1020872 < baseStart_1020872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020935 : List Nat := [1, 1, 4, 3, 1, 1, 1, 6, 2]
def baseStart_1020935 : Nat := 118140960795 + 1020935 * 2 ^ 59
def prefixEnd_1020935 : Nat := 4983230072969 + 3 ^ 40 * 1020935 * 2
def baseEnd_1020935 : Nat := 465982552887171840726499

theorem tailTrace_1020935 : CollatzResearch.WordTrace tailWord_1020935 prefixEnd_1020935 465982552887171840726499 := by
  unfold tailWord_1020935
  simp only [CollatzResearch.WordTrace]
  refine ⟨37236558556334331661456259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24824372370889554440970839 37236558556334331661456259)
  ·
    refine ⟨55854837834501497492184389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37236558556334331661456259 55854837834501497492184389)
    ·
      refine ⟨10472782093969030779784573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55854837834501497492184389 10472782093969030779784573)
      ·
        refine ⟨3927293285238386542419215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10472782093969030779784573 3927293285238386542419215)
        ·
          refine ⟨5890939927857579813628823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927293285238386542419215 5890939927857579813628823)
          ·
            refine ⟨8836409891786369720443235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890939927857579813628823 8836409891786369720443235)
            ·
              refine ⟨13254614837679554580664853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8836409891786369720443235 13254614837679554580664853)
              ·
                refine ⟨621310070516229120968665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13254614837679554580664853 621310070516229120968665)
                ·
                  refine ⟨465982552887171840726499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621310070516229120968665 465982552887171840726499)
                  ·
                    rfl

theorem cell20_1020935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 2].length) (baseStart_1020935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020935 prefixEnd_1020935 := by exact prefixLift 1020935
  have htrace : WordTrace (prefixWord ++ tailWord_1020935) baseStart_1020935 baseEnd_1020935 := by
    simpa [prefixWord, tailWord_1020935, baseEnd_1020935] using wordTrace_append hprefix tailTrace_1020935
  have hstable : (prefixWord ++ tailWord_1020935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020935).length < 2 ^ (prefixWord ++ tailWord_1020935).sum := by decide
  have hdescent : baseEnd_1020935 < baseStart_1020935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020963 : List Nat := [1, 1, 1, 4, 3, 3, 1, 6]
def baseStart_1020963 : Nat := 118140960795 + 1020963 * 2 ^ 59
def prefixEnd_1020963 : Nat := 4983230072969 + 3 ^ 40 * 1020963 * 2
def baseEnd_1020963 : Nat := 155331777616709395931017

theorem tailTrace_1020963 : CollatzResearch.WordTrace tailWord_1020963 prefixEnd_1020963 155331777616709395931017 := by
  unfold tailWord_1020963
  simp only [CollatzResearch.WordTrace]
  refine ⟨37237579800232892443475543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24825053200155261628983695 37237579800232892443475543)
  ·
    refine ⟨55856369700349338665213315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37237579800232892443475543 55856369700349338665213315)
    ·
      refine ⟨83784554550524007997819973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55856369700349338665213315 83784554550524007997819973)
      ·
        refine ⟨15709603978223251499591245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83784554550524007997819973 15709603978223251499591245)
        ·
          refine ⟨5891101491833719312346717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15709603978223251499591245 5891101491833719312346717)
          ·
            refine ⟨2209163059437644742130019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5891101491833719312346717 2209163059437644742130019)
            ·
              refine ⟨3313744589156467113195029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2209163059437644742130019 3313744589156467113195029)
              ·
                refine ⟨155331777616709395931017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3313744589156467113195029 155331777616709395931017)
                ·
                  rfl

theorem cell20_1020963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_1020963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020963 prefixEnd_1020963 := by exact prefixLift 1020963
  have htrace : WordTrace (prefixWord ++ tailWord_1020963) baseStart_1020963 baseEnd_1020963 := by
    simpa [prefixWord, tailWord_1020963, baseEnd_1020963] using wordTrace_append hprefix tailTrace_1020963
  have hstable : (prefixWord ++ tailWord_1020963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020963).length < 2 ^ (prefixWord ++ tailWord_1020963).sum := by decide
  have hdescent : baseEnd_1020963 < baseStart_1020963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020980 : List Nat := [2, 5, 1, 2, 1, 1, 8]
def baseStart_1020980 : Nat := 118140960795 + 1020980 * 2 ^ 59
def prefixEnd_1020980 : Nat := 4983230072969 + 3 ^ 40 * 1020980 * 2
def baseEnd_1020980 : Nat := 51778121345927964914035

theorem tailTrace_1020980 : CollatzResearch.WordTrace tailWord_1020980 prefixEnd_1020980 51778121345927964914035 := by
  unfold tailWord_1020980
  simp only [CollatzResearch.WordTrace]
  refine ⟨18619099920585652173422197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24825466560780869564562929 18619099920585652173422197)
  ·
    refine ⟨1745540617554904891258331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18619099920585652173422197 1745540617554904891258331)
    ·
      refine ⟨2618310926332357336887497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745540617554904891258331 2618310926332357336887497)
      ·
        refine ⟨1963733194749268002665623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2618310926332357336887497 1963733194749268002665623)
        ·
          refine ⟨2945599792123902003998435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963733194749268002665623 2945599792123902003998435)
          ·
            refine ⟨4418399688185853005997653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945599792123902003998435 4418399688185853005997653)
            ·
              refine ⟨51778121345927964914035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4418399688185853005997653 51778121345927964914035)
              ·
                rfl

theorem cell20_1020980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 8].length) (baseStart_1020980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020980 prefixEnd_1020980 := by exact prefixLift 1020980
  have htrace : WordTrace (prefixWord ++ tailWord_1020980) baseStart_1020980 baseEnd_1020980 := by
    simpa [prefixWord, tailWord_1020980, baseEnd_1020980] using wordTrace_append hprefix tailTrace_1020980
  have hstable : (prefixWord ++ tailWord_1020980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020980).length < 2 ^ (prefixWord ++ tailWord_1020980).sum := by decide
  have hdescent : baseEnd_1020980 < baseStart_1020980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020990 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1020990 : Nat := 118140960795 + 1020990 * 2 ^ 59
def prefixEnd_1020990 : Nat := 4983230072969 + 3 ^ 40 * 1020990 * 2
def baseEnd_1020990 : Nat := 466007656385836093892941

theorem tailTrace_1020990 : CollatzResearch.WordTrace tailWord_1020990 prefixEnd_1020990 466007656385836093892941 := by
  unfold tailWord_1020990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4654820571391884506838553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24825709714090050703138949 4654820571391884506838553)
  ·
    refine ⟨3491115428543913380128915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4654820571391884506838553 3491115428543913380128915)
    ·
      refine ⟨5236673142815870070193373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491115428543913380128915 5236673142815870070193373)
      ·
        refine ⟨1963752428555951276322515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5236673142815870070193373 1963752428555951276322515)
        ·
          refine ⟨2945628642833926914483773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963752428555951276322515 2945628642833926914483773)
          ·
            refine ⟨1104610741062722592931415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2945628642833926914483773 1104610741062722592931415)
            ·
              refine ⟨1656916111594083889397123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104610741062722592931415 1656916111594083889397123)
              ·
                refine ⟨2485374167391125834095685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656916111594083889397123 2485374167391125834095685)
                ·
                  refine ⟨466007656385836093892941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2485374167391125834095685 466007656385836093892941)
                  ·
                    rfl

theorem cell20_1020990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1020990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1020990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1020990 prefixEnd_1020990 := by exact prefixLift 1020990
  have htrace : WordTrace (prefixWord ++ tailWord_1020990) baseStart_1020990 baseEnd_1020990 := by
    simpa [prefixWord, tailWord_1020990, baseEnd_1020990] using wordTrace_append hprefix tailTrace_1020990
  have hstable : (prefixWord ++ tailWord_1020990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020990).length < 2 ^ (prefixWord ++ tailWord_1020990).sum := by decide
  have hdescent : baseEnd_1020990 < baseStart_1020990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021015 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_1021015 : Nat := 118140960795 + 1021015 * 2 ^ 59
def prefixEnd_1021015 : Nat := 4983230072969 + 3 ^ 40 * 1021015 * 2
def baseEnd_1021015 : Nat := 466019067067047118059505

theorem tailTrace_1021015 : CollatzResearch.WordTrace tailWord_1021015 prefixEnd_1021015 466019067067047118059505 := by
  unfold tailWord_1021015
  simp only [CollatzResearch.WordTrace]
  refine ⟨37239476396044505324368499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24826317597363003549578999 37239476396044505324368499)
  ·
    refine ⟨55859214594066757986552749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37239476396044505324368499 55859214594066757986552749)
    ·
      refine ⟨20947205472775034244957281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55859214594066757986552749 20947205472775034244957281)
      ·
        refine ⟨15710404104581275683717961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20947205472775034244957281 15710404104581275683717961)
        ·
          refine ⟨11782803078435956762788471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15710404104581275683717961 11782803078435956762788471)
          ·
            refine ⟨17674204617653935144182707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11782803078435956762788471 17674204617653935144182707)
            ·
              refine ⟨26511306926480902716274061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17674204617653935144182707 26511306926480902716274061)
              ·
                refine ⟨9941740097430338518602773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26511306926480902716274061 9941740097430338518602773)
                ·
                  refine ⟨466019067067047118059505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9941740097430338518602773 466019067067047118059505)
                  ·
                    rfl

theorem cell20_1021015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_1021015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021015 prefixEnd_1021015 := by exact prefixLift 1021015
  have htrace : WordTrace (prefixWord ++ tailWord_1021015) baseStart_1021015 baseEnd_1021015 := by
    simpa [prefixWord, tailWord_1021015, baseEnd_1021015] using wordTrace_append hprefix tailTrace_1021015
  have hstable : (prefixWord ++ tailWord_1021015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021015).length < 2 ^ (prefixWord ++ tailWord_1021015).sum := by decide
  have hdescent : baseEnd_1021015 < baseStart_1021015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021045 : List Nat := [1, 3, 4, 3, 1, 1, 1, 4, 2]
def baseStart_1021045 : Nat := 118140960795 + 1021045 * 2 ^ 59
def prefixEnd_1021045 : Nat := 4983230072969 + 3 ^ 40 * 1021045 * 2
def baseEnd_1021045 : Nat := 466032759884500347059383

theorem tailTrace_1021045 : CollatzResearch.WordTrace tailWord_1021045 prefixEnd_1021045 466032759884500347059383 := by
  unfold tailWord_1021045
  simp only [CollatzResearch.WordTrace]
  refine ⟨37240570585935820447960589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24827047057290546965307059 37240570585935820447960589)
  ·
    refine ⟨13965213969725932667985221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37240570585935820447960589 13965213969725932667985221)
    ·
      refine ⟨2618477619323612375247229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13965213969725932667985221 2618477619323612375247229)
      ·
        refine ⟨981929107246354640717711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2618477619323612375247229 981929107246354640717711)
        ·
          refine ⟨1472893660869531961076567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981929107246354640717711 1472893660869531961076567)
          ·
            refine ⟨2209340491304297941614851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472893660869531961076567 2209340491304297941614851)
            ·
              refine ⟨3314010736956446912422277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2209340491304297941614851 3314010736956446912422277)
              ·
                refine ⟨621377013179333796079177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3314010736956446912422277 621377013179333796079177)
                ·
                  refine ⟨466032759884500347059383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621377013179333796079177 466032759884500347059383)
                  ·
                    rfl

theorem cell20_1021045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_1021045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021045 prefixEnd_1021045 := by exact prefixLift 1021045
  have htrace : WordTrace (prefixWord ++ tailWord_1021045) baseStart_1021045 baseEnd_1021045 := by
    simpa [prefixWord, tailWord_1021045, baseEnd_1021045] using wordTrace_append hprefix tailTrace_1021045
  have hstable : (prefixWord ++ tailWord_1021045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021045).length < 2 ^ (prefixWord ++ tailWord_1021045).sum := by decide
  have hdescent : baseEnd_1021045 < baseStart_1021045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021070 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1021070 : Nat := 118140960795 + 1021070 * 2 ^ 59
def prefixEnd_1021070 : Nat := 4983230072969 + 3 ^ 40 * 1021070 * 2
def baseEnd_1021070 : Nat := 466044170565711371225947

theorem tailTrace_1021070 : CollatzResearch.WordTrace tailWord_1021070 prefixEnd_1021070 466044170565711371225947 := by
  unfold tailWord_1021070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4655185301355656214702583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24827654940563499811747109 4655185301355656214702583)
  ·
    refine ⟨6982777952033484322053875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4655185301355656214702583 6982777952033484322053875)
    ·
      refine ⟨10474166928050226483080813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6982777952033484322053875 10474166928050226483080813)
      ·
        refine ⟨3927812598018834931155305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10474166928050226483080813 3927812598018834931155305)
        ·
          refine ⟨2945859448514126198366479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3927812598018834931155305 2945859448514126198366479)
          ·
            refine ⟨4418789172771189297549719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945859448514126198366479 4418789172771189297549719)
            ·
              refine ⟨6628183759156783946324579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418789172771189297549719 6628183759156783946324579)
              ·
                refine ⟨9942275638735175919486869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6628183759156783946324579 9942275638735175919486869)
                ·
                  refine ⟨466044170565711371225947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9942275638735175919486869 466044170565711371225947)
                  ·
                    rfl

theorem cell20_1021070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1021070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021070 prefixEnd_1021070 := by exact prefixLift 1021070
  have htrace : WordTrace (prefixWord ++ tailWord_1021070) baseStart_1021070 baseEnd_1021070 := by
    simpa [prefixWord, tailWord_1021070, baseEnd_1021070] using wordTrace_append hprefix tailTrace_1021070
  have hstable : (prefixWord ++ tailWord_1021070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021070).length < 2 ^ (prefixWord ++ tailWord_1021070).sum := by decide
  have hdescent : baseEnd_1021070 < baseStart_1021070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021149 : List Nat := [1, 4, 3, 2, 3, 1, 6]
def baseStart_1021149 : Nat := 118140960795 + 1021149 * 2 ^ 59
def prefixEnd_1021149 : Nat := 4983230072969 + 3 ^ 40 * 1021149 * 2
def baseEnd_1021149 : Nat := 51786692035370911954699

theorem tailTrace_1021149 : CollatzResearch.WordTrace tailWord_1021149 prefixEnd_1021149 51786692035370911954699 := by
  unfold tailWord_1021149
  simp only [CollatzResearch.WordTrace]
  refine ⟨37244363777559046209746501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24829575851706030806497667 37244363777559046209746501)
  ·
    refine ⟨6983318208292321164327469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37244363777559046209746501 6983318208292321164327469)
    ·
      refine ⟨2618744328109620436622801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6983318208292321164327469 2618744328109620436622801)
      ·
        refine ⟨1964058246082215327467101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2618744328109620436622801 1964058246082215327467101)
        ·
          refine ⟨736521842280830747800163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1964058246082215327467101 736521842280830747800163)
          ·
            refine ⟨1104782763421246121700245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736521842280830747800163 1104782763421246121700245)
            ·
              refine ⟨51786692035370911954699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1104782763421246121700245 51786692035370911954699)
              ·
                rfl

theorem cell20_1021149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 6].length) (baseStart_1021149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021149 prefixEnd_1021149 := by exact prefixLift 1021149
  have htrace : WordTrace (prefixWord ++ tailWord_1021149) baseStart_1021149 baseEnd_1021149 := by
    simpa [prefixWord, tailWord_1021149, baseEnd_1021149] using wordTrace_append hprefix tailTrace_1021149
  have hstable : (prefixWord ++ tailWord_1021149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021149).length < 2 ^ (prefixWord ++ tailWord_1021149).sum := by decide
  have hdescent : baseEnd_1021149 < baseStart_1021149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021153 : List Nat := [1, 2, 3, 1, 3, 4, 6]
def baseStart_1021153 : Nat := 118140960795 + 1021153 * 2 ^ 59
def prefixEnd_1021153 : Nat := 4983230072969 + 3 ^ 40 * 1021153 * 2
def baseEnd_1021153 : Nat := 51786894891925774606549

theorem tailTrace_1021153 : CollatzResearch.WordTrace tailWord_1021153 prefixEnd_1021153 51786894891925774606549 := by
  unfold tailWord_1021153
  simp only [CollatzResearch.WordTrace]
  refine ⟨37244509669544554892892113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24829673113029703261928075 37244509669544554892892113)
  ·
    refine ⟨27933382252158416169669085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37244509669544554892892113 27933382252158416169669085)
    ·
      refine ⟨10475018344559406063625907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27933382252158416169669085 10475018344559406063625907)
      ·
        refine ⟨15712527516839109095438861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10475018344559406063625907 15712527516839109095438861)
        ·
          refine ⟨5892197818814665910789573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15712527516839109095438861 5892197818814665910789573)
          ·
            refine ⟨1104787091027749858273045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5892197818814665910789573 1104787091027749858273045)
            ·
              refine ⟨51786894891925774606549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1104787091027749858273045 51786894891925774606549)
              ·
                rfl

theorem cell20_1021153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 6].length) (baseStart_1021153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021153 prefixEnd_1021153 := by exact prefixLift 1021153
  have htrace : WordTrace (prefixWord ++ tailWord_1021153) baseStart_1021153 baseEnd_1021153 := by
    simpa [prefixWord, tailWord_1021153, baseEnd_1021153] using wordTrace_append hprefix tailTrace_1021153
  have hstable : (prefixWord ++ tailWord_1021153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021153).length < 2 ^ (prefixWord ++ tailWord_1021153).sum := by decide
  have hdescent : baseEnd_1021153 < baseStart_1021153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021159 : List Nat := [1, 1, 5, 3, 2, 1, 3, 2, 2]
def baseStart_1021159 : Nat := 118140960795 + 1021159 * 2 ^ 59
def prefixEnd_1021159 : Nat := 4983230072969 + 3 ^ 40 * 1021159 * 2
def baseEnd_1021159 : Nat := 466084792590822617258917

theorem tailTrace_1021159 : CollatzResearch.WordTrace tailWord_1021159 prefixEnd_1021159 466084792590822617258917 := by
  unfold tailWord_1021159
  simp only [CollatzResearch.WordTrace]
  refine ⟨37244728507522817917610531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24829819005015211945073687 37244728507522817917610531)
  ·
    refine ⟨55867092761284226876415797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37244728507522817917610531 55867092761284226876415797)
    ·
      refine ⟨5237539946370396269663981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55867092761284226876415797 5237539946370396269663981)
      ·
        refine ⟨1964077479888898601123993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5237539946370396269663981 1964077479888898601123993)
        ·
          refine ⟨1473058109916673950842995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1964077479888898601123993 1473058109916673950842995)
          ·
            refine ⟨2209587164875010926264493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473058109916673950842995 2209587164875010926264493)
            ·
              refine ⟨828595186828129097349185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2209587164875010926264493 828595186828129097349185)
              ·
                refine ⟨621446390121096823011889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828595186828129097349185 621446390121096823011889)
                ·
                  refine ⟨466084792590822617258917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621446390121096823011889 466084792590822617258917)
                  ·
                    rfl

theorem cell20_1021159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 2].length) (baseStart_1021159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021159 prefixEnd_1021159 := by exact prefixLift 1021159
  have htrace : WordTrace (prefixWord ++ tailWord_1021159) baseStart_1021159 baseEnd_1021159 := by
    simpa [prefixWord, tailWord_1021159, baseEnd_1021159] using wordTrace_append hprefix tailTrace_1021159
  have hstable : (prefixWord ++ tailWord_1021159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021159).length < 2 ^ (prefixWord ++ tailWord_1021159).sum := by decide
  have hdescent : baseEnd_1021159 < baseStart_1021159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021160 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_1021160 : Nat := 118140960795 + 1021160 * 2 ^ 59
def prefixEnd_1021160 : Nat := 4983230072969 + 3 ^ 40 * 1021160 * 2
def baseEnd_1021160 : Nat := 466085249018071058225579

theorem tailTrace_1021160 : CollatzResearch.WordTrace tailWord_1021160 prefixEnd_1021160 466085249018071058225579 := by
  unfold tailWord_1021160
  simp only [CollatzResearch.WordTrace]
  refine ⟨18622382490259597544198467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24829843320346130058931289 18622382490259597544198467)
  ·
    refine ⟨27933573735389396316297701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18622382490259597544198467 27933573735389396316297701)
    ·
      refine ⟨5237545075385511809305819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27933573735389396316297701 5237545075385511809305819)
      ·
        refine ⟨7856317613078267713958729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237545075385511809305819 7856317613078267713958729)
        ·
          refine ⟨5892238209808700785469047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7856317613078267713958729 5892238209808700785469047)
          ·
            refine ⟨8838357314713051178203571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892238209808700785469047 8838357314713051178203571)
            ·
              refine ⟨13257535972069576767305357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838357314713051178203571 13257535972069576767305357)
              ·
                refine ⟨4971575989526091287739509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13257535972069576767305357 4971575989526091287739509)
                ·
                  refine ⟨466085249018071058225579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4971575989526091287739509 466085249018071058225579)
                  ·
                    rfl

theorem cell20_1021160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_1021160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021160 prefixEnd_1021160 := by exact prefixLift 1021160
  have htrace : WordTrace (prefixWord ++ tailWord_1021160) baseStart_1021160 baseEnd_1021160 := by
    simpa [prefixWord, tailWord_1021160, baseEnd_1021160] using wordTrace_append hprefix tailTrace_1021160
  have hstable : (prefixWord ++ tailWord_1021160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021160).length < 2 ^ (prefixWord ++ tailWord_1021160).sum := by decide
  have hdescent : baseEnd_1021160 < baseStart_1021160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021170 : List Nat := [3, 2, 1, 3, 3, 1, 2, 5]
def baseStart_1021170 : Nat := 118140960795 + 1021170 * 2 ^ 59
def prefixEnd_1021170 : Nat := 4983230072969 + 3 ^ 40 * 1021170 * 2
def baseEnd_1021170 : Nat := 155363271096851822630735

theorem tailTrace_1021170 : CollatzResearch.WordTrace tailWord_1021170 prefixEnd_1021170 155363271096851822630735 := by
  unfold tailWord_1021170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9311282427620741699065241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24830086473655311197507309 9311282427620741699065241)
  ·
    refine ⟨6983461820715556274298931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9311282427620741699065241 6983461820715556274298931)
    ·
      refine ⟨10475192731073334411448397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6983461820715556274298931 10475192731073334411448397)
      ·
        refine ⟨3928197274152500404293149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10475192731073334411448397 3928197274152500404293149)
        ·
          refine ⟨1473073977807187651609931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3928197274152500404293149 1473073977807187651609931)
          ·
            refine ⟨2209610966710781477414897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473073977807187651609931 2209610966710781477414897)
            ·
              refine ⟨1657208225033086108061173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209610966710781477414897 1657208225033086108061173)
              ·
                refine ⟨155363271096851822630735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1657208225033086108061173 155363271096851822630735)
                ·
                  rfl

theorem cell20_1021170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_1021170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021170 prefixEnd_1021170 := by exact prefixLift 1021170
  have htrace : WordTrace (prefixWord ++ tailWord_1021170) baseStart_1021170 baseEnd_1021170 := by
    simpa [prefixWord, tailWord_1021170, baseEnd_1021170] using wordTrace_append hprefix tailTrace_1021170
  have hstable : (prefixWord ++ tailWord_1021170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021170).length < 2 ^ (prefixWord ++ tailWord_1021170).sum := by decide
  have hdescent : baseEnd_1021170 < baseStart_1021170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021218 : List Nat := [3, 3, 1, 1, 4, 1, 1, 4, 2]
def baseStart_1021218 : Nat := 118140960795 + 1021218 * 2 ^ 59
def prefixEnd_1021218 : Nat := 4983230072969 + 3 ^ 40 * 1021218 * 2
def baseEnd_1021218 : Nat := 466111721798480634292009

theorem tailTrace_1021218 : CollatzResearch.WordTrace tailWord_1021218 prefixEnd_1021218 466111721798480634292009 := by
  unfold tailWord_1021218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9311720103577267748502077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24831253609539380662672205 9311720103577267748502077)
  ·
    refine ⟨3491895038841475405688279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9311720103577267748502077 3491895038841475405688279)
    ·
      refine ⟨5237842558262213108532419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491895038841475405688279 5237842558262213108532419)
      ·
        refine ⟨7856763837393319662798629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237842558262213108532419 7856763837393319662798629)
        ·
          refine ⟨1473143219511247436774743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7856763837393319662798629 1473143219511247436774743)
          ·
            refine ⟨2209714829266871155162115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473143219511247436774743 2209714829266871155162115)
            ·
              refine ⟨3314572243900306732743173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2209714829266871155162115 3314572243900306732743173)
              ·
                refine ⟨621482295731307512389345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3314572243900306732743173 621482295731307512389345)
                ·
                  refine ⟨466111721798480634292009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621482295731307512389345 466111721798480634292009)
                  ·
                    rfl

theorem cell20_1021218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_1021218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021218 prefixEnd_1021218 := by exact prefixLift 1021218
  have htrace : WordTrace (prefixWord ++ tailWord_1021218) baseStart_1021218 baseEnd_1021218 := by
    simpa [prefixWord, tailWord_1021218, baseEnd_1021218] using wordTrace_append hprefix tailTrace_1021218
  have hstable : (prefixWord ++ tailWord_1021218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021218).length < 2 ^ (prefixWord ++ tailWord_1021218).sum := by decide
  have hdescent : baseEnd_1021218 < baseStart_1021218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021246 : List Nat := [4, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1021246 : Nat := 118140960795 + 1021246 * 2 ^ 59
def prefixEnd_1021246 : Nat := 4983230072969 + 3 ^ 40 * 1021246 * 2
def baseEnd_1021246 : Nat := 155374833920478993786187

theorem tailTrace_1021246 : CollatzResearch.WordTrace tailWord_1021246 prefixEnd_1021246 155374833920478993786187 := by
  unfold tailWord_1021246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4655987707275953972003449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24831934438805087850685061 4655987707275953972003449)
  ·
    refine ⟨3491990780456965479002587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4655987707275953972003449 3491990780456965479002587)
    ·
      refine ⟨5237986170685448218503881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491990780456965479002587 5237986170685448218503881)
      ·
        refine ⟨3928489628014086163877911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5237986170685448218503881 3928489628014086163877911)
        ·
          refine ⟨5892734442021129245816867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928489628014086163877911 5892734442021129245816867)
          ·
            refine ⟨8839101663031693868725301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892734442021129245816867 8839101663031693868725301)
            ·
              refine ⟨828665780909221300192997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8839101663031693868725301 828665780909221300192997)
              ·
                refine ⟨155374833920478993786187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 828665780909221300192997 155374833920478993786187)
                ·
                  rfl

theorem cell20_1021246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1021246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021246 prefixEnd_1021246 := by exact prefixLift 1021246
  have htrace : WordTrace (prefixWord ++ tailWord_1021246) baseStart_1021246 baseEnd_1021246 := by
    simpa [prefixWord, tailWord_1021246, baseEnd_1021246] using wordTrace_append hprefix tailTrace_1021246
  have hstable : (prefixWord ++ tailWord_1021246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021246).length < 2 ^ (prefixWord ++ tailWord_1021246).sum := by decide
  have hdescent : baseEnd_1021246 < baseStart_1021246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021301 : List Nat := [1, 3, 4, 1, 3, 2, 2, 4]
def baseStart_1021301 : Nat := 118140960795 + 1021301 * 2 ^ 59
def prefixEnd_1021301 : Nat := 4983230072969 + 3 ^ 40 * 1021301 * 2
def baseEnd_1021301 : Nat := 155383201753367078175001

theorem tailTrace_1021301 : CollatzResearch.WordTrace tailWord_1021301 prefixEnd_1021301 155383201753367078175001 := by
  unfold tailWord_1021301
  simp only [CollatzResearch.WordTrace]
  refine ⟨37249907673008376169279757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24833271782005584112853171 37249907673008376169279757)
  ·
    refine ⟨13968715377378141063479909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37249907673008376169279757 13968715377378141063479909)
    ·
      refine ⟨2619134133258401449402483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13968715377378141063479909 2619134133258401449402483)
      ·
        refine ⟨3928701199887602174103725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619134133258401449402483 3928701199887602174103725)
        ·
          refine ⟨1473262949957850815288897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3928701199887602174103725 1473262949957850815288897)
          ·
            refine ⟨1104947212468388111466673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473262949957850815288897 1104947212468388111466673)
            ·
              refine ⟨828710409351291083600005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104947212468388111466673 828710409351291083600005)
              ·
                refine ⟨155383201753367078175001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 828710409351291083600005 155383201753367078175001)
                ·
                  rfl

theorem cell20_1021301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 4].length) (baseStart_1021301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021301 prefixEnd_1021301 := by exact prefixLift 1021301
  have htrace : WordTrace (prefixWord ++ tailWord_1021301) baseStart_1021301 baseEnd_1021301 := by
    simpa [prefixWord, tailWord_1021301, baseEnd_1021301] using wordTrace_append hprefix tailTrace_1021301
  have hstable : (prefixWord ++ tailWord_1021301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021301).length < 2 ^ (prefixWord ++ tailWord_1021301).sum := by decide
  have hdescent : baseEnd_1021301 < baseStart_1021301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021305 : List Nat := [1, 2, 1, 3, 2, 1, 6, 4]
def baseStart_1021305 : Nat := 118140960795 + 1021305 * 2 ^ 59
def prefixEnd_1021305 : Nat := 4983230072969 + 3 ^ 40 * 1021305 * 2
def baseEnd_1021305 : Nat := 155383810323031666130551

theorem tailTrace_1021305 : CollatzResearch.WordTrace tailWord_1021305 prefixEnd_1021305 155383810323031666130551 := by
  unfold tailWord_1021305
  simp only [CollatzResearch.WordTrace]
  refine ⟨37250053564993884852425369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24833369043329256568283579 37250053564993884852425369)
  ·
    refine ⟨27937540173745413639319027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37250053564993884852425369 27937540173745413639319027)
    ·
      refine ⟨41906310260618120458978541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27937540173745413639319027 41906310260618120458978541)
      ·
        refine ⟨15714866347731795172116953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41906310260618120458978541 15714866347731795172116953)
        ·
          refine ⟨11786149760798846379087715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15714866347731795172116953 11786149760798846379087715)
          ·
            refine ⟨17679224641198269568631573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11786149760798846379087715 17679224641198269568631573)
            ·
              refine ⟨828713655056168886029605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17679224641198269568631573 828713655056168886029605)
              ·
                refine ⟨155383810323031666130551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 828713655056168886029605 155383810323031666130551)
                ·
                  rfl

theorem cell20_1021305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 4].length) (baseStart_1021305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021305 prefixEnd_1021305 := by exact prefixLift 1021305
  have htrace : WordTrace (prefixWord ++ tailWord_1021305) baseStart_1021305 baseEnd_1021305 := by
    simpa [prefixWord, tailWord_1021305, baseEnd_1021305] using wordTrace_append hprefix tailTrace_1021305
  have hstable : (prefixWord ++ tailWord_1021305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021305).length < 2 ^ (prefixWord ++ tailWord_1021305).sum := by decide
  have hdescent : baseEnd_1021305 < baseStart_1021305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021315 : List Nat := [1, 1, 1, 3, 5, 1, 3, 3, 2]
def baseStart_1021315 : Nat := 118140960795 + 1021315 * 2 ^ 59
def prefixEnd_1021315 : Nat := 4983230072969 + 3 ^ 40 * 1021315 * 2
def baseEnd_1021315 : Nat := 466155995241579408058279

theorem tailTrace_1021315 : CollatzResearch.WordTrace tailWord_1021315 prefixEnd_1021315 466155995241579408058279 := by
  unfold tailWord_1021315
  simp only [CollatzResearch.WordTrace]
  refine ⟨37250418294957656560289399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24833612196638437706859599 37250418294957656560289399)
  ·
    refine ⟨55875627442436484840434099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37250418294957656560289399 55875627442436484840434099)
    ·
      refine ⟨83813441163654727260651149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55875627442436484840434099 83813441163654727260651149)
      ·
        refine ⟨31430040436370522722744181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83813441163654727260651149 31430040436370522722744181)
        ·
          refine ⟨2946566290909736505257267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31430040436370522722744181 2946566290909736505257267)
          ·
            refine ⟨4419849436364604757885901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946566290909736505257267 4419849436364604757885901)
            ·
              refine ⟨1657443538636726784207213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4419849436364604757885901 1657443538636726784207213)
              ·
                refine ⟨621541326988772544077705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1657443538636726784207213 621541326988772544077705)
                ·
                  refine ⟨466155995241579408058279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621541326988772544077705 466155995241579408058279)
                  ·
                    rfl

theorem cell20_1021315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 2].length) (baseStart_1021315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021315 prefixEnd_1021315 := by exact prefixLift 1021315
  have htrace : WordTrace (prefixWord ++ tailWord_1021315) baseStart_1021315 baseEnd_1021315 := by
    simpa [prefixWord, tailWord_1021315, baseEnd_1021315] using wordTrace_append hprefix tailTrace_1021315
  have hstable : (prefixWord ++ tailWord_1021315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021315).length < 2 ^ (prefixWord ++ tailWord_1021315).sum := by decide
  have hdescent : baseEnd_1021315 < baseStart_1021315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021342 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1021342 : Nat := 118140960795 + 1021342 * 2 ^ 59
def prefixEnd_1021342 : Nat := 4983230072969 + 3 ^ 40 * 1021342 * 2
def baseEnd_1021342 : Nat := 466168318777287314158169

theorem tailTrace_1021342 : CollatzResearch.WordTrace tailWord_1021342 prefixEnd_1021342 466168318777287314158169 := by
  unfold tailWord_1021342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656425383232480021440285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24834268710573226781014853 4656425383232480021440285)
  ·
    refine ⟨1746159518712180008040107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4656425383232480021440285 1746159518712180008040107)
    ·
      refine ⟨2619239278068270012060161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746159518712180008040107 2619239278068270012060161)
      ·
        refine ⟨1964429458551202509045121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2619239278068270012060161 1964429458551202509045121)
        ·
          refine ⟨1473322093913401881783841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1964429458551202509045121 1473322093913401881783841)
          ·
            refine ⟨1104991570435051411337881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473322093913401881783841 1104991570435051411337881)
            ·
              refine ⟨828743677826288558503411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104991570435051411337881 828743677826288558503411)
              ·
                refine ⟨1243115516739432837755117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828743677826288558503411 1243115516739432837755117)
                ·
                  refine ⟨466168318777287314158169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243115516739432837755117 466168318777287314158169)
                  ·
                    rfl

theorem cell20_1021342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1021342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021342 prefixEnd_1021342 := by exact prefixLift 1021342
  have htrace : WordTrace (prefixWord ++ tailWord_1021342) baseStart_1021342 baseEnd_1021342 := by
    simpa [prefixWord, tailWord_1021342, baseEnd_1021342] using wordTrace_append hprefix tailTrace_1021342
  have hstable : (prefixWord ++ tailWord_1021342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021342).length < 2 ^ (prefixWord ++ tailWord_1021342).sum := by decide
  have hdescent : baseEnd_1021342 < baseStart_1021342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021343 : List Nat := [1, 1, 2, 5, 1, 3, 2, 5]
def baseStart_1021343 : Nat := 118140960795 + 1021343 * 2 ^ 59
def prefixEnd_1021343 : Nat := 4983230072969 + 3 ^ 40 * 1021343 * 2
def baseEnd_1021343 : Nat := 155389591734845251708277

theorem tailTrace_1021343 : CollatzResearch.WordTrace tailWord_1021343 prefixEnd_1021343 155389591734845251708277 := by
  unfold tailWord_1021343
  simp only [CollatzResearch.WordTrace]
  refine ⟨37251439538856217342308683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24834293025904144894872455 37251439538856217342308683)
  ·
    refine ⟨55877159308284326013463025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37251439538856217342308683 55877159308284326013463025)
    ·
      refine ⟨41907869481213244510097269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55877159308284326013463025 41907869481213244510097269)
      ·
        refine ⟨3928862763863741672821619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41907869481213244510097269 3928862763863741672821619)
        ·
          refine ⟨5893294145795612509232429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928862763863741672821619 5893294145795612509232429)
          ·
            refine ⟨2209985304673354690962161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5893294145795612509232429 2209985304673354690962161)
            ·
              refine ⟨1657488978505016018221621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209985304673354690962161 1657488978505016018221621)
              ·
                refine ⟨155389591734845251708277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1657488978505016018221621 155389591734845251708277)
                ·
                  rfl

theorem cell20_1021343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_1021343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021343 prefixEnd_1021343 := by exact prefixLift 1021343
  have htrace : WordTrace (prefixWord ++ tailWord_1021343) baseStart_1021343 baseEnd_1021343 := by
    simpa [prefixWord, tailWord_1021343, baseEnd_1021343] using wordTrace_append hprefix tailTrace_1021343
  have hstable : (prefixWord ++ tailWord_1021343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021343).length < 2 ^ (prefixWord ++ tailWord_1021343).sum := by decide
  have hdescent : baseEnd_1021343 < baseStart_1021343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021346 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1021346 : Nat := 118140960795 + 1021346 * 2 ^ 59
def prefixEnd_1021346 : Nat := 4983230072969 + 3 ^ 40 * 1021346 * 2
def baseEnd_1021346 : Nat := 466170144486281078024819

theorem tailTrace_1021346 : CollatzResearch.WordTrace tailWord_1021346 prefixEnd_1021346 466170144486281078024819 := by
  unfold tailWord_1021346
  simp only [CollatzResearch.WordTrace]
  refine ⟨9312887239461337213666973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24834365971896899236445261 9312887239461337213666973)
  ·
    refine ⟨3492332714798001455125115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9312887239461337213666973 3492332714798001455125115)
    ·
      refine ⟨5238499072197002182687673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3492332714798001455125115 5238499072197002182687673)
      ·
        refine ⟨3928874304147751637015755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5238499072197002182687673 3928874304147751637015755)
        ·
          refine ⟨5893311456221627455523633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928874304147751637015755 5893311456221627455523633)
          ·
            refine ⟨4419983592166220591642725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5893311456221627455523633 4419983592166220591642725)
            ·
              refine ⟨828746923531166360933011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4419983592166220591642725 828746923531166360933011)
              ·
                refine ⟨1243120385296749541399517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828746923531166360933011 1243120385296749541399517)
                ·
                  refine ⟨466170144486281078024819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243120385296749541399517 466170144486281078024819)
                  ·
                    rfl

theorem cell20_1021346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1021346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021346 prefixEnd_1021346 := by exact prefixLift 1021346
  have htrace : WordTrace (prefixWord ++ tailWord_1021346) baseStart_1021346 baseEnd_1021346 := by
    simpa [prefixWord, tailWord_1021346, baseEnd_1021346] using wordTrace_append hprefix tailTrace_1021346
  have hstable : (prefixWord ++ tailWord_1021346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021346).length < 2 ^ (prefixWord ++ tailWord_1021346).sum := by decide
  have hdescent : baseEnd_1021346 < baseStart_1021346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021391 : List Nat := [1, 1, 2, 1, 1, 4, 6, 2, 2]
def baseStart_1021391 : Nat := 118140960795 + 1021391 * 2 ^ 59
def prefixEnd_1021391 : Nat := 4983230072969 + 3 ^ 40 * 1021391 * 2
def baseEnd_1021391 : Nat := 466190683712460921524635

theorem tailTrace_1021391 : CollatzResearch.WordTrace tailWord_1021391 prefixEnd_1021391 466190683712460921524635 := by
  unfold tailWord_1021391
  simp only [CollatzResearch.WordTrace]
  refine ⟨37253190242682321540056027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24835460161788214360037351 37253190242682321540056027)
  ·
    refine ⟨55879785364023482310084041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37253190242682321540056027 55879785364023482310084041)
    ·
      refine ⟨41909839023017611732563031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55879785364023482310084041 41909839023017611732563031)
      ·
        refine ⟨62864758534526417598844547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41909839023017611732563031 62864758534526417598844547)
        ·
          refine ⟨94297137801789626398266821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62864758534526417598844547 94297137801789626398266821)
          ·
            refine ⟨17680713337835554949675029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94297137801789626398266821 17680713337835554949675029)
            ·
              refine ⟨828783437711041638266017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17680713337835554949675029 828783437711041638266017)
              ·
                refine ⟨621587578283281228699513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828783437711041638266017 621587578283281228699513)
                ·
                  refine ⟨466190683712460921524635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621587578283281228699513 466190683712460921524635)
                  ·
                    rfl

theorem cell20_1021391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 2].length) (baseStart_1021391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021391 prefixEnd_1021391 := by exact prefixLift 1021391
  have htrace : WordTrace (prefixWord ++ tailWord_1021391) baseStart_1021391 baseEnd_1021391 := by
    simpa [prefixWord, tailWord_1021391, baseEnd_1021391] using wordTrace_append hprefix tailTrace_1021391
  have hstable : (prefixWord ++ tailWord_1021391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021391).length < 2 ^ (prefixWord ++ tailWord_1021391).sum := by decide
  have hdescent : baseEnd_1021391 < baseStart_1021391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021398 : List Nat := [5, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1021398 : Nat := 118140960795 + 1021398 * 2 ^ 59
def prefixEnd_1021398 : Nat := 4983230072969 + 3 ^ 40 * 1021398 * 2
def baseEnd_1021398 : Nat := 155397959567733336097091

theorem tailTrace_1021398 : CollatzResearch.WordTrace tailWord_1021398 prefixEnd_1021398 155397959567733336097091 := by
  unfold tailWord_1021398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2328340347103560108472553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24835630369104641157040565 2328340347103560108472553)
  ·
    refine ⟨1746255260327670081354415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2328340347103560108472553 1746255260327670081354415)
    ·
      refine ⟨2619382890491505122031623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746255260327670081354415 2619382890491505122031623)
      ·
        refine ⟨3929074335737257683047435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619382890491505122031623 3929074335737257683047435)
        ·
          refine ⟨5893611503605886524571153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929074335737257683047435 5893611503605886524571153)
          ·
            refine ⟨4420208627704414893428365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5893611503605886524571153 4420208627704414893428365)
            ·
              refine ⟨1657578235389155585035637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4420208627704414893428365 1657578235389155585035637)
              ·
                refine ⟨155397959567733336097091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1657578235389155585035637 155397959567733336097091)
                ·
                  rfl

theorem cell20_1021398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1021398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021398 prefixEnd_1021398 := by exact prefixLift 1021398
  have htrace : WordTrace (prefixWord ++ tailWord_1021398) baseStart_1021398 baseEnd_1021398 := by
    simpa [prefixWord, tailWord_1021398, baseEnd_1021398] using wordTrace_append hprefix tailTrace_1021398
  have hstable : (prefixWord ++ tailWord_1021398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021398).length < 2 ^ (prefixWord ++ tailWord_1021398).sum := by decide
  have hdescent : baseEnd_1021398 < baseStart_1021398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021405 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1021405 : Nat := 118140960795 + 1021405 * 2 ^ 59
def prefixEnd_1021405 : Nat := 4983230072969 + 3 ^ 40 * 1021405 * 2
def baseEnd_1021405 : Nat := 466197073693939095057911

theorem tailTrace_1021405 : CollatzResearch.WordTrace tailWord_1021405 prefixEnd_1021405 466197073693939095057911 := by
  unfold tailWord_1021405
  simp only [CollatzResearch.WordTrace]
  refine ⟨37253700864631601931065669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24835800576421067954043779 37253700864631601931065669)
  ·
    refine ⟨6985068912118425362074813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37253700864631601931065669 6985068912118425362074813)
    ·
      refine ⟨2619400842044409510778055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6985068912118425362074813 2619400842044409510778055)
      ·
        refine ⟨3929101263066614266167083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619400842044409510778055 3929101263066614266167083)
        ·
          refine ⟨5893651894599921399250625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929101263066614266167083 5893651894599921399250625)
          ·
            refine ⟨4420238920949941049437969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5893651894599921399250625 4420238920949941049437969)
            ·
              refine ⟨3315179190712455787078477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420238920949941049437969 3315179190712455787078477)
              ·
                refine ⟨1243192196517170920154429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3315179190712455787078477 1243192196517170920154429)
                ·
                  refine ⟨466197073693939095057911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243192196517170920154429 466197073693939095057911)
                  ·
                    rfl

theorem cell20_1021405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1021405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021405 prefixEnd_1021405 := by exact prefixLift 1021405
  have htrace : WordTrace (prefixWord ++ tailWord_1021405) baseStart_1021405 baseEnd_1021405 := by
    simpa [prefixWord, tailWord_1021405, baseEnd_1021405] using wordTrace_append hprefix tailTrace_1021405
  have hstable : (prefixWord ++ tailWord_1021405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021405).length < 2 ^ (prefixWord ++ tailWord_1021405).sum := by decide
  have hdescent : baseEnd_1021405 < baseStart_1021405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021450 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1021450 : Nat := 118140960795 + 1021450 * 2 ^ 59
def prefixEnd_1021450 : Nat := 4983230072969 + 3 ^ 40 * 1021450 * 2
def baseEnd_1021450 : Nat := 466217612920118938557727

theorem tailTrace_1021450 : CollatzResearch.WordTrace tailWord_1021450 prefixEnd_1021450 466217612920118938557727 := by
  unfold tailWord_1021450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9313835537367143654113451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24836894766312383077635869 9313835537367143654113451)
  ·
    refine ⟨13970753306050715481170177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9313835537367143654113451 13970753306050715481170177)
    ·
      refine ⟨10478064979538036610877633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13970753306050715481170177 10478064979538036610877633)
      ·
        refine ⟨7858548734653527458158225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10478064979538036610877633 7858548734653527458158225)
        ·
          refine ⟨5893911550990145593618669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7858548734653527458158225 5893911550990145593618669)
          ·
            refine ⟨2210216831621304597607001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5893911550990145593618669 2210216831621304597607001)
            ·
              refine ⟨1657662623715978448205251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210216831621304597607001 1657662623715978448205251)
              ·
                refine ⟨2486493935573967672307877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657662623715978448205251 2486493935573967672307877)
                ·
                  refine ⟨466217612920118938557727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486493935573967672307877 466217612920118938557727)
                  ·
                    rfl

theorem cell20_1021450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1021450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021450 prefixEnd_1021450 := by exact prefixLift 1021450
  have htrace : WordTrace (prefixWord ++ tailWord_1021450) baseStart_1021450 baseEnd_1021450 := by
    simpa [prefixWord, tailWord_1021450, baseEnd_1021450] using wordTrace_append hprefix tailTrace_1021450
  have hstable : (prefixWord ++ tailWord_1021450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021450).length < 2 ^ (prefixWord ++ tailWord_1021450).sum := by decide
  have hdescent : baseEnd_1021450 < baseStart_1021450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021470 : List Nat := [4, 3, 3, 1, 1, 1, 1, 6]
def baseStart_1021470 : Nat := 118140960795 + 1021470 * 2 ^ 59
def prefixEnd_1021470 : Nat := 4983230072969 + 3 ^ 40 * 1021470 * 2
def baseEnd_1021470 : Nat := 155408913821695919296993

theorem tailTrace_1021470 : CollatzResearch.WordTrace tailWord_1021470 prefixEnd_1021470 155408913821695919296993 := by
  unfold tailWord_1021470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4657008951174514754022733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24837381072930745354787909 4657008951174514754022733)
  ·
    refine ⟨1746378356690443032758525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4657008951174514754022733 1746378356690443032758525)
    ·
      refine ⟨654891883758916137284447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1746378356690443032758525 654891883758916137284447)
      ·
        refine ⟨982337825638374205926671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654891883758916137284447 982337825638374205926671)
        ·
          refine ⟨1473506738457561308890007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982337825638374205926671 1473506738457561308890007)
          ·
            refine ⟨2210260107686341963335011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473506738457561308890007 2210260107686341963335011)
            ·
              refine ⟨3315390161529512945002517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2210260107686341963335011 3315390161529512945002517)
              ·
                refine ⟨155408913821695919296993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3315390161529512945002517 155408913821695919296993)
                ·
                  rfl

theorem cell20_1021470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_1021470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021470 prefixEnd_1021470 := by exact prefixLift 1021470
  have htrace : WordTrace (prefixWord ++ tailWord_1021470) baseStart_1021470 baseEnd_1021470 := by
    simpa [prefixWord, tailWord_1021470, baseEnd_1021470] using wordTrace_append hprefix tailTrace_1021470
  have hstable : (prefixWord ++ tailWord_1021470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021470).length < 2 ^ (prefixWord ++ tailWord_1021470).sum := by decide
  have hdescent : baseEnd_1021470 < baseStart_1021470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021471 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_1021471 : Nat := 118140960795 + 1021471 * 2 ^ 59
def prefixEnd_1021471 : Nat := 4983230072969 + 3 ^ 40 * 1021471 * 2
def baseEnd_1021471 : Nat := 466227197892336198857641

theorem tailTrace_1021471 : CollatzResearch.WordTrace tailWord_1021471 prefixEnd_1021471 466227197892336198857641 := by
  unfold tailWord_1021471
  simp only [CollatzResearch.WordTrace]
  refine ⟨37256108082392495202968267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24837405388261663468645511 37256108082392495202968267)
  ·
    refine ⟨55884162123588742804452401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37256108082392495202968267 55884162123588742804452401)
    ·
      refine ⟨41913121592691557103339301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55884162123588742804452401 41913121592691557103339301)
      ·
        refine ⟨7858710298629666956876119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41913121592691557103339301 7858710298629666956876119)
        ·
          refine ⟨11788065447944500435314179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7858710298629666956876119 11788065447944500435314179)
          ·
            refine ⟨17682098171916750652971269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11788065447944500435314179 17682098171916750652971269)
            ·
              refine ⟨3315393407234390747432113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17682098171916750652971269 3315393407234390747432113)
              ·
                refine ⟨2486545055425793060574085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3315393407234390747432113 2486545055425793060574085)
                ·
                  refine ⟨466227197892336198857641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486545055425793060574085 466227197892336198857641)
                  ·
                    rfl

theorem cell20_1021471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_1021471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021471 prefixEnd_1021471 := by exact prefixLift 1021471
  have htrace : WordTrace (prefixWord ++ tailWord_1021471) baseStart_1021471 baseEnd_1021471 := by
    simpa [prefixWord, tailWord_1021471, baseEnd_1021471] using wordTrace_append hprefix tailTrace_1021471
  have hstable : (prefixWord ++ tailWord_1021471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021471).length < 2 ^ (prefixWord ++ tailWord_1021471).sum := by decide
  have hdescent : baseEnd_1021471 < baseStart_1021471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021516 : List Nat := [2, 2, 1, 3, 1, 3, 1, 7]
def baseStart_1021516 : Nat := 118140960795 + 1021516 * 2 ^ 59
def prefixEnd_1021516 : Nat := 4983230072969 + 3 ^ 40 * 1021516 * 2
def baseEnd_1021516 : Nat := 155415912372838680785819

theorem tailTrace_1021516 : CollatzResearch.WordTrace tailWord_1021516 prefixEnd_1021516 155415912372838680785819 := by
  unfold tailWord_1021516
  simp only [CollatzResearch.WordTrace]
  refine ⟨18628874683614733944178201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24838499578152978592237601 18628874683614733944178201)
  ·
    refine ⟨13971656012711050458133651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18628874683614733944178201 13971656012711050458133651)
    ·
      refine ⟨20957484019066575687200477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13971656012711050458133651 20957484019066575687200477)
      ·
        refine ⟨7859056507149965882700179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20957484019066575687200477 7859056507149965882700179)
        ·
          refine ⟨11788584760724948824050269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7859056507149965882700179 11788584760724948824050269)
          ·
            refine ⟨4420719285271855809018851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11788584760724948824050269 4420719285271855809018851)
            ·
              refine ⟨6631078927907783713528277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420719285271855809018851 6631078927907783713528277)
              ·
                refine ⟨155415912372838680785819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6631078927907783713528277 155415912372838680785819)
                ·
                  rfl

theorem cell20_1021516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_1021516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021516 prefixEnd_1021516 := by exact prefixLift 1021516
  have htrace : WordTrace (prefixWord ++ tailWord_1021516) baseStart_1021516 baseEnd_1021516 := by
    simpa [prefixWord, tailWord_1021516, baseEnd_1021516] using wordTrace_append hprefix tailTrace_1021516
  have hstable : (prefixWord ++ tailWord_1021516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021516).length < 2 ^ (prefixWord ++ tailWord_1021516).sum := by decide
  have hdescent : baseEnd_1021516 < baseStart_1021516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021554 : List Nat := [3, 2, 1, 2, 3, 9]
def baseStart_1021554 : Nat := 118140960795 + 1021554 * 2 ^ 59
def prefixEnd_1021554 : Nat := 4983230072969 + 3 ^ 40 * 1021554 * 2
def baseEnd_1021554 : Nat := 17269077087183585151505

theorem tailTrace_1021554 : CollatzResearch.WordTrace tailWord_1021554 prefixEnd_1021554 17269077087183585151505 := by
  unfold tailWord_1021554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9314783835272950094559929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24839423560727866918826477 9314783835272950094559929)
  ·
    refine ⟨6986087876454712570919947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9314783835272950094559929 6986087876454712570919947)
    ·
      refine ⟨10479131814682068856379921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6986087876454712570919947 10479131814682068856379921)
      ·
        refine ⟨7859348861011551642284941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10479131814682068856379921 7859348861011551642284941)
        ·
          refine ⟨2947255822879331865856853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7859348861011551642284941 2947255822879331865856853)
          ·
            refine ⟨17269077087183585151505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2947255822879331865856853 17269077087183585151505)
            ·
              rfl

theorem cell20_1021554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 9].length) (baseStart_1021554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021554 prefixEnd_1021554 := by exact prefixLift 1021554
  have htrace : WordTrace (prefixWord ++ tailWord_1021554) baseStart_1021554 baseEnd_1021554 := by
    simpa [prefixWord, tailWord_1021554, baseEnd_1021554] using wordTrace_append hprefix tailTrace_1021554
  have hstable : (prefixWord ++ tailWord_1021554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021554).length < 2 ^ (prefixWord ++ tailWord_1021554).sum := by decide
  have hdescent : baseEnd_1021554 < baseStart_1021554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021557 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 3]
def baseStart_1021557 : Nat := 118140960795 + 1021557 * 2 ^ 59
def prefixEnd_1021557 : Nat := 4983230072969 + 3 ^ 40 * 1021557 * 2
def baseEnd_1021557 : Nat := 466266450635702121990623

theorem tailTrace_1021557 : CollatzResearch.WordTrace tailWord_1021557 prefixEnd_1021557 466266450635702121990623 := by
  unfold tailWord_1021557
  simp only [CollatzResearch.WordTrace]
  refine ⟨37259244760080931890598925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24839496506720621260399283 37259244760080931890598925)
  ·
    refine ⟨13972216785030349458974597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37259244760080931890598925 13972216785030349458974597)
    ·
      refine ⟨2619790647193190523557737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13972216785030349458974597 2619790647193190523557737)
      ·
        refine ⟨1964842985394892892668303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2619790647193190523557737 1964842985394892892668303)
        ·
          refine ⟨2947264478092339339002455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964842985394892892668303 2947264478092339339002455)
          ·
            refine ⟨4420896717138509008503683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947264478092339339002455 4420896717138509008503683)
            ·
              refine ⟨6631345075707763512755525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420896717138509008503683 6631345075707763512755525)
              ·
                refine ⟨1243377201695205658641661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6631345075707763512755525 1243377201695205658641661)
                ·
                  refine ⟨466266450635702121990623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243377201695205658641661 466266450635702121990623)
                  ·
                    rfl

theorem cell20_1021557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_1021557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021557 prefixEnd_1021557 := by exact prefixLift 1021557
  have htrace : WordTrace (prefixWord ++ tailWord_1021557) baseStart_1021557 baseEnd_1021557 := by
    simpa [prefixWord, tailWord_1021557, baseEnd_1021557] using wordTrace_append hprefix tailTrace_1021557
  have hstable : (prefixWord ++ tailWord_1021557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021557).length < 2 ^ (prefixWord ++ tailWord_1021557).sum := by decide
  have hdescent : baseEnd_1021557 < baseStart_1021557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021598 : List Nat := [4, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1021598 : Nat := 118140960795 + 1021598 * 2 ^ 59
def prefixEnd_1021598 : Nat := 4983230072969 + 3 ^ 40 * 1021598 * 2
def baseEnd_1021598 : Nat := 466285164152888201623789

theorem tailTrace_1021598 : CollatzResearch.WordTrace tailWord_1021598 prefixEnd_1021598 466285164152888201623789 := by
  unfold tailWord_1021598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4657592519116549486605181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24840493435288263928560965 4657592519116549486605181)
  ·
    refine ⟨1746597194668706057476943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4657592519116549486605181 1746597194668706057476943)
    ·
      refine ⟨2619895792003059086215415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746597194668706057476943 2619895792003059086215415)
      ·
        refine ⟨3929843688004588629323123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619895792003059086215415 3929843688004588629323123)
        ·
          refine ⟨5894765532006882943984685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929843688004588629323123 5894765532006882943984685)
          ·
            refine ⟨2210537074502581103994257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5894765532006882943984685 2210537074502581103994257)
            ·
              refine ⟨1657902805876935827995693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210537074502581103994257 1657902805876935827995693)
              ·
                refine ⟨621713552203850935498385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1657902805876935827995693 621713552203850935498385)
                ·
                  refine ⟨466285164152888201623789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621713552203850935498385 466285164152888201623789)
                  ·
                    rfl

theorem cell20_1021598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1021598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021598 prefixEnd_1021598 := by exact prefixLift 1021598
  have htrace : WordTrace (prefixWord ++ tailWord_1021598) baseStart_1021598 baseEnd_1021598 := by
    simpa [prefixWord, tailWord_1021598, baseEnd_1021598] using wordTrace_append hprefix tailTrace_1021598
  have hstable : (prefixWord ++ tailWord_1021598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021598).length < 2 ^ (prefixWord ++ tailWord_1021598).sum := by decide
  have hdescent : baseEnd_1021598 < baseStart_1021598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021608 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 3]
def baseStart_1021608 : Nat := 118140960795 + 1021608 * 2 ^ 59
def prefixEnd_1021608 : Nat := 4983230072969 + 3 ^ 40 * 1021608 * 2
def baseEnd_1021608 : Nat := 466289728425372611290415

theorem tailTrace_1021608 : CollatzResearch.WordTrace tailWord_1021608 prefixEnd_1021608 466289728425372611290415 := by
  unfold tailWord_1021608
  simp only [CollatzResearch.WordTrace]
  refine ⟨18630552441448083800352739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24840736588597445067136985 18630552441448083800352739)
  ·
    refine ⟨27945828662172125700529109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18630552441448083800352739 27945828662172125700529109)
    ·
      refine ⟨654980359269659196106151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 27945828662172125700529109 654980359269659196106151)
      ·
        refine ⟨982470538904488794159227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654980359269659196106151 982470538904488794159227)
        ·
          refine ⟨1473705808356733191238841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982470538904488794159227 1473705808356733191238841)
          ·
            refine ⟨1105279356267549893429131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473705808356733191238841 1105279356267549893429131)
            ·
              refine ⟨1657919034401324840143697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105279356267549893429131 1657919034401324840143697)
              ·
                refine ⟨1243439275800993630107773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657919034401324840143697 1243439275800993630107773)
                ·
                  refine ⟨466289728425372611290415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243439275800993630107773 466289728425372611290415)
                  ·
                    rfl

theorem cell20_1021608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_1021608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021608 prefixEnd_1021608 := by exact prefixLift 1021608
  have htrace : WordTrace (prefixWord ++ tailWord_1021608) baseStart_1021608 baseEnd_1021608 := by
    simpa [prefixWord, tailWord_1021608, baseEnd_1021608] using wordTrace_append hprefix tailTrace_1021608
  have hstable : (prefixWord ++ tailWord_1021608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021608).length < 2 ^ (prefixWord ++ tailWord_1021608).sum := by decide
  have hdescent : baseEnd_1021608 < baseStart_1021608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021616 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 3]
def baseStart_1021616 : Nat := 118140960795 + 1021616 * 2 ^ 59
def prefixEnd_1021616 : Nat := 4983230072969 + 3 ^ 40 * 1021616 * 2
def baseEnd_1021616 : Nat := 466293379843360139023715

theorem tailTrace_1021616 : CollatzResearch.WordTrace tailWord_1021616 prefixEnd_1021616 466293379843360139023715 := by
  unfold tailWord_1021616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18630698333433592483498351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24840931111244789977997801 18630698333433592483498351)
  ·
    refine ⟨27946047500150388725247527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18630698333433592483498351 27946047500150388725247527)
    ·
      refine ⟨41919071250225583087871291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27946047500150388725247527 41919071250225583087871291)
      ·
        refine ⟨62878606875338374631806937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41919071250225583087871291 62878606875338374631806937)
        ·
          refine ⟨47158955156503780973855203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62878606875338374631806937 47158955156503780973855203)
          ·
            refine ⟨70738432734755671460782805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47158955156503780973855203 70738432734755671460782805)
            ·
              refine ⟨1657932017220836049862097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 70738432734755671460782805 1657932017220836049862097)
              ·
                refine ⟨1243449012915627037396573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657932017220836049862097 1243449012915627037396573)
                ·
                  refine ⟨466293379843360139023715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243449012915627037396573 466293379843360139023715)
                  ·
                    rfl

theorem cell20_1021616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_1021616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021616 prefixEnd_1021616 := by exact prefixLift 1021616
  have htrace : WordTrace (prefixWord ++ tailWord_1021616) baseStart_1021616 baseEnd_1021616 := by
    simpa [prefixWord, tailWord_1021616, baseEnd_1021616] using wordTrace_append hprefix tailTrace_1021616
  have hstable : (prefixWord ++ tailWord_1021616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021616).length < 2 ^ (prefixWord ++ tailWord_1021616).sum := by decide
  have hdescent : baseEnd_1021616 < baseStart_1021616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021623 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_1021623 : Nat := 118140960795 + 1021623 * 2 ^ 59
def prefixEnd_1021623 : Nat := 4983230072969 + 3 ^ 40 * 1021623 * 2
def baseEnd_1021623 : Nat := 466296574834099225790353

theorem tailTrace_1021623 : CollatzResearch.WordTrace tailWord_1021623 prefixEnd_1021623 466296574834099225790353 := by
  unfold tailWord_1021623
  simp only [CollatzResearch.WordTrace]
  refine ⟨37261651977841825162501523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24841101318561216775001015 37261651977841825162501523)
  ·
    refine ⟨55892477966762737743752285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37261651977841825162501523 55892477966762737743752285)
    ·
      refine ⟨20959679237536026653907107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55892477966762737743752285 20959679237536026653907107)
      ·
        refine ⟨31439518856304039980860661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20959679237536026653907107 31439518856304039980860661)
        ·
          refine ⟨2947454892778503748205687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31439518856304039980860661 2947454892778503748205687)
          ·
            refine ⟨4421182339167755622308531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947454892778503748205687 4421182339167755622308531)
            ·
              refine ⟨6631773508751633433462797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421182339167755622308531 6631773508751633433462797)
              ·
                refine ⟨2486915065781862537548549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6631773508751633433462797 2486915065781862537548549)
                ·
                  refine ⟨466296574834099225790353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486915065781862537548549 466296574834099225790353)
                  ·
                    rfl

theorem cell20_1021623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_1021623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021623 prefixEnd_1021623 := by exact prefixLift 1021623
  have htrace : WordTrace (prefixWord ++ tailWord_1021623) baseStart_1021623 baseEnd_1021623 := by
    simpa [prefixWord, tailWord_1021623, baseEnd_1021623] using wordTrace_append hprefix tailTrace_1021623
  have hstable : (prefixWord ++ tailWord_1021623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021623).length < 2 ^ (prefixWord ++ tailWord_1021623).sum := by decide
  have hdescent : baseEnd_1021623 < baseStart_1021623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021657 : List Nat := [1, 2, 1, 2, 3, 5, 1, 3, 2]
def baseStart_1021657 : Nat := 118140960795 + 1021657 * 2 ^ 59
def prefixEnd_1021657 : Nat := 4983230072969 + 3 ^ 40 * 1021657 * 2
def baseEnd_1021657 : Nat := 466312093360546218656881

theorem tailTrace_1021657 : CollatzResearch.WordTrace tailWord_1021657 prefixEnd_1021657 466312093360546218656881 := by
  unfold tailWord_1021657
  simp only [CollatzResearch.WordTrace]
  refine ⟨37262892059718648969239225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24841928039812432646159483 37262892059718648969239225)
  ·
    refine ⟨27947169044788986726929419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37262892059718648969239225 27947169044788986726929419)
    ·
      refine ⟨41920753567183480090394129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27947169044788986726929419 41920753567183480090394129)
      ·
        refine ⟨31440565175387610067795597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41920753567183480090394129 31440565175387610067795597)
        ·
          refine ⟨11790211940770353775423349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31440565175387610067795597 11790211940770353775423349)
          ·
            refine ⟨1105332369447220666445939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11790211940770353775423349 1105332369447220666445939)
            ·
              refine ⟨1657998554170830999668909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105332369447220666445939 1657998554170830999668909)
              ·
                refine ⟨621749457814061624875841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1657998554170830999668909 621749457814061624875841)
                ·
                  refine ⟨466312093360546218656881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621749457814061624875841 466312093360546218656881)
                  ·
                    rfl

theorem cell20_1021657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_1021657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021657 prefixEnd_1021657 := by exact prefixLift 1021657
  have htrace : WordTrace (prefixWord ++ tailWord_1021657) baseStart_1021657 baseEnd_1021657 := by
    simpa [prefixWord, tailWord_1021657, baseEnd_1021657] using wordTrace_append hprefix tailTrace_1021657
  have hstable : (prefixWord ++ tailWord_1021657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021657).length < 2 ^ (prefixWord ++ tailWord_1021657).sum := by decide
  have hdescent : baseEnd_1021657 < baseStart_1021657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021675 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_1021675 : Nat := 118140960795 + 1021675 * 2 ^ 59
def prefixEnd_1021675 : Nat := 4983230072969 + 3 ^ 40 * 1021675 * 2
def baseEnd_1021675 : Nat := 466320309051018156056807

theorem tailTrace_1021675 : CollatzResearch.WordTrace tailWord_1021675 prefixEnd_1021675 466320309051018156056807 := by
  unfold tailWord_1021675
  simp only [CollatzResearch.WordTrace]
  refine ⟨37263548573653438043394479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24842365715768958695596319 37263548573653438043394479)
  ·
    refine ⟨55895322860480157065091719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37263548573653438043394479 55895322860480157065091719)
    ·
      refine ⟨83842984290720235597637579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55895322860480157065091719 83842984290720235597637579)
      ·
        refine ⟨125764476436080353396456369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83842984290720235597637579 125764476436080353396456369)
        ·
          refine ⟨94323357327060265047342277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125764476436080353396456369 94323357327060265047342277)
          ·
            refine ⟨17685629498823799696376677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94323357327060265047342277 17685629498823799696376677)
            ·
              refine ⟨3316055531029462443070627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17685629498823799696376677 3316055531029462443070627)
              ·
                refine ⟨4974083296544193664605941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316055531029462443070627 4974083296544193664605941)
                ·
                  refine ⟨466320309051018156056807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974083296544193664605941 466320309051018156056807)
                  ·
                    rfl

theorem cell20_1021675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_1021675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021675 prefixEnd_1021675 := by exact prefixLift 1021675
  have htrace : WordTrace (prefixWord ++ tailWord_1021675) baseStart_1021675 baseEnd_1021675 := by
    simpa [prefixWord, tailWord_1021675, baseEnd_1021675] using wordTrace_append hprefix tailTrace_1021675
  have hstable : (prefixWord ++ tailWord_1021675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021675).length < 2 ^ (prefixWord ++ tailWord_1021675).sum := by decide
  have hdescent : baseEnd_1021675 < baseStart_1021675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021684 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1021684 : Nat := 118140960795 + 1021684 * 2 ^ 59
def prefixEnd_1021684 : Nat := 4983230072969 + 3 ^ 40 * 1021684 * 2
def baseEnd_1021684 : Nat := 466324416896254124756771

theorem tailTrace_1021684 : CollatzResearch.WordTrace tailWord_1021684 prefixEnd_1021684 466324416896254124756771 := by
  unfold tailWord_1021684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18631938415310416290236053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24842584553747221720314737 18631938415310416290236053)
  ·
    refine ⟨873372113217675763604815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18631938415310416290236053 873372113217675763604815)
    ·
      refine ⟨1310058169826513645407223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 873372113217675763604815 1310058169826513645407223)
      ·
        refine ⟨1965087254739770468110835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310058169826513645407223 1965087254739770468110835)
        ·
          refine ⟨2947630882109655702166253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1965087254739770468110835 2947630882109655702166253)
          ·
            refine ⟨1105361580791120888312345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2947630882109655702166253 1105361580791120888312345)
            ·
              refine ⟨829021185593340666234259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105361580791120888312345 829021185593340666234259)
              ·
                refine ⟨1243531778390010999351389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829021185593340666234259 1243531778390010999351389)
                ·
                  refine ⟨466324416896254124756771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243531778390010999351389 466324416896254124756771)
                  ·
                    rfl

theorem cell20_1021684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1021684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021684 prefixEnd_1021684 := by exact prefixLift 1021684
  have htrace : WordTrace (prefixWord ++ tailWord_1021684) baseStart_1021684 baseEnd_1021684 := by
    simpa [prefixWord, tailWord_1021684, baseEnd_1021684] using wordTrace_append hprefix tailTrace_1021684
  have hstable : (prefixWord ++ tailWord_1021684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021684).length < 2 ^ (prefixWord ++ tailWord_1021684).sum := by decide
  have hdescent : baseEnd_1021684 < baseStart_1021684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021692 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 3]
def baseStart_1021692 : Nat := 118140960795 + 1021692 * 2 ^ 59
def prefixEnd_1021692 : Nat := 4983230072969 + 3 ^ 40 * 1021692 * 2
def baseEnd_1021692 : Nat := 466328068314241652490071

theorem tailTrace_1021692 : CollatzResearch.WordTrace tailWord_1021692 prefixEnd_1021692 466328068314241652490071 := by
  unfold tailWord_1021692
  simp only [CollatzResearch.WordTrace]
  refine ⟨18632084307295924973381665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24842779076394566631175553 18632084307295924973381665)
  ·
    refine ⟨13974063230471943730036249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18632084307295924973381665 13974063230471943730036249)
    ·
      refine ⟨10480547422853957797527187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13974063230471943730036249 10480547422853957797527187)
      ·
        refine ⟨15720821134280936696290781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10480547422853957797527187 15720821134280936696290781)
        ·
          refine ⟨5895307925355351261109043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15720821134280936696290781 5895307925355351261109043)
          ·
            refine ⟨8842961888033026891663565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895307925355351261109043 8842961888033026891663565)
            ·
              refine ⟨3316110708012385084373837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8842961888033026891663565 3316110708012385084373837)
              ·
                refine ⟨1243541515504644406640189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3316110708012385084373837 1243541515504644406640189)
                ·
                  refine ⟨466328068314241652490071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243541515504644406640189 466328068314241652490071)
                  ·
                    rfl

theorem cell20_1021692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_1021692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021692 prefixEnd_1021692 := by exact prefixLift 1021692
  have htrace : WordTrace (prefixWord ++ tailWord_1021692) baseStart_1021692 baseEnd_1021692 := by
    simpa [prefixWord, tailWord_1021692, baseEnd_1021692] using wordTrace_append hprefix tailTrace_1021692
  have hstable : (prefixWord ++ tailWord_1021692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021692).length < 2 ^ (prefixWord ++ tailWord_1021692).sum := by decide
  have hdescent : baseEnd_1021692 < baseStart_1021692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021706 : List Nat := [3, 1, 2, 2, 1, 3, 2, 6]
def baseStart_1021706 : Nat := 118140960795 + 1021706 * 2 ^ 59
def prefixEnd_1021706 : Nat := 4983230072969 + 3 ^ 40 * 1021706 * 2
def baseEnd_1021706 : Nat := 155444819431906608674449

theorem tailTrace_1021706 : CollatzResearch.WordTrace tailWord_1021706 prefixEnd_1021706 155444819431906608674449 := by
  unfold tailWord_1021706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9316169809135282584443243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24843119491027420225181981 9316169809135282584443243)
  ·
    refine ⟨13974254713702923876664865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9316169809135282584443243 13974254713702923876664865)
    ·
      refine ⟨10480691035277192907498649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13974254713702923876664865 10480691035277192907498649)
      ·
        refine ⟨7860518276457894680623987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10480691035277192907498649 7860518276457894680623987)
        ·
          refine ⟨11790777414686842020935981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7860518276457894680623987 11790777414686842020935981)
          ·
            refine ⟨4421541530507565757850993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11790777414686842020935981 4421541530507565757850993)
            ·
              refine ⟨3316156147880674318388245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421541530507565757850993 3316156147880674318388245)
              ·
                refine ⟨155444819431906608674449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3316156147880674318388245 155444819431906608674449)
                ·
                  rfl

theorem cell20_1021706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_1021706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021706 prefixEnd_1021706 := by exact prefixLift 1021706
  have htrace : WordTrace (prefixWord ++ tailWord_1021706) baseStart_1021706 baseEnd_1021706 := by
    simpa [prefixWord, tailWord_1021706, baseEnd_1021706] using wordTrace_append hprefix tailTrace_1021706
  have hstable : (prefixWord ++ tailWord_1021706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021706).length < 2 ^ (prefixWord ++ tailWord_1021706).sum := by decide
  have hdescent : baseEnd_1021706 < baseStart_1021706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021733 : List Nat := [1, 3, 1, 2, 3, 2, 4, 2, 2]
def baseStart_1021733 : Nat := 118140960795 + 1021733 * 2 ^ 59
def prefixEnd_1021733 : Nat := 4983230072969 + 3 ^ 40 * 1021733 * 2
def baseEnd_1021733 : Nat := 466346781831427732123237

theorem tailTrace_1021733 : CollatzResearch.WordTrace tailWord_1021733 prefixEnd_1021733 466346781831427732123237 := by
  unfold tailWord_1021733
  simp only [CollatzResearch.WordTrace]
  refine ⟨37265664007443313949005853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24843776004962209299337235 37265664007443313949005853)
  ·
    refine ⟨13974624002791242730877195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37265664007443313949005853 13974624002791242730877195)
    ·
      refine ⟨20961936004186864096315793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13974624002791242730877195 20961936004186864096315793)
      ·
        refine ⟨15721452003140148072236845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20961936004186864096315793 15721452003140148072236845)
        ·
          refine ⟨5895544501177555527088817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15721452003140148072236845 5895544501177555527088817)
          ·
            refine ⟨4421658375883166645316613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5895544501177555527088817 4421658375883166645316613)
            ·
              refine ⟨829060945478093745996865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4421658375883166645316613 829060945478093745996865)
              ·
                refine ⟨621795709108570309497649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 829060945478093745996865 621795709108570309497649)
                ·
                  refine ⟨466346781831427732123237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621795709108570309497649 466346781831427732123237)
                  ·
                    rfl

theorem cell20_1021733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_1021733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021733 prefixEnd_1021733 := by exact prefixLift 1021733
  have htrace : WordTrace (prefixWord ++ tailWord_1021733) baseStart_1021733 baseEnd_1021733 := by
    simpa [prefixWord, tailWord_1021733, baseEnd_1021733] using wordTrace_append hprefix tailTrace_1021733
  have hstable : (prefixWord ++ tailWord_1021733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021733).length < 2 ^ (prefixWord ++ tailWord_1021733).sum := by decide
  have hdescent : baseEnd_1021733 < baseStart_1021733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021792 : List Nat := [2, 1, 1, 3, 3, 2, 2, 4, 2]
def baseStart_1021792 : Nat := 118140960795 + 1021792 * 2 ^ 59
def prefixEnd_1021792 : Nat := 4983230072969 + 3 ^ 40 * 1021792 * 2
def baseEnd_1021792 : Nat := 466373711039085749156329

theorem tailTrace_1021792 : CollatzResearch.WordTrace tailWord_1021792 prefixEnd_1021792 466373711039085749156329 := by
  unfold tailWord_1021792
  simp only [CollatzResearch.WordTrace]
  refine ⟨18633907957114783512701815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24845210609486378016935753 18633907957114783512701815)
  ·
    refine ⟨27950861935672175269052723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18633907957114783512701815 27950861935672175269052723)
    ·
      refine ⟨41926292903508262903579085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27950861935672175269052723 41926292903508262903579085)
      ·
        refine ⟨15722359838815598588842157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41926292903508262903579085 15722359838815598588842157)
        ·
          refine ⟨5895884939555849470815809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15722359838815598588842157 5895884939555849470815809)
          ·
            refine ⟨4421913704666887103111857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5895884939555849470815809 4421913704666887103111857)
            ·
              refine ⟨3316435278500165327333893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421913704666887103111857 3316435278500165327333893)
              ·
                refine ⟨621831614718780998875105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3316435278500165327333893 621831614718780998875105)
                ·
                  refine ⟨466373711039085749156329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621831614718780998875105 466373711039085749156329)
                  ·
                    rfl

theorem cell20_1021792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_1021792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021792 prefixEnd_1021792 := by exact prefixLift 1021792
  have htrace : WordTrace (prefixWord ++ tailWord_1021792) baseStart_1021792 baseEnd_1021792 := by
    simpa [prefixWord, tailWord_1021792, baseEnd_1021792] using wordTrace_append hprefix tailTrace_1021792
  have hstable : (prefixWord ++ tailWord_1021792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021792).length < 2 ^ (prefixWord ++ tailWord_1021792).sum := by decide
  have hdescent : baseEnd_1021792 < baseStart_1021792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021803 : List Nat := [1, 1, 1, 1, 2, 2, 3, 9]
def baseStart_1021803 : Nat := 118140960795 + 1021803 * 2 ^ 59
def prefixEnd_1021803 : Nat := 4983230072969 + 3 ^ 40 * 1021803 * 2
def baseEnd_1021803 : Nat := 155459577246272866596539

theorem tailTrace_1021803 : CollatzResearch.WordTrace tailWord_1021803 prefixEnd_1021803 155459577246272866596539 := by
  unfold tailWord_1021803
  simp only [CollatzResearch.WordTrace]
  refine ⟨37268217117189715904054063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24845478078126477269369375 37268217117189715904054063)
  ·
    refine ⟨55902325675784573856081095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37268217117189715904054063 55902325675784573856081095)
    ·
      refine ⟨83853488513676860784121643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55902325675784573856081095 83853488513676860784121643)
      ·
        refine ⟨125780232770515291176182465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83853488513676860784121643 125780232770515291176182465)
        ·
          refine ⟨94335174577886468382136849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125780232770515291176182465 94335174577886468382136849)
          ·
            refine ⟨70751380933414851286602637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94335174577886468382136849 70751380933414851286602637)
            ·
              refine ⟨26531767850030569232475989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70751380933414851286602637 26531767850030569232475989)
              ·
                refine ⟨155459577246272866596539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26531767850030569232475989 155459577246272866596539)
                ·
                  rfl

theorem cell20_1021803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_1021803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021803 prefixEnd_1021803 := by exact prefixLift 1021803
  have htrace : WordTrace (prefixWord ++ tailWord_1021803) baseStart_1021803 baseEnd_1021803 := by
    simpa [prefixWord, tailWord_1021803, baseEnd_1021803] using wordTrace_append hprefix tailTrace_1021803
  have hstable : (prefixWord ++ tailWord_1021803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021803).length < 2 ^ (prefixWord ++ tailWord_1021803).sum := by decide
  have hdescent : baseEnd_1021803 < baseStart_1021803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021813 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_1021813 : Nat := 118140960795 + 1021813 * 2 ^ 59
def prefixEnd_1021813 : Nat := 4983230072969 + 3 ^ 40 * 1021813 * 2
def baseEnd_1021813 : Nat := 466383296011303009456243

theorem tailTrace_1021813 : CollatzResearch.WordTrace tailWord_1021813 prefixEnd_1021813 466383296011303009456243 := by
  unfold tailWord_1021813
  simp only [CollatzResearch.WordTrace]
  refine ⟨37268581847153487611918093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24845721231435658407945395 37268581847153487611918093)
  ·
    refine ⟨13975718192682557854469285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37268581847153487611918093 13975718192682557854469285)
    ·
      refine ⟨2620447161127979597712991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13975718192682557854469285 2620447161127979597712991)
      ·
        refine ⟨3930670741691969396569487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2620447161127979597712991 3930670741691969396569487)
        ·
          refine ⟨5896006112537954094854231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930670741691969396569487 5896006112537954094854231)
          ·
            refine ⟨8844009168806931142281347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896006112537954094854231 8844009168806931142281347)
            ·
              refine ⟨13266013753210396713422021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844009168806931142281347 13266013753210396713422021)
              ·
                refine ⟨2487377578726949383766629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13266013753210396713422021 2487377578726949383766629)
                ·
                  refine ⟨466383296011303009456243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2487377578726949383766629 466383296011303009456243)
                  ·
                    rfl

theorem cell20_1021813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_1021813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021813 prefixEnd_1021813 := by exact prefixLift 1021813
  have htrace : WordTrace (prefixWord ++ tailWord_1021813) baseStart_1021813 baseEnd_1021813 := by
    simpa [prefixWord, tailWord_1021813, baseEnd_1021813] using wordTrace_append hprefix tailTrace_1021813
  have hstable : (prefixWord ++ tailWord_1021813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021813).length < 2 ^ (prefixWord ++ tailWord_1021813).sum := by decide
  have hdescent : baseEnd_1021813 < baseStart_1021813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021827 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_1021827 : Nat := 118140960795 + 1021827 * 2 ^ 59
def prefixEnd_1021827 : Nat := 4983230072969 + 3 ^ 40 * 1021827 * 2
def baseEnd_1021827 : Nat := 466389685992781182989519

theorem tailTrace_1021827 : CollatzResearch.WordTrace tailWord_1021827 prefixEnd_1021827 466389685992781182989519 := by
  unfold tailWord_1021827
  simp only [CollatzResearch.WordTrace]
  refine ⟨37269092469102768002927735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24846061646068512001951823 37269092469102768002927735)
  ·
    refine ⟨55903638703654152004391603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37269092469102768002927735 55903638703654152004391603)
    ·
      refine ⟨83855458055481228006587405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55903638703654152004391603 83855458055481228006587405)
      ·
        refine ⟨31445796770805460502470277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83855458055481228006587405 31445796770805460502470277)
        ·
          refine ⟨5896086894526023844213177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31445796770805460502470277 5896086894526023844213177)
          ·
            refine ⟨4422065170894517883159883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5896086894526023844213177 4422065170894517883159883)
            ·
              refine ⟨6633097756341776824739825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4422065170894517883159883 6633097756341776824739825)
              ·
                refine ⟨4974823317256332618554869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6633097756341776824739825 4974823317256332618554869)
                ·
                  refine ⟨466389685992781182989519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974823317256332618554869 466389685992781182989519)
                  ·
                    rfl

theorem cell20_1021827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_1021827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021827 prefixEnd_1021827 := by exact prefixLift 1021827
  have htrace : WordTrace (prefixWord ++ tailWord_1021827) baseStart_1021827 baseEnd_1021827 := by
    simpa [prefixWord, tailWord_1021827, baseEnd_1021827] using wordTrace_append hprefix tailTrace_1021827
  have hstable : (prefixWord ++ tailWord_1021827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021827).length < 2 ^ (prefixWord ++ tailWord_1021827).sum := by decide
  have hdescent : baseEnd_1021827 < baseStart_1021827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021841 : List Nat := [1, 2, 2, 1, 1, 1, 12]
def baseStart_1021841 : Nat := 118140960795 + 1021841 * 2 ^ 59
def prefixEnd_1021841 : Nat := 4983230072969 + 3 ^ 40 * 1021841 * 2
def baseEnd_1021841 : Nat := 51821786219362150724755

theorem tailTrace_1021841 : CollatzResearch.WordTrace tailWord_1021841 prefixEnd_1021841 51821786219362150724755 := by
  unfold tailWord_1021841
  simp only [CollatzResearch.WordTrace]
  refine ⟨37269603091052048393937377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24846402060701365595958251 37269603091052048393937377)
  ·
    refine ⟨27952202318289036295453033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37269603091052048393937377 27952202318289036295453033)
    ·
      refine ⟨20964151738716777221589775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27952202318289036295453033 20964151738716777221589775)
      ·
        refine ⟨31446227608075165832384663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20964151738716777221589775 31446227608075165832384663)
        ·
          refine ⟨47169341412112748748576995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31446227608075165832384663 47169341412112748748576995)
          ·
            refine ⟨70754012118169123122865493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47169341412112748748576995 70754012118169123122865493)
            ·
              refine ⟨51821786219362150724755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 70754012118169123122865493 51821786219362150724755)
              ·
                rfl

theorem cell20_1021841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 12].length) (baseStart_1021841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021841 prefixEnd_1021841 := by exact prefixLift 1021841
  have htrace : WordTrace (prefixWord ++ tailWord_1021841) baseStart_1021841 baseEnd_1021841 := by
    simpa [prefixWord, tailWord_1021841, baseEnd_1021841] using wordTrace_append hprefix tailTrace_1021841
  have hstable : (prefixWord ++ tailWord_1021841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021841).length < 2 ^ (prefixWord ++ tailWord_1021841).sum := by decide
  have hdescent : baseEnd_1021841 < baseStart_1021841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021844 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1021844 : Nat := 118140960795 + 1021844 * 2 ^ 59
def prefixEnd_1021844 : Nat := 4983230072969 + 3 ^ 40 * 1021844 * 2
def baseEnd_1021844 : Nat := 466397445256004679422783

theorem tailTrace_1021844 : CollatzResearch.WordTrace tailWord_1021844 prefixEnd_1021844 466397445256004679422783 := by
  unfold tailWord_1021844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18634856255020589953148293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24846475006694119937531057 18634856255020589953148293)
  ·
    refine ⟨3494035547816360616215305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18634856255020589953148293 3494035547816360616215305)
    ·
      refine ⟨2620526660862270462161479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3494035547816360616215305 2620526660862270462161479)
      ·
        refine ⟨3930789991293405693242219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2620526660862270462161479 3930789991293405693242219)
        ·
          refine ⟨5896184986940108539863329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930789991293405693242219 5896184986940108539863329)
          ·
            refine ⟨4422138740205081404897497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5896184986940108539863329 4422138740205081404897497)
            ·
              refine ⟨3316604055153811053673123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4422138740205081404897497 3316604055153811053673123)
              ·
                refine ⟨4974906082730716580509685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316604055153811053673123 4974906082730716580509685)
                ·
                  refine ⟨466397445256004679422783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974906082730716580509685 466397445256004679422783)
                  ·
                    rfl

theorem cell20_1021844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1021844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021844 prefixEnd_1021844 := by exact prefixLift 1021844
  have htrace : WordTrace (prefixWord ++ tailWord_1021844) baseStart_1021844 baseEnd_1021844 := by
    simpa [prefixWord, tailWord_1021844, baseEnd_1021844] using wordTrace_append hprefix tailTrace_1021844
  have hstable : (prefixWord ++ tailWord_1021844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021844).length < 2 ^ (prefixWord ++ tailWord_1021844).sum := by decide
  have hdescent : baseEnd_1021844 < baseStart_1021844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021847 : List Nat := [1, 1, 3, 3, 1, 4, 3, 2, 2]
def baseStart_1021847 : Nat := 118140960795 + 1021847 * 2 ^ 59
def prefixEnd_1021847 : Nat := 4983230072969 + 3 ^ 40 * 1021847 * 2
def baseEnd_1021847 : Nat := 466398814537750002322771

theorem tailTrace_1021847 : CollatzResearch.WordTrace tailWord_1021847 prefixEnd_1021847 466398814537750002322771 := by
  unfold tailWord_1021847
  simp only [CollatzResearch.WordTrace]
  refine ⟨37269821929030311418655795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24846547952686874279103863 37269821929030311418655795)
  ·
    refine ⟨55904732893545467127983693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37269821929030311418655795 55904732893545467127983693)
    ·
      refine ⟨20964274835079550172993885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55904732893545467127983693 20964274835079550172993885)
      ·
        refine ⟨7861603063154831314872707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20964274835079550172993885 7861603063154831314872707)
        ·
          refine ⟨11792404594732246972309061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7861603063154831314872707 11792404594732246972309061)
          ·
            refine ⟨2211075861512296307307949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11792404594732246972309061 2211075861512296307307949)
            ·
              refine ⟨829153448067111115240481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2211075861512296307307949 829153448067111115240481)
              ·
                refine ⟨621865086050333336430361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 829153448067111115240481 621865086050333336430361)
                ·
                  refine ⟨466398814537750002322771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621865086050333336430361 466398814537750002322771)
                  ·
                    rfl

theorem cell20_1021847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 2].length) (baseStart_1021847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021847 prefixEnd_1021847 := by exact prefixLift 1021847
  have htrace : WordTrace (prefixWord ++ tailWord_1021847) baseStart_1021847 baseEnd_1021847 := by
    simpa [prefixWord, tailWord_1021847, baseEnd_1021847] using wordTrace_append hprefix tailTrace_1021847
  have hstable : (prefixWord ++ tailWord_1021847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021847).length < 2 ^ (prefixWord ++ tailWord_1021847).sum := by decide
  have hdescent : baseEnd_1021847 < baseStart_1021847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021857 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 3]
def baseStart_1021857 : Nat := 118140960795 + 1021857 * 2 ^ 59
def prefixEnd_1021857 : Nat := 4983230072969 + 3 ^ 40 * 1021857 * 2
def baseEnd_1021857 : Nat := 466403378810234411989397

theorem tailTrace_1021857 : CollatzResearch.WordTrace tailWord_1021857 prefixEnd_1021857 466403378810234411989397 := by
  unfold tailWord_1021857
  simp only [CollatzResearch.WordTrace]
  refine ⟨37270186658994083126519825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24846791105996055417679883 37270186658994083126519825)
  ·
    refine ⟨27952639994245562344889869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37270186658994083126519825 27952639994245562344889869)
    ·
      refine ⟨10482239997842085879333701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27952639994245562344889869 10482239997842085879333701)
      ·
        refine ⟨1965419999595391102375069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10482239997842085879333701 1965419999595391102375069)
        ·
          refine ⟨737032499848271663390651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1965419999595391102375069 737032499848271663390651)
          ·
            refine ⟨1105548749772407495085977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737032499848271663390651 1105548749772407495085977)
            ·
              refine ⟨829161562329305621314483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105548749772407495085977 829161562329305621314483)
              ·
                refine ⟨1243742343493958431971725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829161562329305621314483 1243742343493958431971725)
                ·
                  refine ⟨466403378810234411989397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243742343493958431971725 466403378810234411989397)
                  ·
                    rfl

theorem cell20_1021857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_1021857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021857 prefixEnd_1021857 := by exact prefixLift 1021857
  have htrace : WordTrace (prefixWord ++ tailWord_1021857) baseStart_1021857 baseEnd_1021857 := by
    simpa [prefixWord, tailWord_1021857, baseEnd_1021857] using wordTrace_append hprefix tailTrace_1021857
  have hstable : (prefixWord ++ tailWord_1021857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021857).length < 2 ^ (prefixWord ++ tailWord_1021857).sum := by decide
  have hdescent : baseEnd_1021857 < baseStart_1021857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021913 : List Nat := [1, 2, 1, 2, 6, 2, 1, 5]
def baseStart_1021913 : Nat := 118140960795 + 1021913 * 2 ^ 59
def prefixEnd_1021913 : Nat := 4983230072969 + 3 ^ 40 * 1021913 * 2
def baseEnd_1021913 : Nat := 155476312912049035374167

theorem tailTrace_1021913 : CollatzResearch.WordTrace tailWord_1021913 prefixEnd_1021913 155476312912049035374167 := by
  unfold tailWord_1021913
  simp only [CollatzResearch.WordTrace]
  refine ⟨37272229146791204690558393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24848152764527469793705595 37272229146791204690558393)
  ·
    refine ⟨27954171860093403517918795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37272229146791204690558393 27954171860093403517918795)
    ·
      refine ⟨41931257790140105276878193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27954171860093403517918795 41931257790140105276878193)
      ·
        refine ⟨31448443342605078957658645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41931257790140105276878193 31448443342605078957658645)
        ·
          refine ⟨1474145781684613076140249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31448443342605078957658645 1474145781684613076140249)
          ·
            refine ⟨1105609336263459807105187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474145781684613076140249 1105609336263459807105187)
            ·
              refine ⟨1658414004395189710657781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105609336263459807105187 1658414004395189710657781)
              ·
                refine ⟨155476312912049035374167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1658414004395189710657781 155476312912049035374167)
                ·
                  rfl

theorem cell20_1021913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 5].length) (baseStart_1021913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021913 prefixEnd_1021913 := by exact prefixLift 1021913
  have htrace : WordTrace (prefixWord ++ tailWord_1021913) baseStart_1021913 baseEnd_1021913 := by
    simpa [prefixWord, tailWord_1021913, baseEnd_1021913] using wordTrace_append hprefix tailTrace_1021913
  have hstable : (prefixWord ++ tailWord_1021913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021913).length < 2 ^ (prefixWord ++ tailWord_1021913).sum := by decide
  have hdescent : baseEnd_1021913 < baseStart_1021913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021948 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1021948 : Nat := 118140960795 + 1021948 * 2 ^ 59
def prefixEnd_1021948 : Nat := 4983230072969 + 3 ^ 40 * 1021948 * 2
def baseEnd_1021948 : Nat := 466444913689842539955691

theorem tailTrace_1021948 : CollatzResearch.WordTrace tailWord_1021948 prefixEnd_1021948 466444913689842539955691 := by
  unfold tailWord_1021948
  simp only [CollatzResearch.WordTrace]
  refine ⟨18636752850832202834041249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24849003801109603778721665 18636752850832202834041249)
  ·
    refine ⟨13977564638124152125530937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18636752850832202834041249 13977564638124152125530937)
    ·
      refine ⟨10483173478593114094148203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13977564638124152125530937 10483173478593114094148203)
      ·
        refine ⟨15724760217889671141222305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10483173478593114094148203 15724760217889671141222305)
        ·
          refine ⟨11793570163417253355916729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15724760217889671141222305 11793570163417253355916729)
          ·
            refine ⟨8845177622562940016937547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11793570163417253355916729 8845177622562940016937547)
            ·
              refine ⟨13267766433844410025406321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8845177622562940016937547 13267766433844410025406321)
              ·
                refine ⟨9950824825383307519054741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13267766433844410025406321 9950824825383307519054741)
                ·
                  refine ⟨466444913689842539955691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9950824825383307519054741 466444913689842539955691)
                  ·
                    rfl

theorem cell20_1021948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1021948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021948 prefixEnd_1021948 := by exact prefixLift 1021948
  have htrace : WordTrace (prefixWord ++ tailWord_1021948) baseStart_1021948 baseEnd_1021948 := by
    simpa [prefixWord, tailWord_1021948, baseEnd_1021948] using wordTrace_append hprefix tailTrace_1021948
  have hstable : (prefixWord ++ tailWord_1021948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021948).length < 2 ^ (prefixWord ++ tailWord_1021948).sum := by decide
  have hdescent : baseEnd_1021948 < baseStart_1021948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021989 : List Nat := [1, 3, 1, 2, 2, 5, 2, 4]
def baseStart_1021989 : Nat := 118140960795 + 1021989 * 2 ^ 59
def prefixEnd_1021989 : Nat := 4983230072969 + 3 ^ 40 * 1021989 * 2
def baseEnd_1021989 : Nat := 155487875735676206529619

theorem tailTrace_1021989 : CollatzResearch.WordTrace tailWord_1021989 prefixEnd_1021989 155487875735676206529619 := by
  unfold tailWord_1021989
  simp only [CollatzResearch.WordTrace]
  refine ⟨37275001094515869670325021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24850000729677246446883347 37275001094515869670325021)
  ·
    refine ⟨13978125410443451126371883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37275001094515869670325021 13978125410443451126371883)
    ·
      refine ⟨20967188115665176689557825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13978125410443451126371883 20967188115665176689557825)
      ·
        refine ⟨15725391086748882517168369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20967188115665176689557825 15725391086748882517168369)
        ·
          refine ⟨11794043315061661887876277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15725391086748882517168369 11794043315061661887876277)
          ·
            refine ⟨1105691560787030801988401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11794043315061661887876277 1105691560787030801988401)
            ·
              refine ⟨829268670590273101491301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105691560787030801988401 829268670590273101491301)
              ·
                refine ⟨155487875735676206529619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829268670590273101491301 155487875735676206529619)
                ·
                  rfl

theorem cell20_1021989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 4].length) (baseStart_1021989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1021989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1021989 prefixEnd_1021989 := by exact prefixLift 1021989
  have htrace : WordTrace (prefixWord ++ tailWord_1021989) baseStart_1021989 baseEnd_1021989 := by
    simpa [prefixWord, tailWord_1021989, baseEnd_1021989] using wordTrace_append hprefix tailTrace_1021989
  have hstable : (prefixWord ++ tailWord_1021989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021989).length < 2 ^ (prefixWord ++ tailWord_1021989).sum := by decide
  have hdescent : baseEnd_1021989 < baseStart_1021989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022024 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_1022024 : Nat := 118140960795 + 1022024 * 2 ^ 59
def prefixEnd_1022024 : Nat := 4983230072969 + 3 ^ 40 * 1022024 * 2
def baseEnd_1022024 : Nat := 466479602160724053422047

theorem tailTrace_1022024 : CollatzResearch.WordTrace tailWord_1022024 prefixEnd_1022024 466479602160724053422047 := by
  unfold tailWord_1022024
  simp only [CollatzResearch.WordTrace]
  refine ⟨18638138824694535323924563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24850851766259380431899417 18638138824694535323924563)
  ·
    refine ⟨27957208237041802985886845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18638138824694535323924563 27957208237041802985886845)
    ·
      refine ⟨10483953088890676119707567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27957208237041802985886845 10483953088890676119707567)
      ·
        refine ⟨15725929633336014179561351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10483953088890676119707567 15725929633336014179561351)
        ·
          refine ⟨23588894450004021269342027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15725929633336014179561351 23588894450004021269342027)
          ·
            refine ⟨35383341675006031904013041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23588894450004021269342027 35383341675006031904013041)
            ·
              refine ⟨26537506256254523928009781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35383341675006031904013041 26537506256254523928009781)
              ·
                refine ⟨2487891211523861618250917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26537506256254523928009781 2487891211523861618250917)
                ·
                  refine ⟨466479602160724053422047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2487891211523861618250917 466479602160724053422047)
                  ·
                    rfl

theorem cell20_1022024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_1022024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022024 prefixEnd_1022024 := by exact prefixLift 1022024
  have htrace : WordTrace (prefixWord ++ tailWord_1022024) baseStart_1022024 baseEnd_1022024 := by
    simpa [prefixWord, tailWord_1022024, baseEnd_1022024] using wordTrace_append hprefix tailTrace_1022024
  have hstable : (prefixWord ++ tailWord_1022024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022024).length < 2 ^ (prefixWord ++ tailWord_1022024).sum := by decide
  have hdescent : baseEnd_1022024 < baseStart_1022024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022069 : List Nat := [1, 3, 4, 12]
def baseStart_1022069 : Nat := 118140960795 + 1022069 * 2 ^ 59
def prefixEnd_1022069 : Nat := 4983230072969 + 3 ^ 40 * 1022069 * 2
def baseEnd_1022069 : Nat := 1919753668258863773341

theorem tailTrace_1022069 : CollatzResearch.WordTrace tailWord_1022069 prefixEnd_1022069 1919753668258863773341 := by
  unfold tailWord_1022069
  simp only [CollatzResearch.WordTrace]
  refine ⟨37277918934226043333237261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24851945956150695555491507 37277918934226043333237261)
  ·
    refine ⟨13979219600334766249963973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37277918934226043333237261 13979219600334766249963973)
    ·
      refine ⟨2621103675062768671868245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13979219600334766249963973 2621103675062768671868245)
      ·
        refine ⟨1919753668258863773341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2621103675062768671868245 1919753668258863773341)
        ·
          rfl

theorem cell20_1022069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 12].length) (baseStart_1022069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022069 prefixEnd_1022069 := by exact prefixLift 1022069
  have htrace : WordTrace (prefixWord ++ tailWord_1022069) baseStart_1022069 baseEnd_1022069 := by
    simpa [prefixWord, tailWord_1022069, baseEnd_1022069] using wordTrace_append hprefix tailTrace_1022069
  have hstable : (prefixWord ++ tailWord_1022069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022069).length < 2 ^ (prefixWord ++ tailWord_1022069).sum := by decide
  have hdescent : baseEnd_1022069 < baseStart_1022069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022103 : List Nat := [1, 1, 3, 3, 4, 1, 3, 4]
def baseStart_1022103 : Nat := 118140960795 + 1022103 * 2 ^ 59
def prefixEnd_1022103 : Nat := 4983230072969 + 3 ^ 40 * 1022103 * 2
def baseEnd_1022103 : Nat := 155505219971116963262797

theorem tailTrace_1022103 : CollatzResearch.WordTrace tailWord_1022103 prefixEnd_1022103 155505219971116963262797 := by
  unfold tailWord_1022103
  simp only [CollatzResearch.WordTrace]
  refine ⟨37279159016102867139974963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24852772677401911426649975 37279159016102867139974963)
  ·
    refine ⟨55918738524154300709962445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37279159016102867139974963 55918738524154300709962445)
    ·
      refine ⟨20969526946557862766235917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55918738524154300709962445 20969526946557862766235917)
      ·
        refine ⟨7863572604959198537338469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20969526946557862766235917 7863572604959198537338469)
        ·
          refine ⟨1474419863429849725750963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7863572604959198537338469 1474419863429849725750963)
          ·
            refine ⟨2211629795144774588626445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474419863429849725750963 2211629795144774588626445)
            ·
              refine ⟨829361173179290470734917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2211629795144774588626445 829361173179290470734917)
              ·
                refine ⟨155505219971116963262797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829361173179290470734917 155505219971116963262797)
                ·
                  rfl

theorem cell20_1022103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 4].length) (baseStart_1022103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022103 prefixEnd_1022103 := by exact prefixLift 1022103
  have htrace : WordTrace (prefixWord ++ tailWord_1022103) baseStart_1022103 baseEnd_1022103 := by
    simpa [prefixWord, tailWord_1022103, baseEnd_1022103] using wordTrace_append hprefix tailTrace_1022103
  have hstable : (prefixWord ++ tailWord_1022103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022103).length < 2 ^ (prefixWord ++ tailWord_1022103).sum := by decide
  have hdescent : baseEnd_1022103 < baseStart_1022103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022138 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1022138 : Nat := 118140960795 + 1022138 * 2 ^ 59
def prefixEnd_1022138 : Nat := 4983230072969 + 3 ^ 40 * 1022138 * 2
def baseEnd_1022138 : Nat := 466531634867046323621581

theorem tailTrace_1022138 : CollatzResearch.WordTrace tailWord_1022138 prefixEnd_1022138 466531634867046323621581 := by
  unfold tailWord_1022138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320108892744017029374767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24853623713984045411666045 9320108892744017029374767)
  ·
    refine ⟨13980163339116025544062151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9320108892744017029374767 13980163339116025544062151)
    ·
      refine ⟨20970245008674038316093227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13980163339116025544062151 20970245008674038316093227)
      ·
        refine ⟨31455367513011057474139841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20970245008674038316093227 31455367513011057474139841)
        ·
          refine ⟨23591525634758293105604881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31455367513011057474139841 23591525634758293105604881)
          ·
            refine ⟨17693644226068719829203661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23591525634758293105604881 17693644226068719829203661)
            ·
              refine ⟨6635116584775769935951373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17693644226068719829203661 6635116584775769935951373)
              ·
                refine ⟨2488168719290913725981765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6635116584775769935951373 2488168719290913725981765)
                ·
                  refine ⟨466531634867046323621581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488168719290913725981765 466531634867046323621581)
                  ·
                    rfl

theorem cell20_1022138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1022138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022138 prefixEnd_1022138 := by exact prefixLift 1022138
  have htrace : WordTrace (prefixWord ++ tailWord_1022138) baseStart_1022138 baseEnd_1022138 := by
    simpa [prefixWord, tailWord_1022138, baseEnd_1022138] using wordTrace_append hprefix tailTrace_1022138
  have hstable : (prefixWord ++ tailWord_1022138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022138).length < 2 ^ (prefixWord ++ tailWord_1022138).sum := by decide
  have hdescent : baseEnd_1022138 < baseStart_1022138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022162 : List Nat := [3, 2, 2, 2, 1, 3, 1, 6]
def baseStart_1022162 : Nat := 118140960795 + 1022162 * 2 ^ 59
def prefixEnd_1022162 : Nat := 4983230072969 + 3 ^ 40 * 1022162 * 2
def baseEnd_1022162 : Nat := 155514196373669635607161

theorem tailTrace_1022162 : CollatzResearch.WordTrace tailWord_1022162 prefixEnd_1022162 155514196373669635607161 := by
  unfold tailWord_1022162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320327730722280054093185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24854207281926080144248493 9320327730722280054093185)
  ·
    refine ⟨6990245798041710040569889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9320327730722280054093185 6990245798041710040569889)
    ·
      refine ⟨5242684348531282530427417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6990245798041710040569889 5242684348531282530427417)
      ·
        refine ⟨3932013261398461897820563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5242684348531282530427417 3932013261398461897820563)
        ·
          refine ⟨5898019892097692846730845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932013261398461897820563 5898019892097692846730845)
          ·
            refine ⟨2211757459536634817524067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5898019892097692846730845 2211757459536634817524067)
            ·
              refine ⟨3317636189304952226286101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211757459536634817524067 3317636189304952226286101)
              ·
                refine ⟨155514196373669635607161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3317636189304952226286101 155514196373669635607161)
                ·
                  rfl

theorem cell20_1022162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_1022162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022162 prefixEnd_1022162 := by exact prefixLift 1022162
  have htrace : WordTrace (prefixWord ++ tailWord_1022162) baseStart_1022162 baseEnd_1022162 := by
    simpa [prefixWord, tailWord_1022162, baseEnd_1022162] using wordTrace_append hprefix tailTrace_1022162
  have hstable : (prefixWord ++ tailWord_1022162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022162).length < 2 ^ (prefixWord ++ tailWord_1022162).sum := by decide
  have hdescent : baseEnd_1022162 < baseStart_1022162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022179 : List Nat := [1, 1, 1, 8, 1, 2, 6]
def baseStart_1022179 : Nat := 118140960795 + 1022179 * 2 ^ 59
def prefixEnd_1022179 : Nat := 4983230072969 + 3 ^ 40 * 1022179 * 2
def baseEnd_1022179 : Nat := 51838927598248044806083

theorem tailTrace_1022179 : CollatzResearch.WordTrace tailWord_1022179 prefixEnd_1022179 51838927598248044806083 := by
  unfold tailWord_1022179
  simp only [CollatzResearch.WordTrace]
  refine ⟨37281930963827532119741591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24854620642551688079827727 37281930963827532119741591)
  ·
    refine ⟨55922896445741298179612387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37281930963827532119741591 55922896445741298179612387)
    ·
      refine ⟨83884344668611947269418581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55922896445741298179612387 83884344668611947269418581)
      ·
        refine ⟨983019664085296257063499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 83884344668611947269418581 983019664085296257063499)
        ·
          refine ⟨1474529496127944385595249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983019664085296257063499 1474529496127944385595249)
          ·
            refine ⟨1105897122095958289196437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474529496127944385595249 1105897122095958289196437)
            ·
              refine ⟨51838927598248044806083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1105897122095958289196437 51838927598248044806083)
              ·
                rfl

theorem cell20_1022179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 6].length) (baseStart_1022179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022179 prefixEnd_1022179 := by exact prefixLift 1022179
  have htrace : WordTrace (prefixWord ++ tailWord_1022179) baseStart_1022179 baseEnd_1022179 := by
    simpa [prefixWord, tailWord_1022179, baseEnd_1022179] using wordTrace_append hprefix tailTrace_1022179
  have hstable : (prefixWord ++ tailWord_1022179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022179).length < 2 ^ (prefixWord ++ tailWord_1022179).sum := by decide
  have hdescent : baseEnd_1022179 < baseStart_1022179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022189 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 4]
def baseStart_1022189 : Nat := 118140960795 + 1022189 * 2 ^ 59
def prefixEnd_1022189 : Nat := 4983230072969 + 3 ^ 40 * 1022189 * 2
def baseEnd_1022189 : Nat := 466554912656716812921373

theorem tailTrace_1022189 : CollatzResearch.WordTrace tailWord_1022189 prefixEnd_1022189 466554912656716812921373 := by
  unfold tailWord_1022189
  simp only [CollatzResearch.WordTrace]
  refine ⟨37282295693791303827605621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24854863795860869218403747 37282295693791303827605621)
  ·
    refine ⟨3495215221292934733838027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37282295693791303827605621 3495215221292934733838027)
    ·
      refine ⟨5242822831939402100757041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495215221292934733838027 5242822831939402100757041)
      ·
        refine ⟨3932117123954551575567781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5242822831939402100757041 3932117123954551575567781)
        ·
          refine ⟨737271960741478420418959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3932117123954551575567781 737271960741478420418959)
          ·
            refine ⟨1105907941112217630628439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737271960741478420418959 1105907941112217630628439)
            ·
              refine ⟨1658861911668326445942659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105907941112217630628439 1658861911668326445942659)
              ·
                refine ⟨2488292867502489668913989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658861911668326445942659 2488292867502489668913989)
                ·
                  refine ⟨466554912656716812921373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488292867502489668913989 466554912656716812921373)
                  ·
                    rfl

theorem cell20_1022189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_1022189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022189 prefixEnd_1022189 := by exact prefixLift 1022189
  have htrace : WordTrace (prefixWord ++ tailWord_1022189) baseStart_1022189 baseEnd_1022189 := by
    simpa [prefixWord, tailWord_1022189, baseEnd_1022189] using wordTrace_append hprefix tailTrace_1022189
  have hstable : (prefixWord ++ tailWord_1022189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022189).length < 2 ^ (prefixWord ++ tailWord_1022189).sum := by decide
  have hdescent : baseEnd_1022189 < baseStart_1022189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022193 : List Nat := [1, 2, 2, 2, 2, 1, 2, 6, 2]
def baseStart_1022193 : Nat := 118140960795 + 1022193 * 2 ^ 59
def prefixEnd_1022193 : Nat := 4983230072969 + 3 ^ 40 * 1022193 * 2
def baseEnd_1022193 : Nat := 466556738365710576788023

theorem tailTrace_1022193 : CollatzResearch.WordTrace tailWord_1022193 prefixEnd_1022193 466556738365710576788023 := by
  unfold tailWord_1022193
  simp only [CollatzResearch.WordTrace]
  refine ⟨37282441585776812510751233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24854961057184541673834155 37282441585776812510751233)
  ·
    refine ⟨27961831189332609383063425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37282441585776812510751233 27961831189332609383063425)
    ·
      refine ⟨20971373391999457037297569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27961831189332609383063425 20971373391999457037297569)
      ·
        refine ⟨15728530043999592777973177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20971373391999457037297569 15728530043999592777973177)
        ·
          refine ⟨11796397532999694583479883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15728530043999592777973177 11796397532999694583479883)
          ·
            refine ⟨17694596299499541875219825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796397532999694583479883 17694596299499541875219825)
            ·
              refine ⟨13270947224624656406414869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17694596299499541875219825 13270947224624656406414869)
              ·
                refine ⟨622075651154280769050697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13270947224624656406414869 622075651154280769050697)
                ·
                  refine ⟨466556738365710576788023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622075651154280769050697 466556738365710576788023)
                  ·
                    rfl

theorem cell20_1022193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_1022193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022193 prefixEnd_1022193 := by exact prefixLift 1022193
  have htrace : WordTrace (prefixWord ++ tailWord_1022193) baseStart_1022193 baseEnd_1022193 := by
    simpa [prefixWord, tailWord_1022193, baseEnd_1022193] using wordTrace_append hprefix tailTrace_1022193
  have hstable : (prefixWord ++ tailWord_1022193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022193).length < 2 ^ (prefixWord ++ tailWord_1022193).sum := by decide
  have hdescent : baseEnd_1022193 < baseStart_1022193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022207 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 3]
def baseStart_1022207 : Nat := 118140960795 + 1022207 * 2 ^ 59
def prefixEnd_1022207 : Nat := 4983230072969 + 3 ^ 40 * 1022207 * 2
def baseEnd_1022207 : Nat := 466563128347188750321299

theorem tailTrace_1022207 : CollatzResearch.WordTrace tailWord_1022207 prefixEnd_1022207 466563128347188750321299 := by
  unfold tailWord_1022207
  simp only [CollatzResearch.WordTrace]
  refine ⟨37282952207726092901760875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24855301471817395267840583 37282952207726092901760875)
  ·
    refine ⟨55924428311589139352641313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37282952207726092901760875 55924428311589139352641313)
    ·
      refine ⟨41943321233691854514480985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55924428311589139352641313 41943321233691854514480985)
      ·
        refine ⟨31457490925268890885860739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41943321233691854514480985 31457490925268890885860739)
        ·
          refine ⟨47186236387903336328791109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31457490925268890885860739 47186236387903336328791109)
          ·
            refine ⟨8847419322731875561648333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47186236387903336328791109 8847419322731875561648333)
            ·
              refine ⟨3317782246024453335618125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8847419322731875561648333 3317782246024453335618125)
              ·
                refine ⟨1244168342259170000856797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3317782246024453335618125 1244168342259170000856797)
                ·
                  refine ⟨466563128347188750321299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244168342259170000856797 466563128347188750321299)
                  ·
                    rfl

theorem cell20_1022207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 3].length) (baseStart_1022207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022207 prefixEnd_1022207 := by exact prefixLift 1022207
  have htrace : WordTrace (prefixWord ++ tailWord_1022207) baseStart_1022207 baseEnd_1022207 := by
    simpa [prefixWord, tailWord_1022207, baseEnd_1022207] using wordTrace_append hprefix tailTrace_1022207
  have hstable : (prefixWord ++ tailWord_1022207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022207).length < 2 ^ (prefixWord ++ tailWord_1022207).sum := by decide
  have hdescent : baseEnd_1022207 < baseStart_1022207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022307 : List Nat := [1, 1, 1, 5, 2, 1, 1, 6, 2]
def baseStart_1022307 : Nat := 118140960795 + 1022307 * 2 ^ 59
def prefixEnd_1022307 : Nat := 4983230072969 + 3 ^ 40 * 1022307 * 2
def baseEnd_1022307 : Nat := 466608771072032846987557

theorem tailTrace_1022307 : CollatzResearch.WordTrace tailWord_1022307 prefixEnd_1022307 466608771072032846987557 := by
  unfold tailWord_1022307
  simp only [CollatzResearch.WordTrace]
  refine ⟨37286599507363809980401175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24857733004909206653600783 37286599507363809980401175)
  ·
    refine ⟨55929899261045714970601763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37286599507363809980401175 55929899261045714970601763)
    ·
      refine ⟨83894848891568572455902645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55929899261045714970601763 83894848891568572455902645)
      ·
        refine ⟨7865142083584553667740873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83894848891568572455902645 7865142083584553667740873)
        ·
          refine ⟨5898856562688415250805655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7865142083584553667740873 5898856562688415250805655)
          ·
            refine ⟨8848284844032622876208483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5898856562688415250805655 8848284844032622876208483)
            ·
              refine ⟨13272427266048934314312725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8848284844032622876208483 13272427266048934314312725)
              ·
                refine ⟨622145028096043795983409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13272427266048934314312725 622145028096043795983409)
                ·
                  refine ⟨466608771072032846987557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622145028096043795983409 466608771072032846987557)
                  ·
                    rfl

theorem cell20_1022307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 2].length) (baseStart_1022307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022307 prefixEnd_1022307 := by exact prefixLift 1022307
  have htrace : WordTrace (prefixWord ++ tailWord_1022307) baseStart_1022307 baseEnd_1022307 := by
    simpa [prefixWord, tailWord_1022307, baseEnd_1022307] using wordTrace_append hprefix tailTrace_1022307
  have hstable : (prefixWord ++ tailWord_1022307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022307).length < 2 ^ (prefixWord ++ tailWord_1022307).sum := by decide
  have hdescent : baseEnd_1022307 < baseStart_1022307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022369 : List Nat := [1, 2, 3, 5, 1, 1, 2, 5]
def baseStart_1022369 : Nat := 118140960795 + 1022369 * 2 ^ 59
def prefixEnd_1022369 : Nat := 4983230072969 + 3 ^ 40 * 1022369 * 2
def baseEnd_1022369 : Nat := 155545689853812062306879

theorem tailTrace_1022369 : CollatzResearch.WordTrace tailWord_1022369 prefixEnd_1022369 155545689853812062306879 := by
  unfold tailWord_1022369
  simp only [CollatzResearch.WordTrace]
  refine ⟨37288860833139194569158161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24859240555426129712772107 37288860833139194569158161)
  ·
    refine ⟨27966645624854395926868621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37288860833139194569158161 27966645624854395926868621)
    ·
      refine ⟨10487492109320398472575733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27966645624854395926868621 10487492109320398472575733)
      ·
        refine ⟨983202385248787356803975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10487492109320398472575733 983202385248787356803975)
        ·
          refine ⟨1474803577873181035205963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983202385248787356803975 1474803577873181035205963)
          ·
            refine ⟨2212205366809771552808945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474803577873181035205963 2212205366809771552808945)
            ·
              refine ⟨1659154025107328664606709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212205366809771552808945 1659154025107328664606709)
              ·
                refine ⟨155545689853812062306879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1659154025107328664606709 155545689853812062306879)
                ·
                  rfl

theorem cell20_1022369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 5].length) (baseStart_1022369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022369 prefixEnd_1022369 := by exact prefixLift 1022369
  have htrace : WordTrace (prefixWord ++ tailWord_1022369) baseStart_1022369 baseEnd_1022369 := by
    simpa [prefixWord, tailWord_1022369, baseEnd_1022369] using wordTrace_append hprefix tailTrace_1022369
  have hstable : (prefixWord ++ tailWord_1022369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022369).length < 2 ^ (prefixWord ++ tailWord_1022369).sum := by decide
  have hdescent : baseEnd_1022369 < baseStart_1022369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022373 : List Nat := [1, 3, 1, 2, 1, 1, 6, 5]
def baseStart_1022373 : Nat := 118140960795 + 1022373 * 2 ^ 59
def prefixEnd_1022373 : Nat := 4983230072969 + 3 ^ 40 * 1022373 * 2
def baseEnd_1022373 : Nat := 155546298423476650262429

theorem tailTrace_1022373 : CollatzResearch.WordTrace tailWord_1022373 prefixEnd_1022373 155546298423476650262429 := by
  unfold tailWord_1022373
  simp only [CollatzResearch.WordTrace]
  refine ⟨37289006725124703252303773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24859337816749802168202515 37289006725124703252303773)
  ·
    refine ⟨13983377521921763719613915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37289006725124703252303773 13983377521921763719613915)
    ·
      refine ⟨20975066282882645579420873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13983377521921763719613915 20975066282882645579420873)
      ·
        refine ⟨15731299712161984184565655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20975066282882645579420873 15731299712161984184565655)
        ·
          refine ⟨23596949568242976276848483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15731299712161984184565655 23596949568242976276848483)
          ·
            refine ⟨35395424352364464415272725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23596949568242976276848483 35395424352364464415272725)
            ·
              refine ⟨1659160516517084269465909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35395424352364464415272725 1659160516517084269465909)
              ·
                refine ⟨155546298423476650262429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1659160516517084269465909 155546298423476650262429)
                ·
                  rfl

theorem cell20_1022373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_1022373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022373 prefixEnd_1022373 := by exact prefixLift 1022373
  have htrace : WordTrace (prefixWord ++ tailWord_1022373) baseStart_1022373 baseEnd_1022373 := by
    simpa [prefixWord, tailWord_1022373, baseEnd_1022373] using wordTrace_append hprefix tailTrace_1022373
  have hstable : (prefixWord ++ tailWord_1022373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022373).length < 2 ^ (prefixWord ++ tailWord_1022373).sum := by decide
  have hdescent : baseEnd_1022373 < baseStart_1022373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022442 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_1022442 : Nat := 118140960795 + 1022442 * 2 ^ 59
def prefixEnd_1022442 : Nat := 4983230072969 + 3 ^ 40 * 1022442 * 2
def baseEnd_1022442 : Nat := 466670388750572377487005

theorem tailTrace_1022442 : CollatzResearch.WordTrace tailWord_1022442 prefixEnd_1022442 466670388750572377487005 := by
  unfold tailWord_1022442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9322880840468682009141395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24861015574583152024377053 9322880840468682009141395)
  ·
    refine ⟨13984321260703023013712093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9322880840468682009141395 13984321260703023013712093)
    ·
      refine ⟨5244120472763633630142035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13984321260703023013712093 5244120472763633630142035)
      ·
        refine ⟨7866180709145450445213053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5244120472763633630142035 7866180709145450445213053)
        ·
          refine ⟨2949817765929543916954895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7866180709145450445213053 2949817765929543916954895)
          ·
            refine ⟨4424726648894315875432343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949817765929543916954895 4424726648894315875432343)
            ·
              refine ⟨6637089973341473813148515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424726648894315875432343 6637089973341473813148515)
              ·
                refine ⟨9955634960012210719722773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637089973341473813148515 9955634960012210719722773)
                ·
                  refine ⟨466670388750572377487005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9955634960012210719722773 466670388750572377487005)
                  ·
                    rfl

theorem cell20_1022442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_1022442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022442 prefixEnd_1022442 := by exact prefixLift 1022442
  have htrace : WordTrace (prefixWord ++ tailWord_1022442) baseStart_1022442 baseEnd_1022442 := by
    simpa [prefixWord, tailWord_1022442, baseEnd_1022442] using wordTrace_append hprefix tailTrace_1022442
  have hstable : (prefixWord ++ tailWord_1022442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022442).length < 2 ^ (prefixWord ++ tailWord_1022442).sum := by decide
  have hdescent : baseEnd_1022442 < baseStart_1022442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022445 : List Nat := [1, 5, 1, 3, 1, 2, 3, 4]
def baseStart_1022445 : Nat := 118140960795 + 1022445 * 2 ^ 59
def prefixEnd_1022445 : Nat := 4983230072969 + 3 ^ 40 * 1022445 * 2
def baseEnd_1022445 : Nat := 155557252677439233462331

theorem tailTrace_1022445 : CollatzResearch.WordTrace tailWord_1022445 prefixEnd_1022445 155557252677439233462331 := by
  unfold tailWord_1022445
  simp only [CollatzResearch.WordTrace]
  refine ⟨37291632780863859548924789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24861088520575906365949859 37291632780863859548924789)
  ·
    refine ⟨3496090573205986832711699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37291632780863859548924789 3496090573205986832711699)
    ·
      refine ⟨5244135859808980249067549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3496090573205986832711699 5244135859808980249067549)
      ·
        refine ⟨1966550947428367593400331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5244135859808980249067549 1966550947428367593400331)
        ·
          refine ⟨2949826421142551390100497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966550947428367593400331 2949826421142551390100497)
          ·
            refine ⟨2212369815856913542575373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949826421142551390100497 2212369815856913542575373)
            ·
              refine ⟨829638680946342578465765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2212369815856913542575373 829638680946342578465765)
              ·
                refine ⟨155557252677439233462331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829638680946342578465765 155557252677439233462331)
                ·
                  rfl

theorem cell20_1022445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 4].length) (baseStart_1022445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022445 prefixEnd_1022445 := by exact prefixLift 1022445
  have htrace : WordTrace (prefixWord ++ tailWord_1022445) baseStart_1022445 baseEnd_1022445 := by
    simpa [prefixWord, tailWord_1022445, baseEnd_1022445] using wordTrace_append hprefix tailTrace_1022445
  have hstable : (prefixWord ++ tailWord_1022445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022445).length < 2 ^ (prefixWord ++ tailWord_1022445).sum := by decide
  have hdescent : baseEnd_1022445 < baseStart_1022445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022456 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_1022456 : Nat := 118140960795 + 1022456 * 2 ^ 59
def prefixEnd_1022456 : Nat := 4983230072969 + 3 ^ 40 * 1022456 * 2
def baseEnd_1022456 : Nat := 466676778732050551020281

theorem tailTrace_1022456 : CollatzResearch.WordTrace tailWord_1022456 prefixEnd_1022456 466676778732050551020281 := by
  unfold tailWord_1022456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18646016991912004213787611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24861355989216005618383481 18646016991912004213787611)
  ·
    refine ⟨27969025487868006320681417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18646016991912004213787611 27969025487868006320681417)
    ·
      refine ⟨20976769115901004740511063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27969025487868006320681417 20976769115901004740511063)
      ·
        refine ⟨31465153673851507110766595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20976769115901004740511063 31465153673851507110766595)
        ·
          refine ⟨47197730510777260666149893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31465153673851507110766595 47197730510777260666149893)
          ·
            refine ⟨8849574470770736374903105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47197730510777260666149893 8849574470770736374903105)
            ·
              refine ⟨6637180853078052281177329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8849574470770736374903105 6637180853078052281177329)
              ·
                refine ⟨4977885639808539210882997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6637180853078052281177329 4977885639808539210882997)
                ·
                  refine ⟨466676778732050551020281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4977885639808539210882997 466676778732050551020281)
                  ·
                    rfl

theorem cell20_1022456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_1022456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022456 prefixEnd_1022456 := by exact prefixLift 1022456
  have htrace : WordTrace (prefixWord ++ tailWord_1022456) baseStart_1022456 baseEnd_1022456 := by
    simpa [prefixWord, tailWord_1022456, baseEnd_1022456] using wordTrace_append hprefix tailTrace_1022456
  have hstable : (prefixWord ++ tailWord_1022456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022456).length < 2 ^ (prefixWord ++ tailWord_1022456).sum := by decide
  have hdescent : baseEnd_1022456 < baseStart_1022456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022463 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_1022463 : Nat := 118140960795 + 1022463 * 2 ^ 59
def prefixEnd_1022463 : Nat := 4983230072969 + 3 ^ 40 * 1022463 * 2
def baseEnd_1022463 : Nat := 466679973722789637786919

theorem tailTrace_1022463 : CollatzResearch.WordTrace tailWord_1022463 prefixEnd_1022463 466679973722789637786919 := by
  unfold tailWord_1022463
  simp only [CollatzResearch.WordTrace]
  refine ⟨37292289294798648623080043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24861526196532432415386695 37292289294798648623080043)
  ·
    refine ⟨55938433942197972934620065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37292289294798648623080043 55938433942197972934620065)
    ·
      refine ⟨41953825456648479700965049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55938433942197972934620065 41953825456648479700965049)
      ·
        refine ⟨31465369092486359775723787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41953825456648479700965049 31465369092486359775723787)
        ·
          refine ⟨47198053638729539663585681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31465369092486359775723787 47198053638729539663585681)
          ·
            refine ⟨35398540229047154747689261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47198053638729539663585681 35398540229047154747689261)
            ·
              refine ⟨13274452585892683030383473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35398540229047154747689261 13274452585892683030383473)
              ·
                refine ⟨9955839439419512272787605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13274452585892683030383473 9955839439419512272787605)
                ·
                  refine ⟨466679973722789637786919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9955839439419512272787605 466679973722789637786919)
                  ·
                    rfl

theorem cell20_1022463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_1022463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022463 prefixEnd_1022463 := by exact prefixLift 1022463
  have htrace : WordTrace (prefixWord ++ tailWord_1022463) baseStart_1022463 baseEnd_1022463 := by
    simpa [prefixWord, tailWord_1022463, baseEnd_1022463] using wordTrace_append hprefix tailTrace_1022463
  have hstable : (prefixWord ++ tailWord_1022463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022463).length < 2 ^ (prefixWord ++ tailWord_1022463).sum := by decide
  have hdescent : baseEnd_1022463 < baseStart_1022463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022500 : List Nat := [2, 3, 1, 5, 1, 2, 2, 4]
def baseStart_1022500 : Nat := 118140960795 + 1022500 * 2 ^ 59
def prefixEnd_1022500 : Nat := 4983230072969 + 3 ^ 40 * 1022500 * 2
def baseEnd_1022500 : Nat := 155565620510327317851145

theorem tailTrace_1022500 : CollatzResearch.WordTrace tailWord_1022500 prefixEnd_1022500 155565620510327317851145 := by
  unfold tailWord_1022500
  simp only [CollatzResearch.WordTrace]
  refine ⟨18646819397832301971088477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24862425863776402628117969 18646819397832301971088477)
  ·
    refine ⟨6992557274187113239158179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18646819397832301971088477 6992557274187113239158179)
    ·
      refine ⟨10488835911280669858737269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6992557274187113239158179 10488835911280669858737269)
      ·
        refine ⟨983328366682562799256619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10488835911280669858737269 983328366682562799256619)
        ·
          refine ⟨1474992550023844198884929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983328366682562799256619 1474992550023844198884929)
          ·
            refine ⟨1106244412517883149163697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474992550023844198884929 1106244412517883149163697)
            ·
              refine ⟨829683309388412361872773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106244412517883149163697 829683309388412361872773)
              ·
                refine ⟨155565620510327317851145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829683309388412361872773 155565620510327317851145)
                ·
                  rfl

theorem cell20_1022500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_1022500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022500 prefixEnd_1022500 := by exact prefixLift 1022500
  have htrace : WordTrace (prefixWord ++ tailWord_1022500) baseStart_1022500 baseEnd_1022500 := by
    simpa [prefixWord, tailWord_1022500, baseEnd_1022500] using wordTrace_append hprefix tailTrace_1022500
  have hstable : (prefixWord ++ tailWord_1022500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022500).length < 2 ^ (prefixWord ++ tailWord_1022500).sum := by decide
  have hdescent : baseEnd_1022500 < baseStart_1022500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022504 : List Nat := [2, 1, 5, 2, 1, 2, 1, 6]
def baseStart_1022504 : Nat := 118140960795 + 1022504 * 2 ^ 59
def prefixEnd_1022504 : Nat := 4983230072969 + 3 ^ 40 * 1022504 * 2
def baseEnd_1022504 : Nat := 155566229079991905806695

theorem tailTrace_1022504 : CollatzResearch.WordTrace tailWord_1022504 prefixEnd_1022504 155566229079991905806695 := by
  unfold tailWord_1022504
  simp only [CollatzResearch.WordTrace]
  refine ⟨18646892343825056312661283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24862523125100075083548377 18646892343825056312661283)
  ·
    refine ⟨27970338515737584468991925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18646892343825056312661283 27970338515737584468991925)
    ·
      refine ⟨2622219235850398543967993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27970338515737584468991925 2622219235850398543967993)
      ·
        refine ⟨1966664426887798907975995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2622219235850398543967993 1966664426887798907975995)
        ·
          refine ⟨2949996640331698361963993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966664426887798907975995 2949996640331698361963993)
          ·
            refine ⟨2212497480248773771472995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949996640331698361963993 2212497480248773771472995)
            ·
              refine ⟨3318746220373160657209493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2212497480248773771472995 3318746220373160657209493)
              ·
                refine ⟨155566229079991905806695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3318746220373160657209493 155566229079991905806695)
                ·
                  rfl

theorem cell20_1022504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_1022504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022504 prefixEnd_1022504 := by exact prefixLift 1022504
  have htrace : WordTrace (prefixWord ++ tailWord_1022504) baseStart_1022504 baseEnd_1022504 := by
    simpa [prefixWord, tailWord_1022504, baseEnd_1022504] using wordTrace_append hprefix tailTrace_1022504
  have hstable : (prefixWord ++ tailWord_1022504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022504).length < 2 ^ (prefixWord ++ tailWord_1022504).sum := by decide
  have hdescent : baseEnd_1022504 < baseStart_1022504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022510 : List Nat := [4, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_1022510 : Nat := 118140960795 + 1022510 * 2 ^ 59
def prefixEnd_1022510 : Nat := 4983230072969 + 3 ^ 40 * 1022510 * 2
def baseEnd_1022510 : Nat := 466701425803466363220061

theorem tailTrace_1022510 : CollatzResearch.WordTrace tailWord_1022510 prefixEnd_1022510 466701425803466363220061 := by
  unfold tailWord_1022510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4661750440703546956255123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24862669017085583766693989 4661750440703546956255123)
  ·
    refine ⟨6992625661055320434382685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4661750440703546956255123 6992625661055320434382685)
    ·
      refine ⟨2622234622895745162893507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6992625661055320434382685 2622234622895745162893507)
      ·
        refine ⟨3933351934343617744340261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622234622895745162893507 3933351934343617744340261)
        ·
          refine ⟨737503487689428327063799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3933351934343617744340261 737503487689428327063799)
          ·
            refine ⟨1106255231534142490595699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737503487689428327063799 1106255231534142490595699)
            ·
              refine ⟨1659382847301213735893549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106255231534142490595699 1659382847301213735893549)
              ·
                refine ⟨622268567737955150960081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1659382847301213735893549 622268567737955150960081)
                ·
                  refine ⟨466701425803466363220061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622268567737955150960081 466701425803466363220061)
                  ·
                    rfl

theorem cell20_1022510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_1022510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022510 prefixEnd_1022510 := by exact prefixLift 1022510
  have htrace : WordTrace (prefixWord ++ tailWord_1022510) baseStart_1022510 baseEnd_1022510 := by
    simpa [prefixWord, tailWord_1022510, baseEnd_1022510] using wordTrace_append hprefix tailTrace_1022510
  have hstable : (prefixWord ++ tailWord_1022510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022510).length < 2 ^ (prefixWord ++ tailWord_1022510).sum := by decide
  have hdescent : baseEnd_1022510 < baseStart_1022510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022525 : List Nat := [1, 4, 1, 3, 2, 1, 8]
def baseStart_1022525 : Nat := 118140960795 + 1022525 * 2 ^ 59
def prefixEnd_1022525 : Nat := 4983230072969 + 3 ^ 40 * 1022525 * 2
def baseEnd_1022525 : Nat := 51856474690243664191111

theorem tailTrace_1022525 : CollatzResearch.WordTrace tailWord_1022525 prefixEnd_1022525 51856474690243664191111 := by
  unfold tailWord_1022525
  simp only [CollatzResearch.WordTrace]
  refine ⟨37294550620574033211837029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24863033747049355474558019 37294550620574033211837029)
  ·
    refine ⟨6992728241357631227219443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37294550620574033211837029 6992728241357631227219443)
    ·
      refine ⟨10489092362036446840829165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6992728241357631227219443 10489092362036446840829165)
      ·
        refine ⟨3933409635763667565310937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10489092362036446840829165 3933409635763667565310937)
        ·
          refine ⟨2950057226822750673983203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3933409635763667565310937 2950057226822750673983203)
          ·
            refine ⟨4425085840234126010974805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950057226822750673983203 4425085840234126010974805)
            ·
              refine ⟨51856474690243664191111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4425085840234126010974805 51856474690243664191111)
              ·
                rfl

theorem cell20_1022525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 8].length) (baseStart_1022525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022525 prefixEnd_1022525 := by exact prefixLift 1022525
  have htrace : WordTrace (prefixWord ++ tailWord_1022525) baseStart_1022525 baseEnd_1022525 := by
    simpa [prefixWord, tailWord_1022525, baseEnd_1022525] using wordTrace_append hprefix tailTrace_1022525
  have hstable : (prefixWord ++ tailWord_1022525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022525).length < 2 ^ (prefixWord ++ tailWord_1022525).sum := by decide
  have hdescent : baseEnd_1022525 < baseStart_1022525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022535 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 4]
def baseStart_1022535 : Nat := 118140960795 + 1022535 * 2 ^ 59
def prefixEnd_1022535 : Nat := 4983230072969 + 3 ^ 40 * 1022535 * 2
def baseEnd_1022535 : Nat := 466712836484677387386625

theorem tailTrace_1022535 : CollatzResearch.WordTrace tailWord_1022535 prefixEnd_1022535 466712836484677387386625 := by
  unfold tailWord_1022535
  simp only [CollatzResearch.WordTrace]
  refine ⟨37294915350537804919701059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24863276900358536613134039 37294915350537804919701059)
  ·
    refine ⟨55942373025806707379551589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37294915350537804919701059 55942373025806707379551589)
    ·
      refine ⟨10489194942338757633665923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55942373025806707379551589 10489194942338757633665923)
      ·
        refine ⟨15733792413508136450498885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10489194942338757633665923 15733792413508136450498885)
        ·
          refine ⟨2950086077532775584468541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15733792413508136450498885 2950086077532775584468541)
          ·
            refine ⟨1106282279074790844175703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2950086077532775584468541 1106282279074790844175703)
            ·
              refine ⟨1659423418612186266263555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106282279074790844175703 1659423418612186266263555)
              ·
                refine ⟨2489135127918279399395333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659423418612186266263555 2489135127918279399395333)
                ·
                  refine ⟨466712836484677387386625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2489135127918279399395333 466712836484677387386625)
                  ·
                    rfl

theorem cell20_1022535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 4].length) (baseStart_1022535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022535 prefixEnd_1022535 := by exact prefixLift 1022535
  have htrace : WordTrace (prefixWord ++ tailWord_1022535) baseStart_1022535 baseEnd_1022535 := by
    simpa [prefixWord, tailWord_1022535, baseEnd_1022535] using wordTrace_append hprefix tailTrace_1022535
  have hstable : (prefixWord ++ tailWord_1022535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022535).length < 2 ^ (prefixWord ++ tailWord_1022535).sum := by decide
  have hdescent : baseEnd_1022535 < baseStart_1022535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022669 : List Nat := [1, 6, 2, 1, 3, 1, 2, 4]
def baseStart_1022669 : Nat := 118140960795 + 1022669 * 2 ^ 59
def prefixEnd_1022669 : Nat := 4983230072969 + 3 ^ 40 * 1022669 * 2
def baseEnd_1022669 : Nat := 155591332578656158973137

theorem tailTrace_1022669 : CollatzResearch.WordTrace tailWord_1022669 prefixEnd_1022669 155591332578656158973137 := by
  unfold tailWord_1022669
  simp only [CollatzResearch.WordTrace]
  refine ⟨37299802732052345805079061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24866535154701563870052707 37299802732052345805079061)
  ·
    refine ⟨1748428253064953709613081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37299802732052345805079061 1748428253064953709613081)
    ·
      refine ⟨1311321189798715282209811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1748428253064953709613081 1311321189798715282209811)
      ·
        refine ⟨1966981784698072923314717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311321189798715282209811 1966981784698072923314717)
        ·
          refine ⟨737618169261777346243019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1966981784698072923314717 737618169261777346243019)
          ·
            refine ⟨1106427253892666019364529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737618169261777346243019 1106427253892666019364529)
            ·
              refine ⟨829820440419499514523397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106427253892666019364529 829820440419499514523397)
              ·
                refine ⟨155591332578656158973137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829820440419499514523397 155591332578656158973137)
                ·
                  rfl

theorem cell20_1022669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 4].length) (baseStart_1022669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022669 prefixEnd_1022669 := by exact prefixLift 1022669
  have htrace : WordTrace (prefixWord ++ tailWord_1022669) baseStart_1022669 baseEnd_1022669 := by
    simpa [prefixWord, tailWord_1022669, baseEnd_1022669] using wordTrace_append hprefix tailTrace_1022669
  have hstable : (prefixWord ++ tailWord_1022669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022669).length < 2 ^ (prefixWord ++ tailWord_1022669).sum := by decide
  have hdescent : baseEnd_1022669 < baseStart_1022669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022670 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1022670 : Nat := 118140960795 + 1022670 * 2 ^ 59
def prefixEnd_1022670 : Nat := 4983230072969 + 3 ^ 40 * 1022670 * 2
def baseEnd_1022670 : Nat := 466774454163216917886073

theorem tailTrace_1022670 : CollatzResearch.WordTrace tailWord_1022670 prefixEnd_1022670 466774454163216917886073 := by
  unfold tailWord_1022670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662479900631090371983183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24866559470032481983910309 4662479900631090371983183)
  ·
    refine ⟨6993719850946635557974775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4662479900631090371983183 6993719850946635557974775)
    ·
      refine ⟨10490579776419953336962163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6993719850946635557974775 10490579776419953336962163)
      ·
        refine ⟨15735869664629930005443245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10490579776419953336962163 15735869664629930005443245)
        ·
          refine ⟨5900951124236223752041217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15735869664629930005443245 5900951124236223752041217)
          ·
            refine ⟨4425713343177167814030913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5900951124236223752041217 4425713343177167814030913)
            ·
              refine ⟨3319285007382875860523185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4425713343177167814030913 3319285007382875860523185)
              ·
                refine ⟨2489463755537156895392389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3319285007382875860523185 2489463755537156895392389)
                ·
                  refine ⟨466774454163216917886073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2489463755537156895392389 466774454163216917886073)
                  ·
                    rfl

theorem cell20_1022670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1022670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022670 prefixEnd_1022670 := by exact prefixLift 1022670
  have htrace : WordTrace (prefixWord ++ tailWord_1022670) baseStart_1022670 baseEnd_1022670 := by
    simpa [prefixWord, tailWord_1022670, baseEnd_1022670] using wordTrace_append hprefix tailTrace_1022670
  have hstable : (prefixWord ++ tailWord_1022670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022670).length < 2 ^ (prefixWord ++ tailWord_1022670).sum := by decide
  have hdescent : baseEnd_1022670 < baseStart_1022670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022687 : List Nat := [1, 1, 2, 3, 2, 3, 3, 3, 2]
def baseStart_1022687 : Nat := 118140960795 + 1022687 * 2 ^ 59
def prefixEnd_1022687 : Nat := 4983230072969 + 3 ^ 40 * 1022687 * 2
def baseEnd_1022687 : Nat := 466782213426440414319337

theorem tailTrace_1022687 : CollatzResearch.WordTrace tailWord_1022687 prefixEnd_1022687 466782213426440414319337 := by
  unfold tailWord_1022687
  simp only [CollatzResearch.WordTrace]
  refine ⟨37300459245987134879234315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24866972830658089919489543 37300459245987134879234315)
  ·
    refine ⟨55950688868980702318851473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37300459245987134879234315 55950688868980702318851473)
    ·
      refine ⟨41963016651735526739138605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55950688868980702318851473 41963016651735526739138605)
      ·
        refine ⟨15736131244400822527176977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41963016651735526739138605 15736131244400822527176977)
        ·
          refine ⟨11802098433300616895382733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15736131244400822527176977 11802098433300616895382733)
          ·
            refine ⟨4425786912487731335768525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11802098433300616895382733 4425786912487731335768525)
            ·
              refine ⟨1659670092182899250913197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4425786912487731335768525 1659670092182899250913197)
              ·
                refine ⟨622376284568587219092449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1659670092182899250913197 622376284568587219092449)
                ·
                  refine ⟨466782213426440414319337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622376284568587219092449 466782213426440414319337)
                  ·
                    rfl

theorem cell20_1022687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 2].length) (baseStart_1022687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022687 prefixEnd_1022687 := by exact prefixLift 1022687
  have htrace : WordTrace (prefixWord ++ tailWord_1022687) baseStart_1022687 baseEnd_1022687 := by
    simpa [prefixWord, tailWord_1022687, baseEnd_1022687] using wordTrace_append hprefix tailTrace_1022687
  have hstable : (prefixWord ++ tailWord_1022687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022687).length < 2 ^ (prefixWord ++ tailWord_1022687).sum := by decide
  have hdescent : baseEnd_1022687 < baseStart_1022687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022701 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1022701 : Nat := 118140960795 + 1022701 * 2 ^ 59
def prefixEnd_1022701 : Nat := 4983230072969 + 3 ^ 40 * 1022701 * 2
def baseEnd_1022701 : Nat := 466788603407918587852613

theorem tailTrace_1022701 : CollatzResearch.WordTrace tailWord_1022701 prefixEnd_1022701 466788603407918587852613 := by
  unfold tailWord_1022701
  simp only [CollatzResearch.WordTrace]
  refine ⟨37300969867936415270243957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24867313245290943513495971 37300969867936415270243957)
  ·
    refine ⟨3496965925119038931585371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37300969867936415270243957 3496965925119038931585371)
    ·
      refine ⟨5245448887678558397378057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3496965925119038931585371 5245448887678558397378057)
      ·
        refine ⟨3934086665758918798033543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5245448887678558397378057 3934086665758918798033543)
        ·
          refine ⟨5901129998638378197050315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3934086665758918798033543 5901129998638378197050315)
          ·
            refine ⟨8851694997957567295575473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5901129998638378197050315 8851694997957567295575473)
            ·
              refine ⟨6638771248468175471681605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8851694997957567295575473 6638771248468175471681605)
              ·
                refine ⟨1244769609087782900940301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6638771248468175471681605 1244769609087782900940301)
                ·
                  refine ⟨466788603407918587852613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244769609087782900940301 466788603407918587852613)
                  ·
                    rfl

theorem cell20_1022701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1022701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022701 prefixEnd_1022701 := by exact prefixLift 1022701
  have htrace : WordTrace (prefixWord ++ tailWord_1022701) baseStart_1022701 baseEnd_1022701 := by
    simpa [prefixWord, tailWord_1022701, baseEnd_1022701] using wordTrace_append hprefix tailTrace_1022701
  have hstable : (prefixWord ++ tailWord_1022701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022701).length < 2 ^ (prefixWord ++ tailWord_1022701).sum := by decide
  have hdescent : baseEnd_1022701 < baseStart_1022701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022718 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1022718 : Nat := 118140960795 + 1022718 * 2 ^ 59
def prefixEnd_1022718 : Nat := 4983230072969 + 3 ^ 40 * 1022718 * 2
def baseEnd_1022718 : Nat := 466796362671142084285877

theorem tailTrace_1022718 : CollatzResearch.WordTrace tailWord_1022718 prefixEnd_1022718 466796362671142084285877 := by
  unfold tailWord_1022718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662698738609353396701601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24867726605916551449075205 4662698738609353396701601)
  ·
    refine ⟨3497024053957015047526201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4662698738609353396701601 3497024053957015047526201)
    ·
      refine ⟨2622768040467761285644651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3497024053957015047526201 2622768040467761285644651)
      ·
        refine ⟨3934152060701641928466977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622768040467761285644651 3934152060701641928466977)
        ·
          refine ⟨2950614045526231446350233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3934152060701641928466977 2950614045526231446350233)
          ·
            refine ⟨2212960534144673584762675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2950614045526231446350233 2212960534144673584762675)
            ·
              refine ⟨3319440801217010377144013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2212960534144673584762675 3319440801217010377144013)
              ·
                refine ⟨1244790300456378891429005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3319440801217010377144013 1244790300456378891429005)
                ·
                  refine ⟨466796362671142084285877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244790300456378891429005 466796362671142084285877)
                  ·
                    rfl

theorem cell20_1022718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1022718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022718 prefixEnd_1022718 := by exact prefixLift 1022718
  have htrace : WordTrace (prefixWord ++ tailWord_1022718) baseStart_1022718 baseEnd_1022718 := by
    simpa [prefixWord, tailWord_1022718, baseEnd_1022718] using wordTrace_append hprefix tailTrace_1022718
  have hstable : (prefixWord ++ tailWord_1022718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022718).length < 2 ^ (prefixWord ++ tailWord_1022718).sum := by decide
  have hdescent : baseEnd_1022718 < baseStart_1022718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022729 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_1022729 : Nat := 118140960795 + 1022729 * 2 ^ 59
def prefixEnd_1022729 : Nat := 4983230072969 + 3 ^ 40 * 1022729 * 2
def baseEnd_1022729 : Nat := 466801383370874934919165

theorem tailTrace_1022729 : CollatzResearch.WordTrace tailWord_1022729 prefixEnd_1022729 466801383370874934919165 := by
  unfold tailWord_1022729
  simp only [CollatzResearch.WordTrace]
  refine ⟨37301991111834976052263241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24867994074556650701508827 37301991111834976052263241)
  ·
    refine ⟨27976493333876232039197431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37301991111834976052263241 27976493333876232039197431)
    ·
      refine ⟨41964740000814348058796147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27976493333876232039197431 41964740000814348058796147)
      ·
        refine ⟨62947110001221522088194221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41964740000814348058796147 62947110001221522088194221)
        ·
          refine ⟨23605166250458070783072833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62947110001221522088194221 23605166250458070783072833)
          ·
            refine ⟨17703874687843553087304625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23605166250458070783072833 17703874687843553087304625)
            ·
              refine ⟨13277906015882664815478469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17703874687843553087304625 13277906015882664815478469)
              ·
                refine ⟨2489607377977999652902213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13277906015882664815478469 2489607377977999652902213)
                ·
                  refine ⟨466801383370874934919165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2489607377977999652902213 466801383370874934919165)
                  ·
                    rfl

theorem cell20_1022729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_1022729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022729 prefixEnd_1022729 := by exact prefixLift 1022729
  have htrace : WordTrace (prefixWord ++ tailWord_1022729) baseStart_1022729 baseEnd_1022729 := by
    simpa [prefixWord, tailWord_1022729, baseEnd_1022729] using wordTrace_append hprefix tailTrace_1022729
  have hstable : (prefixWord ++ tailWord_1022729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022729).length < 2 ^ (prefixWord ++ tailWord_1022729).sum := by decide
  have hdescent : baseEnd_1022729 < baseStart_1022729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022756 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1022756 : Nat := 118140960795 + 1022756 * 2 ^ 59
def prefixEnd_1022756 : Nat := 4983230072969 + 3 ^ 40 * 1022756 * 2
def baseEnd_1022756 : Nat := 466813706906582841019055

theorem tailTrace_1022756 : CollatzResearch.WordTrace tailWord_1022756 prefixEnd_1022756 466813706906582841019055 := by
  unfold tailWord_1022756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18651487941368579831748061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24868650588491439775664081 18651487941368579831748061)
  ·
    refine ⟨6994307978013217436905523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18651487941368579831748061 6994307978013217436905523)
    ·
      refine ⟨10491461967019826155358285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6994307978013217436905523 10491461967019826155358285)
      ·
        refine ⟨3934298237632434808259357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10491461967019826155358285 3934298237632434808259357)
        ·
          refine ⟨1475361839112163053097259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3934298237632434808259357 1475361839112163053097259)
          ·
            refine ⟨2213042758668244579645889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475361839112163053097259 2213042758668244579645889)
            ·
              refine ⟨1659782069001183434734417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213042758668244579645889 1659782069001183434734417)
              ·
                refine ⟨1244836551750887576050813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1659782069001183434734417 1244836551750887576050813)
                ·
                  refine ⟨466813706906582841019055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244836551750887576050813 466813706906582841019055)
                  ·
                    rfl

theorem cell20_1022756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1022756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022756 prefixEnd_1022756 := by exact prefixLift 1022756
  have htrace : WordTrace (prefixWord ++ tailWord_1022756) baseStart_1022756 baseEnd_1022756 := by
    simpa [prefixWord, tailWord_1022756, baseEnd_1022756] using wordTrace_append hprefix tailTrace_1022756
  have hstable : (prefixWord ++ tailWord_1022756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022756).length < 2 ^ (prefixWord ++ tailWord_1022756).sum := by decide
  have hdescent : baseEnd_1022756 < baseStart_1022756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
