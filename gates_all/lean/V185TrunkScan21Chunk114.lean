import V185TrunkScan21Chunk113

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1385905 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 4]
def baseStart_1385905 : Nat := 118140960795 + 1385905 * 2 ^ 59
def prefixEnd_1385905 : Nat := 4983230072969 + 3 ^ 40 * 1385905 * 2
def baseEnd_1385905 : Nat := 316282402875335721783931

theorem tailTrace_1385905 : CollatzResearch.WordTrace tailWord_1385905 prefixEnd_1385905 316282402875335721783931 := by
  unfold tailWord_1385905
  simp only [CollatzResearch.WordTrace]
  refine ⟨50548108044110353574959169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33698738696073569049972779 50548108044110353574959169)
  ·
    refine ⟨37911081033082765181219377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50548108044110353574959169 37911081033082765181219377)
    ·
      refine ⟨28433310774812073885914533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37911081033082765181219377 28433310774812073885914533)
      ·
        refine ⟨5331245770277263853608975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28433310774812073885914533 5331245770277263853608975)
        ·
          refine ⟨7996868655415895780413463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331245770277263853608975 7996868655415895780413463)
          ·
            refine ⟨11995302983123843670620195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7996868655415895780413463 11995302983123843670620195)
            ·
              refine ⟨17992954474685765505930293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11995302983123843670620195 17992954474685765505930293)
              ·
                refine ⟨1686839482001790516180965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17992954474685765505930293 1686839482001790516180965)
                ·
                  refine ⟨316282402875335721783931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1686839482001790516180965 316282402875335721783931)
                  ·
                    rfl

theorem cell21_1385905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_1385905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1385905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1385905 prefixEnd_1385905 := by exact prefixLift 1385905
  have htrace : WordTrace (prefixWord ++ tailWord_1385905) baseStart_1385905 baseEnd_1385905 := by
    simpa [prefixWord, tailWord_1385905, baseEnd_1385905] using wordTrace_append hprefix tailTrace_1385905
  have hstable : (prefixWord ++ tailWord_1385905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385905).length < 2 ^ (prefixWord ++ tailWord_1385905).sum := by decide
  have hdescent : baseEnd_1385905 < baseStart_1385905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386026 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_1386026 : Nat := 118140960795 + 1386026 * 2 ^ 59
def prefixEnd_1386026 : Nat := 4983230072969 + 3 ^ 40 * 1386026 * 2
def baseEnd_1386026 : Nat := 316310016723866400267017

theorem tailTrace_1386026 : CollatzResearch.WordTrace tailWord_1386026 prefixEnd_1386026 316310016723866400267017 := by
  unfold tailWord_1386026
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638130319167997810028483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33701680851114660826742621 12638130319167997810028483)
  ·
    refine ⟨18957195478751996715042725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12638130319167997810028483 18957195478751996715042725)
    ·
      refine ⟨3554474152265999384070511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18957195478751996715042725 3554474152265999384070511)
      ·
        refine ⟨5331711228398999076105767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3554474152265999384070511 5331711228398999076105767)
        ·
          refine ⟨7997566842598498614158651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331711228398999076105767 7997566842598498614158651)
          ·
            refine ⟨11996350263897747921237977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7997566842598498614158651 11996350263897747921237977)
            ·
              refine ⟨8997262697923310940928483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11996350263897747921237977 8997262697923310940928483)
              ·
                refine ⟨13495894046884966411392725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8997262697923310940928483 13495894046884966411392725)
                ·
                  refine ⟨316310016723866400267017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13495894046884966411392725 316310016723866400267017)
                  ·
                    rfl

theorem cell21_1386026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_1386026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386026 prefixEnd_1386026 := by exact prefixLift 1386026
  have htrace : WordTrace (prefixWord ++ tailWord_1386026) baseStart_1386026 baseEnd_1386026 := by
    simpa [prefixWord, tailWord_1386026, baseEnd_1386026] using wordTrace_append hprefix tailTrace_1386026
  have hstable : (prefixWord ++ tailWord_1386026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386026).length < 2 ^ (prefixWord ++ tailWord_1386026).sum := by decide
  have hdescent : baseEnd_1386026 < baseStart_1386026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386060 : List Nat := [2, 2, 1, 3, 1, 3, 4, 2, 3]
def baseStart_1386060 : Nat := 118140960795 + 1386060 * 2 ^ 59
def prefixEnd_1386060 : Nat := 4983230072969 + 3 ^ 40 * 1386060 * 2
def baseEnd_1386060 : Nat := 316317775987089896700281

theorem tailTrace_1386060 : CollatzResearch.WordTrace tailWord_1386060 prefixEnd_1386060 316317775987089896700281 := by
  unfold tailWord_1386060
  simp only [CollatzResearch.WordTrace]
  refine ⟨25276880679274407523425817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33702507572365876697901089 25276880679274407523425817)
  ·
    refine ⟨18957660509455805642569363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25276880679274407523425817 18957660509455805642569363)
    ·
      refine ⟨28436490764183708463854045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18957660509455805642569363 28436490764183708463854045)
      ·
        refine ⟨10663684036568890673945267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28436490764183708463854045 10663684036568890673945267)
        ·
          refine ⟨15995526054853336010917901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10663684036568890673945267 15995526054853336010917901)
          ·
            refine ⟨5998322270570001004094213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15995526054853336010917901 5998322270570001004094213)
            ·
              refine ⟨1124685425731875188267665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5998322270570001004094213 1124685425731875188267665)
              ·
                refine ⟨843514069298906391200749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124685425731875188267665 843514069298906391200749)
                ·
                  refine ⟨316317775987089896700281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843514069298906391200749 316317775987089896700281)
                  ·
                    rfl

theorem cell21_1386060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_1386060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386060 prefixEnd_1386060 := by exact prefixLift 1386060
  have htrace : WordTrace (prefixWord ++ tailWord_1386060) baseStart_1386060 baseEnd_1386060 := by
    simpa [prefixWord, tailWord_1386060, baseEnd_1386060] using wordTrace_append hprefix tailTrace_1386060
  have hstable : (prefixWord ++ tailWord_1386060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386060).length < 2 ^ (prefixWord ++ tailWord_1386060).sum := by decide
  have hdescent : baseEnd_1386060 < baseStart_1386060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386071 : List Nat := [1, 1, 3, 2, 2, 3, 3, 6]
def baseStart_1386071 : Nat := 118140960795 + 1386071 * 2 ^ 59
def prefixEnd_1386071 : Nat := 4983230072969 + 3 ^ 40 * 1386071 * 2
def baseEnd_1386071 : Nat := 105440095445652107338975

theorem tailTrace_1386071 : CollatzResearch.WordTrace tailWord_1386071 prefixEnd_1386071 105440095445652107338975 := by
  unfold tailWord_1386071
  simp only [CollatzResearch.WordTrace]
  refine ⟨50554162561508963925502067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33702775041005975950334711 50554162561508963925502067)
  ·
    refine ⟨75831243842263445888253101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50554162561508963925502067 75831243842263445888253101)
    ·
      refine ⟨28436716440848792208094913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75831243842263445888253101 28436716440848792208094913)
      ·
        refine ⟨21327537330636594156071185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28436716440848792208094913 21327537330636594156071185)
        ·
          refine ⟨15995652997977445617053389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21327537330636594156071185 15995652997977445617053389)
          ·
            refine ⟨5998369874241542106395021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15995652997977445617053389 5998369874241542106395021)
            ·
              refine ⟨2249388702840578289898133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5998369874241542106395021 2249388702840578289898133)
              ·
                refine ⟨105440095445652107338975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2249388702840578289898133 105440095445652107338975)
                ·
                  rfl

theorem cell21_1386071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 6].length) (baseStart_1386071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386071 prefixEnd_1386071 := by exact prefixLift 1386071
  have htrace : WordTrace (prefixWord ++ tailWord_1386071) baseStart_1386071 baseEnd_1386071 := by
    simpa [prefixWord, tailWord_1386071, baseEnd_1386071] using wordTrace_append hprefix tailTrace_1386071
  have hstable : (prefixWord ++ tailWord_1386071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386071).length < 2 ^ (prefixWord ++ tailWord_1386071).sum := by decide
  have hdescent : baseEnd_1386071 < baseStart_1386071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386119 : List Nat := [1, 1, 4, 2, 1, 3, 2, 4, 3]
def baseStart_1386119 : Nat := 118140960795 + 1386119 * 2 ^ 59
def prefixEnd_1386119 : Nat := 4983230072969 + 3 ^ 40 * 1386119 * 2
def baseEnd_1386119 : Nat := 316331240590918905216827

theorem tailTrace_1386119 : CollatzResearch.WordTrace tailWord_1386119 prefixEnd_1386119 316331240590918905216827 := by
  unfold tailWord_1386119
  simp only [CollatzResearch.WordTrace]
  refine ⟨50555913265335068123249411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33703942176890045415499607 50555913265335068123249411)
  ·
    refine ⟨75833869898002602184874117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50555913265335068123249411 75833869898002602184874117)
    ·
      refine ⟨14218850605875487909663897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75833869898002602184874117 14218850605875487909663897)
      ·
        refine ⟨10664137954406615932247923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14218850605875487909663897 10664137954406615932247923)
        ·
          refine ⟨15996206931609923898371885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10664137954406615932247923 15996206931609923898371885)
          ·
            refine ⟨5998577599353721461889457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15996206931609923898371885 5998577599353721461889457)
            ·
              refine ⟨4498933199515291096417093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5998577599353721461889457 4498933199515291096417093)
              ·
                refine ⟨843549974909117080578205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4498933199515291096417093 843549974909117080578205)
                ·
                  refine ⟨316331240590918905216827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843549974909117080578205 316331240590918905216827)
                  ·
                    rfl

theorem cell21_1386119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 3].length) (baseStart_1386119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386119 prefixEnd_1386119 := by exact prefixLift 1386119
  have htrace : WordTrace (prefixWord ++ tailWord_1386119) baseStart_1386119 baseEnd_1386119 := by
    simpa [prefixWord, tailWord_1386119, baseEnd_1386119] using wordTrace_append hprefix tailTrace_1386119
  have hstable : (prefixWord ++ tailWord_1386119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386119).length < 2 ^ (prefixWord ++ tailWord_1386119).sum := by decide
  have hdescent : baseEnd_1386119 < baseStart_1386119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386268 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_1386268 : Nat := 118140960795 + 1386268 * 2 ^ 59
def prefixEnd_1386268 : Nat := 4983230072969 + 3 ^ 40 * 1386268 * 2
def baseEnd_1386268 : Nat := 316365244420927757233189

theorem tailTrace_1386268 : CollatzResearch.WordTrace tailWord_1386268 prefixEnd_1386268 316365244420927757233189 := by
  unfold tailWord_1386268
  simp only [CollatzResearch.WordTrace]
  refine ⟨25280673870897633285211729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33707565161196844380282305 25280673870897633285211729)
  ·
    refine ⟨18960505403173224963908797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25280673870897633285211729 18960505403173224963908797)
    ·
      refine ⟨7110189526189959361465799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18960505403173224963908797 7110189526189959361465799)
      ·
        refine ⟨10665284289284939042198699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7110189526189959361465799 10665284289284939042198699)
        ·
          refine ⟨15997926433927408563298049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10665284289284939042198699 15997926433927408563298049)
          ·
            refine ⟨11998444825445556422473537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15997926433927408563298049 11998444825445556422473537)
            ·
              refine ⟨8998833619084167316855153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11998444825445556422473537 8998833619084167316855153)
              ·
                refine ⟨6749125214313125487641365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8998833619084167316855153 6749125214313125487641365)
                ·
                  refine ⟨316365244420927757233189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6749125214313125487641365 316365244420927757233189)
                  ·
                    rfl

theorem cell21_1386268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_1386268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386268 prefixEnd_1386268 := by exact prefixLift 1386268
  have htrace : WordTrace (prefixWord ++ tailWord_1386268) baseStart_1386268 baseEnd_1386268 := by
    simpa [prefixWord, tailWord_1386268, baseEnd_1386268] using wordTrace_append hprefix tailTrace_1386268
  have hstable : (prefixWord ++ tailWord_1386268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386268).length < 2 ^ (prefixWord ++ tailWord_1386268).sum := by decide
  have hdescent : baseEnd_1386268 < baseStart_1386268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386271 : List Nat := [1, 1, 2, 4, 2, 1, 4, 3, 3]
def baseStart_1386271 : Nat := 118140960795 + 1386271 * 2 ^ 59
def prefixEnd_1386271 : Nat := 4983230072969 + 3 ^ 40 * 1386271 * 2
def baseEnd_1386271 : Nat := 316365929061800418683183

theorem tailTrace_1386271 : CollatzResearch.WordTrace tailWord_1386271 prefixEnd_1386271 316365929061800418683183 := by
  unfold tailWord_1386271
  simp only [CollatzResearch.WordTrace]
  refine ⟨50561457160784398082782667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33707638107189598721855111 50561457160784398082782667)
  ·
    refine ⟨75842185741176597124174001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50561457160784398082782667 75842185741176597124174001)
    ·
      refine ⟨56881639305882447843130501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75842185741176597124174001 56881639305882447843130501)
      ·
        refine ⟨10665307369852958970586969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56881639305882447843130501 10665307369852958970586969)
        ·
          refine ⟨7998980527389719227940227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10665307369852958970586969 7998980527389719227940227)
          ·
            refine ⟨11998470791084578841910341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7998980527389719227940227 11998470791084578841910341)
            ·
              refine ⟨2249713273328358532858189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11998470791084578841910341 2249713273328358532858189)
              ·
                refine ⟨843642477498134449821821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2249713273328358532858189 843642477498134449821821)
                ·
                  refine ⟨316365929061800418683183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843642477498134449821821 316365929061800418683183)
                  ·
                    rfl

theorem cell21_1386271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 3].length) (baseStart_1386271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386271 prefixEnd_1386271 := by exact prefixLift 1386271
  have htrace : WordTrace (prefixWord ++ tailWord_1386271) baseStart_1386271 baseEnd_1386271 := by
    simpa [prefixWord, tailWord_1386271, baseEnd_1386271] using wordTrace_append hprefix tailTrace_1386271
  have hstable : (prefixWord ++ tailWord_1386271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386271).length < 2 ^ (prefixWord ++ tailWord_1386271).sum := by decide
  have hdescent : baseEnd_1386271 < baseStart_1386271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386313 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 5]
def baseStart_1386313 : Nat := 118140960795 + 1386313 * 2 ^ 59
def prefixEnd_1386313 : Nat := 4983230072969 + 3 ^ 40 * 1386313 * 2
def baseEnd_1386313 : Nat := 316375514034017678983097

theorem tailTrace_1386313 : CollatzResearch.WordTrace tailWord_1386313 prefixEnd_1386313 316375514034017678983097 := by
  unfold tailWord_1386313
  simp only [CollatzResearch.WordTrace]
  refine ⟨50562989026632239255811593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33708659351088159503874395 50562989026632239255811593)
  ·
    refine ⟨37922241769974179441858695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50562989026632239255811593 37922241769974179441858695)
    ·
      refine ⟨56883362654961269162788043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37922241769974179441858695 56883362654961269162788043)
      ·
        refine ⟨85325043982441903744182065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56883362654961269162788043 85325043982441903744182065)
        ·
          refine ⟨63993782986831427808136549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85325043982441903744182065 63993782986831427808136549)
          ·
            refine ⟨11998834310030892714025603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63993782986831427808136549 11998834310030892714025603)
            ·
              refine ⟨17998251465046339071038405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11998834310030892714025603 17998251465046339071038405)
              ·
                refine ⟨3374672149696188575819701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17998251465046339071038405 3374672149696188575819701)
                ·
                  refine ⟨316375514034017678983097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3374672149696188575819701 316375514034017678983097)
                  ·
                    rfl

theorem cell21_1386313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_1386313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386313 prefixEnd_1386313 := by exact prefixLift 1386313
  have htrace : WordTrace (prefixWord ++ tailWord_1386313) baseStart_1386313 baseEnd_1386313 := by
    simpa [prefixWord, tailWord_1386313, baseEnd_1386313] using wordTrace_append hprefix tailTrace_1386313
  have hstable : (prefixWord ++ tailWord_1386313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386313).length < 2 ^ (prefixWord ++ tailWord_1386313).sum := by decide
  have hdescent : baseEnd_1386313 < baseStart_1386313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386344 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_1386344 : Nat := 118140960795 + 1386344 * 2 ^ 59
def prefixEnd_1386344 : Nat := 4983230072969 + 3 ^ 40 * 1386344 * 2
def baseEnd_1386344 : Nat := 316382588656368513966367

theorem tailTrace_1386344 : CollatzResearch.WordTrace tailWord_1386344 prefixEnd_1386344 316382588656368513966367 := by
  unfold tailWord_1386344
  simp only [CollatzResearch.WordTrace]
  refine ⟨25282059844759965775095043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33709413126346621033460057 25282059844759965775095043)
  ·
    refine ⟨37923089767139948662642565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25282059844759965775095043 37923089767139948662642565)
    ·
      refine ⟨7110579331338740374245481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37923089767139948662642565 7110579331338740374245481)
      ·
        refine ⟨5332934498504055280684111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7110579331338740374245481 5332934498504055280684111)
        ·
          refine ⟨7999401747756082921026167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5332934498504055280684111 7999401747756082921026167)
          ·
            refine ⟨11999102621634124381539251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7999401747756082921026167 11999102621634124381539251)
            ·
              refine ⟨17998653932451186572308877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11999102621634124381539251 17998653932451186572308877)
              ·
                refine ⟨6749495224669194964615829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17998653932451186572308877 6749495224669194964615829)
                ·
                  refine ⟨316382588656368513966367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6749495224669194964615829 316382588656368513966367)
                  ·
                    rfl

theorem cell21_1386344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_1386344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386344 prefixEnd_1386344 := by exact prefixLift 1386344
  have htrace : WordTrace (prefixWord ++ tailWord_1386344) baseStart_1386344 baseEnd_1386344 := by
    simpa [prefixWord, tailWord_1386344, baseEnd_1386344] using wordTrace_append hprefix tailTrace_1386344
  have hstable : (prefixWord ++ tailWord_1386344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386344).length < 2 ^ (prefixWord ++ tailWord_1386344).sum := by decide
  have hdescent : baseEnd_1386344 < baseStart_1386344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386392 : List Nat := [2, 1, 2, 6, 2, 8]
def baseStart_1386392 : Nat := 118140960795 + 1386392 * 2 ^ 59
def prefixEnd_1386392 : Nat := 4983230072969 + 3 ^ 40 * 1386392 * 2
def baseEnd_1386392 : Nat := 11718279367049299895047

theorem tailTrace_1386392 : CollatzResearch.WordTrace tailWord_1386392 prefixEnd_1386392 11718279367049299895047 := by
  unfold tailWord_1386392
  simp only [CollatzResearch.WordTrace]
  refine ⟨25282935196673017873968715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33710580262230690498624953 25282935196673017873968715)
  ·
    refine ⟨37924402795009526810953073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25282935196673017873968715 37924402795009526810953073)
    ·
      refine ⟨28443302096257145108214805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37924402795009526810953073 28443302096257145108214805)
      ·
        refine ⟨1333279785762053676947569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28443302096257145108214805 1333279785762053676947569)
        ·
          refine ⟨999959839321540257710677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1333279785762053676947569 999959839321540257710677)
          ·
            refine ⟨11718279367049299895047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 999959839321540257710677 11718279367049299895047)
            ·
              rfl

theorem cell21_1386392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 8].length) (baseStart_1386392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386392 prefixEnd_1386392 := by exact prefixLift 1386392
  have htrace : WordTrace (prefixWord ++ tailWord_1386392) baseStart_1386392 baseEnd_1386392 := by
    simpa [prefixWord, tailWord_1386392, baseEnd_1386392] using wordTrace_append hprefix tailTrace_1386392
  have hstable : (prefixWord ++ tailWord_1386392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386392).length < 2 ^ (prefixWord ++ tailWord_1386392).sum := by decide
  have hdescent : baseEnd_1386392 < baseStart_1386392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386454 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1386454 : Nat := 118140960795 + 1386454 * 2 ^ 59
def prefixEnd_1386454 : Nat := 4983230072969 + 3 ^ 40 * 1386454 * 2
def baseEnd_1386454 : Nat := 316407692155032767132809

theorem tailTrace_1386454 : CollatzResearch.WordTrace tailWord_1386454 prefixEnd_1386454 316407692155032767132809 := by
  unfold tailWord_1386454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160508232445088771043401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33712087812747613557796277 3160508232445088771043401)
  ·
    refine ⟨2370381174333816578282551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3160508232445088771043401 2370381174333816578282551)
    ·
      refine ⟨3555571761500724867423827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370381174333816578282551 3555571761500724867423827)
      ·
        refine ⟨5333357642251087301135741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555571761500724867423827 5333357642251087301135741)
        ·
          refine ⟨2000009115844157737925903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5333357642251087301135741 2000009115844157737925903)
          ·
            refine ⟨3000013673766236606888855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000009115844157737925903 3000013673766236606888855)
            ·
              refine ⟨4500020510649354910333283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000013673766236606888855 4500020510649354910333283)
              ·
                refine ⟨6750030765974032365499925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500020510649354910333283 6750030765974032365499925)
                ·
                  refine ⟨316407692155032767132809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6750030765974032365499925 316407692155032767132809)
                  ·
                    rfl

theorem cell21_1386454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1386454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386454 prefixEnd_1386454 := by exact prefixLift 1386454
  have htrace : WordTrace (prefixWord ++ tailWord_1386454) baseStart_1386454 baseEnd_1386454 := by
    simpa [prefixWord, tailWord_1386454, baseEnd_1386454] using wordTrace_append hprefix tailTrace_1386454
  have hstable : (prefixWord ++ tailWord_1386454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386454).length < 2 ^ (prefixWord ++ tailWord_1386454).sum := by decide
  have hdescent : baseEnd_1386454 < baseStart_1386454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386465 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 5]
def baseStart_1386465 : Nat := 118140960795 + 1386465 * 2 ^ 59
def prefixEnd_1386465 : Nat := 4983230072969 + 3 ^ 40 * 1386465 * 2
def baseEnd_1386465 : Nat := 316410202504899192449453

theorem tailTrace_1386465 : CollatzResearch.WordTrace tailWord_1386465 prefixEnd_1386465 316410202504899192449453 := by
  unfold tailWord_1386465
  simp only [CollatzResearch.WordTrace]
  refine ⟨50568532922081569215344849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33712355281387712810229899 50568532922081569215344849)
  ·
    refine ⟨37926399691561176911508637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50568532922081569215344849 37926399691561176911508637)
    ·
      refine ⟨14222399884335441341815739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37926399691561176911508637 14222399884335441341815739)
      ·
        refine ⟨21333599826503162012723609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14222399884335441341815739 21333599826503162012723609)
        ·
          refine ⟨16000199869877371509542707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21333599826503162012723609 16000199869877371509542707)
          ·
            refine ⟨24000299804816057264314061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16000199869877371509542707 24000299804816057264314061)
            ·
              refine ⟨9000112426806021474117773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24000299804816057264314061 9000112426806021474117773)
              ·
                refine ⟨3375042160052258052794165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9000112426806021474117773 3375042160052258052794165)
                ·
                  refine ⟨316410202504899192449453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3375042160052258052794165 316410202504899192449453)
                  ·
                    rfl

theorem cell21_1386465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_1386465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386465 prefixEnd_1386465 := by exact prefixLift 1386465
  have htrace : WordTrace (prefixWord ++ tailWord_1386465) baseStart_1386465 baseEnd_1386465 := by
    simpa [prefixWord, tailWord_1386465, baseEnd_1386465] using wordTrace_append hprefix tailTrace_1386465
  have hstable : (prefixWord ++ tailWord_1386465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386465).length < 2 ^ (prefixWord ++ tailWord_1386465).sum := by decide
  have hdescent : baseEnd_1386465 < baseStart_1386465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386572 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_1386572 : Nat := 118140960795 + 1386572 * 2 ^ 59
def prefixEnd_1386572 : Nat := 4983230072969 + 3 ^ 40 * 1386572 * 2
def baseEnd_1386572 : Nat := 316434621362690784165901

theorem tailTrace_1386572 : CollatzResearch.WordTrace tailWord_1386572 prefixEnd_1386572 316434621362690784165901 := by
  unfold tailWord_1386572
  simp only [CollatzResearch.WordTrace]
  refine ⟨25286217766346963244744985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33714957021795950992993313 25286217766346963244744985)
  ·
    refine ⟨18964663324760222433558739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25286217766346963244744985 18964663324760222433558739)
    ·
      refine ⟨28446994987140333650338109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18964663324760222433558739 28446994987140333650338109)
      ·
        refine ⟨10667623120177625118876791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28446994987140333650338109 10667623120177625118876791)
        ·
          refine ⟨16001434680266437678315187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10667623120177625118876791 16001434680266437678315187)
          ·
            refine ⟨24002152020399656517472781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16001434680266437678315187 24002152020399656517472781)
            ·
              refine ⟨9000807007649871194052293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24002152020399656517472781 9000807007649871194052293)
              ·
                refine ⟨1687651313934350848884805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9000807007649871194052293 1687651313934350848884805)
                ·
                  refine ⟨316434621362690784165901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1687651313934350848884805 316434621362690784165901)
                  ·
                    rfl

theorem cell21_1386572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_1386572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386572 prefixEnd_1386572 := by exact prefixLift 1386572
  have htrace : WordTrace (prefixWord ++ tailWord_1386572) baseStart_1386572 baseEnd_1386572 := by
    simpa [prefixWord, tailWord_1386572, baseEnd_1386572] using wordTrace_append hprefix tailTrace_1386572
  have hstable : (prefixWord ++ tailWord_1386572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386572).length < 2 ^ (prefixWord ++ tailWord_1386572).sum := by decide
  have hdescent : baseEnd_1386572 < baseStart_1386572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386634 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_1386634 : Nat := 118140960795 + 1386634 * 2 ^ 59
def prefixEnd_1386634 : Nat := 4983230072969 + 3 ^ 40 * 1386634 * 2
def baseEnd_1386634 : Nat := 316448770607392454132441

theorem tailTrace_1386634 : CollatzResearch.WordTrace tailWord_1386634 prefixEnd_1386634 316448770607392454132441 := by
  unfold tailWord_1386634
  simp only [CollatzResearch.WordTrace]
  refine ⟨12643674214617327769561739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33716464572312874052164637 12643674214617327769561739)
  ·
    refine ⟨18965511321925991654342609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12643674214617327769561739 18965511321925991654342609)
    ·
      refine ⟨14224133491444493740756957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18965511321925991654342609 14224133491444493740756957)
      ·
        refine ⟨5334050059291685152783859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14224133491444493740756957 5334050059291685152783859)
        ·
          refine ⟨8001075088937527729175789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5334050059291685152783859 8001075088937527729175789)
          ·
            refine ⟨3000403158351572898440921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8001075088937527729175789 3000403158351572898440921)
            ·
              refine ⟨2250302368763679673830691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000403158351572898440921 2250302368763679673830691)
              ·
                refine ⟨3375453553145519510746037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250302368763679673830691 3375453553145519510746037)
                ·
                  refine ⟨316448770607392454132441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3375453553145519510746037 316448770607392454132441)
                  ·
                    rfl

theorem cell21_1386634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_1386634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386634 prefixEnd_1386634 := by exact prefixLift 1386634
  have htrace : WordTrace (prefixWord ++ tailWord_1386634) baseStart_1386634 baseEnd_1386634 := by
    simpa [prefixWord, tailWord_1386634, baseEnd_1386634] using wordTrace_append hprefix tailTrace_1386634
  have hstable : (prefixWord ++ tailWord_1386634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386634).length < 2 ^ (prefixWord ++ tailWord_1386634).sum := by decide
  have hdescent : baseEnd_1386634 < baseStart_1386634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386654 : List Nat := [4, 3, 1, 1, 4, 1, 2, 5]
def baseStart_1386654 : Nat := 118140960795 + 1386654 * 2 ^ 59
def prefixEnd_1386654 : Nat := 4983230072969 + 3 ^ 40 * 1386654 * 2
def baseEnd_1386654 : Nat := 105484444959958954599689

theorem tailTrace_1386654 : CollatzResearch.WordTrace tailWord_1386654 prefixEnd_1386654 105484444959958954599689 := by
  unfold tailWord_1386654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6321928289799606811746877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33716950878931236329316677 6321928289799606811746877)
  ·
    refine ⟨2370723108674852554405079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6321928289799606811746877 2370723108674852554405079)
    ·
      refine ⟨3556084663012278831607619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370723108674852554405079 3556084663012278831607619)
      ·
        refine ⟨5334126994518418247411429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3556084663012278831607619 5334126994518418247411429)
        ·
          refine ⟨1000148811472203421389643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5334126994518418247411429 1000148811472203421389643)
          ·
            refine ⟨1500223217208305132084465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000148811472203421389643 1500223217208305132084465)
            ·
              refine ⟨1125167412906228849063349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1500223217208305132084465 1125167412906228849063349)
              ·
                refine ⟨105484444959958954599689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1125167412906228849063349 105484444959958954599689)
                ·
                  rfl

theorem cell21_1386654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_1386654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386654 prefixEnd_1386654 := by exact prefixLift 1386654
  have htrace : WordTrace (prefixWord ++ tailWord_1386654) baseStart_1386654 baseEnd_1386654 := by
    simpa [prefixWord, tailWord_1386654, baseEnd_1386654] using wordTrace_append hprefix tailTrace_1386654
  have hstable : (prefixWord ++ tailWord_1386654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386654).length < 2 ^ (prefixWord ++ tailWord_1386654).sum := by decide
  have hdescent : baseEnd_1386654 < baseStart_1386654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386693 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 5]
def baseStart_1386693 : Nat := 118140960795 + 1386693 * 2 ^ 59
def prefixEnd_1386693 : Nat := 4983230072969 + 3 ^ 40 * 1386693 * 2
def baseEnd_1386693 : Nat := 316462235211221462648987

theorem tailTrace_1386693 : CollatzResearch.WordTrace tailWord_1386693 prefixEnd_1386693 316462235211221462648987 := by
  unfold tailWord_1386693
  simp only [CollatzResearch.WordTrace]
  refine ⟨50576848765255564154644733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33717899176837042769763155 50576848765255564154644733)
  ·
    refine ⟨18966318286970836557991775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50576848765255564154644733 18966318286970836557991775)
    ·
      refine ⟨28449477430456254836987663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18966318286970836557991775 28449477430456254836987663)
      ·
        refine ⟨42674216145684382255481495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28449477430456254836987663 42674216145684382255481495)
        ·
          refine ⟨64011324218526573383222243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42674216145684382255481495 64011324218526573383222243)
          ·
            refine ⟨96016986327789860074833365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64011324218526573383222243 96016986327789860074833365)
            ·
              refine ⟨2250398117057574845503907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 96016986327789860074833365 2250398117057574845503907)
              ·
                refine ⟨3375597175586362268255861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250398117057574845503907 3375597175586362268255861)
                ·
                  refine ⟨316462235211221462648987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3375597175586362268255861 316462235211221462648987)
                  ·
                    rfl

theorem cell21_1386693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_1386693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386693 prefixEnd_1386693 := by exact prefixLift 1386693
  have htrace : WordTrace (prefixWord ++ tailWord_1386693) baseStart_1386693 baseEnd_1386693 := by
    simpa [prefixWord, tailWord_1386693, baseEnd_1386693] using wordTrace_append hprefix tailTrace_1386693
  have hstable : (prefixWord ++ tailWord_1386693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386693).length < 2 ^ (prefixWord ++ tailWord_1386693).sum := by decide
  have hdescent : baseEnd_1386693 < baseStart_1386693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386738 : List Nat := [3, 2, 1, 3, 2, 10]
def baseStart_1386738 : Nat := 118140960795 + 1386738 * 2 ^ 59
def prefixEnd_1386738 : Nat := 4983230072969 + 3 ^ 40 * 1386738 * 2
def baseEnd_1386738 : Nat := 11721203882381903125885

theorem tailTrace_1386738 : CollatzResearch.WordTrace tailWord_1386738 prefixEnd_1386738 11721203882381903125885 := by
  unfold tailWord_1386738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12644622512523134210008217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33718993366728357893355245 12644622512523134210008217)
  ·
    refine ⟨9483466884392350657506163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12644622512523134210008217 9483466884392350657506163)
    ·
      refine ⟨14225200326588525986259245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9483466884392350657506163 14225200326588525986259245)
      ·
        refine ⟨5334450122470697244847217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14225200326588525986259245 5334450122470697244847217)
        ·
          refine ⟨4000837591853022933635413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5334450122470697244847217 4000837591853022933635413)
          ·
            refine ⟨11721203882381903125885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4000837591853022933635413 11721203882381903125885)
            ·
              rfl

theorem cell21_1386738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 10].length) (baseStart_1386738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386738 prefixEnd_1386738 := by exact prefixLift 1386738
  have htrace : WordTrace (prefixWord ++ tailWord_1386738) baseStart_1386738 baseEnd_1386738 := by
    simpa [prefixWord, tailWord_1386738, baseEnd_1386738] using wordTrace_append hprefix tailTrace_1386738
  have hstable : (prefixWord ++ tailWord_1386738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386738).length < 2 ^ (prefixWord ++ tailWord_1386738).sum := by decide
  have hdescent : baseEnd_1386738 < baseStart_1386738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386769 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 5]
def baseStart_1386769 : Nat := 118140960795 + 1386769 * 2 ^ 59
def prefixEnd_1386769 : Nat := 4983230072969 + 3 ^ 40 * 1386769 * 2
def baseEnd_1386769 : Nat := 316479579446662219382165

theorem tailTrace_1386769 : CollatzResearch.WordTrace tailWord_1386769 prefixEnd_1386769 316479579446662219382165 := by
  unfold tailWord_1386769
  simp only [CollatzResearch.WordTrace]
  refine ⟨50579620712980229134411361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33719747141986819422940907 50579620712980229134411361)
  ·
    refine ⟨37934715534735171850808521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50579620712980229134411361 37934715534735171850808521)
    ·
      refine ⟨28451036651051378888106391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37934715534735171850808521 28451036651051378888106391)
      ·
        refine ⟨42676554976577068332159587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28451036651051378888106391 42676554976577068332159587)
        ·
          refine ⟨64014832464865602498239381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42676554976577068332159587 64014832464865602498239381)
          ·
            refine ⟨3000695271790575117104971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64014832464865602498239381 3000695271790575117104971)
            ·
              refine ⟨4501042907685862675657457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000695271790575117104971 4501042907685862675657457)
              ·
                refine ⟨3375782180764397006743093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501042907685862675657457 3375782180764397006743093)
                ·
                  refine ⟨316479579446662219382165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3375782180764397006743093 316479579446662219382165)
                  ·
                    rfl

theorem cell21_1386769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_1386769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386769 prefixEnd_1386769 := by exact prefixLift 1386769
  have htrace : WordTrace (prefixWord ++ tailWord_1386769) baseStart_1386769 baseEnd_1386769 := by
    simpa [prefixWord, tailWord_1386769, baseEnd_1386769] using wordTrace_append hprefix tailTrace_1386769
  have hstable : (prefixWord ++ tailWord_1386769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386769).length < 2 ^ (prefixWord ++ tailWord_1386769).sum := by decide
  have hdescent : baseEnd_1386769 < baseStart_1386769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386910 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1386910 : Nat := 118140960795 + 1386910 * 2 ^ 59
def prefixEnd_1386910 : Nat := 4983230072969 + 3 ^ 40 * 1386910 * 2
def baseEnd_1386910 : Nat := 316511757567677307531877

theorem tailTrace_1386910 : CollatzResearch.WordTrace tailWord_1386910 prefixEnd_1386910 316511757567677307531877 := by
  unfold tailWord_1386910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323095425683676276911773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33723175603646273476862789 6323095425683676276911773)
  ·
    refine ⟨2371160784631378603841915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6323095425683676276911773 2371160784631378603841915)
    ·
      refine ⟨3556741176947067905762873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2371160784631378603841915 3556741176947067905762873)
      ·
        refine ⟨2667555882710300929322155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3556741176947067905762873 2667555882710300929322155)
        ·
          refine ⟨4001333824065451393983233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667555882710300929322155 4001333824065451393983233)
          ·
            refine ⟨3001000368049088545487425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001333824065451393983233 3001000368049088545487425)
            ·
              refine ⟨2250750276036816409115569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001000368049088545487425 2250750276036816409115569)
              ·
                refine ⟨1688062707027612306836677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250750276036816409115569 1688062707027612306836677)
                ·
                  refine ⟨316511757567677307531877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688062707027612306836677 316511757567677307531877)
                  ·
                    rfl

theorem cell21_1386910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1386910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386910 prefixEnd_1386910 := by exact prefixLift 1386910
  have htrace : WordTrace (prefixWord ++ tailWord_1386910) baseStart_1386910 baseEnd_1386910 := by
    simpa [prefixWord, tailWord_1386910, baseEnd_1386910] using wordTrace_append hprefix tailTrace_1386910
  have hstable : (prefixWord ++ tailWord_1386910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386910).length < 2 ^ (prefixWord ++ tailWord_1386910).sum := by decide
  have hdescent : baseEnd_1386910 < baseStart_1386910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386913 : List Nat := [1, 2, 3, 5, 1, 2, 2, 2, 3]
def baseStart_1386913 : Nat := 118140960795 + 1386913 * 2 ^ 59
def prefixEnd_1386913 : Nat := 4983230072969 + 3 ^ 40 * 1386913 * 2
def baseEnd_1386913 : Nat := 316512442208549968981871

theorem tailTrace_1386913 : CollatzResearch.WordTrace tailWord_1386913 prefixEnd_1386913 316512442208549968981871 := by
  unfold tailWord_1386913
  simp only [CollatzResearch.WordTrace]
  refine ⟨50584872824458541727653393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33723248549639027818435595 50584872824458541727653393)
  ·
    refine ⟨37938654618343906295740045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50584872824458541727653393 37938654618343906295740045)
    ·
      refine ⟨14226995481878964860902517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37938654618343906295740045 14226995481878964860902517)
      ·
        refine ⟨1333780826426152955709611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14226995481878964860902517 1333780826426152955709611)
        ·
          refine ⟨2000671239639229433564417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333780826426152955709611 2000671239639229433564417)
          ·
            refine ⟨1500503429729422075173313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2000671239639229433564417 1500503429729422075173313)
            ·
              refine ⟨1125377572297066556379985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1500503429729422075173313 1125377572297066556379985)
              ·
                refine ⟨844033179222799917284989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1125377572297066556379985 844033179222799917284989)
                ·
                  refine ⟨316512442208549968981871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844033179222799917284989 316512442208549968981871)
                  ·
                    rfl

theorem cell21_1386913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 3].length) (baseStart_1386913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1386913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1386913 prefixEnd_1386913 := by exact prefixLift 1386913
  have htrace : WordTrace (prefixWord ++ tailWord_1386913) baseStart_1386913 baseEnd_1386913 := by
    simpa [prefixWord, tailWord_1386913, baseEnd_1386913] using wordTrace_append hprefix tailTrace_1386913
  have hstable : (prefixWord ++ tailWord_1386913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386913).length < 2 ^ (prefixWord ++ tailWord_1386913).sum := by decide
  have hdescent : baseEnd_1386913 < baseStart_1386913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387031 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 5]
def baseStart_1387031 : Nat := 118140960795 + 1387031 * 2 ^ 59
def prefixEnd_1387031 : Nat := 4983230072969 + 3 ^ 40 * 1387031 * 2
def baseEnd_1387031 : Nat := 316539371416207986014963

theorem tailTrace_1387031 : CollatzResearch.WordTrace tailWord_1387031 prefixEnd_1387031 316539371416207986014963 := by
  unfold tailWord_1387031
  simp only [CollatzResearch.WordTrace]
  refine ⟨50589176638031047880448947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33726117758687365253632631 50589176638031047880448947)
  ·
    refine ⟨75883764957046571820673421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50589176638031047880448947 75883764957046571820673421)
    ·
      refine ⟨28456411858892464432752533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75883764957046571820673421 28456411858892464432752533)
      ·
        refine ⟨1333894305885584270285275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28456411858892464432752533 1333894305885584270285275)
        ·
          refine ⟨2000841458828376405427913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333894305885584270285275 2000841458828376405427913)
          ·
            refine ⟨1500631094121282304070935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2000841458828376405427913 1500631094121282304070935)
            ·
              refine ⟨2250946641181923456106403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500631094121282304070935 2250946641181923456106403)
              ·
                refine ⟨3376419961772885184159605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250946641181923456106403 3376419961772885184159605)
                ·
                  refine ⟨316539371416207986014963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3376419961772885184159605 316539371416207986014963)
                  ·
                    rfl

theorem cell21_1387031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 5].length) (baseStart_1387031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387031 prefixEnd_1387031 := by exact prefixLift 1387031
  have htrace : WordTrace (prefixWord ++ tailWord_1387031) baseStart_1387031 baseEnd_1387031 := by
    simpa [prefixWord, tailWord_1387031, baseEnd_1387031] using wordTrace_append hprefix tailTrace_1387031
  have hstable : (prefixWord ++ tailWord_1387031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387031).length < 2 ^ (prefixWord ++ tailWord_1387031).sum := by decide
  have hdescent : baseEnd_1387031 < baseStart_1387031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387056 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_1387056 : Nat := 118140960795 + 1387056 * 2 ^ 59
def prefixEnd_1387056 : Nat := 4983230072969 + 3 ^ 40 * 1387056 * 2
def baseEnd_1387056 : Nat := 316545076756813498098245

theorem tailTrace_1387056 : CollatzResearch.WordTrace tailWord_1387056 prefixEnd_1387056 316545076756813498098245 := by
  unfold tailWord_1387056
  simp only [CollatzResearch.WordTrace]
  refine ⟨25295044231470238575054511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33726725641960318100072681 25295044231470238575054511)
  ·
    refine ⟨37942566347205357862581767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25295044231470238575054511 37942566347205357862581767)
    ·
      refine ⟨56913849520808036793872651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37942566347205357862581767 56913849520808036793872651)
      ·
        refine ⟨85370774281212055190808977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56913849520808036793872651 85370774281212055190808977)
        ·
          refine ⟨64028080710909041393106733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85370774281212055190808977 64028080710909041393106733)
          ·
            refine ⟨24010530266590890522415025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64028080710909041393106733 24010530266590890522415025)
            ·
              refine ⟨18007897699943167891811269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24010530266590890522415025 18007897699943167891811269)
              ·
                refine ⟨3376480818739343979714613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18007897699943167891811269 3376480818739343979714613)
                ·
                  refine ⟨316545076756813498098245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3376480818739343979714613 316545076756813498098245)
                  ·
                    rfl

theorem cell21_1387056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_1387056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387056 prefixEnd_1387056 := by exact prefixLift 1387056
  have htrace : WordTrace (prefixWord ++ tailWord_1387056) baseStart_1387056 baseEnd_1387056 := by
    simpa [prefixWord, tailWord_1387056, baseEnd_1387056] using wordTrace_append hprefix tailTrace_1387056
  have hstable : (prefixWord ++ tailWord_1387056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387056).length < 2 ^ (prefixWord ++ tailWord_1387056).sum := by decide
  have hdescent : baseEnd_1387056 < baseStart_1387056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387076 : List Nat := [2, 3, 5, 1, 1, 9]
def baseStart_1387076 : Nat := 118140960795 + 1387076 * 2 ^ 59
def prefixEnd_1387076 : Nat := 4983230072969 + 3 ^ 40 * 1387076 * 2
def baseEnd_1387076 : Nat := 11724060778862885472773

theorem tailTrace_1387076 : CollatzResearch.WordTrace tailWord_1387076 prefixEnd_1387076 11724060778862885472773 := by
  unfold tailWord_1387076
  simp only [CollatzResearch.WordTrace]
  refine ⟨25295408961434010282918541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33727211948578680377224721 25295408961434010282918541)
  ·
    refine ⟨9485778360537753856094453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25295408961434010282918541 9485778360537753856094453)
    ·
      refine ⟨889291721300414424008855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9485778360537753856094453 889291721300414424008855)
      ·
        refine ⟨1333937581950621636013283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889291721300414424008855 1333937581950621636013283)
        ·
          refine ⟨2000906372925932454019925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333937581950621636013283 2000906372925932454019925)
          ·
            refine ⟨11724060778862885472773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2000906372925932454019925 11724060778862885472773)
            ·
              rfl

theorem cell21_1387076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 9].length) (baseStart_1387076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387076 prefixEnd_1387076 := by exact prefixLift 1387076
  have htrace : WordTrace (prefixWord ++ tailWord_1387076) baseStart_1387076 baseEnd_1387076 := by
    simpa [prefixWord, tailWord_1387076, baseEnd_1387076] using wordTrace_append hprefix tailTrace_1387076
  have hstable : (prefixWord ++ tailWord_1387076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387076).length < 2 ^ (prefixWord ++ tailWord_1387076).sum := by decide
  have hdescent : baseEnd_1387076 < baseStart_1387076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387087 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 4]
def baseStart_1387087 : Nat := 118140960795 + 1387087 * 2 ^ 59
def prefixEnd_1387087 : Nat := 4983230072969 + 3 ^ 40 * 1387087 * 2
def baseEnd_1387087 : Nat := 316552151379164333081515

theorem tailTrace_1387087 : CollatzResearch.WordTrace tailWord_1387087 prefixEnd_1387087 316552151379164333081515 := by
  unfold tailWord_1387087
  simp only [CollatzResearch.WordTrace]
  refine ⟨50591219125828169444487515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33727479417218779629658343 50591219125828169444487515)
  ·
    refine ⟨75886828688742254166731273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50591219125828169444487515 75886828688742254166731273)
    ·
      refine ⟨56915121516556690625048455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75886828688742254166731273 56915121516556690625048455)
      ·
        refine ⟨85372682274835035937572683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56915121516556690625048455 85372682274835035937572683)
        ·
          refine ⟨128059023412252553906359025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85372682274835035937572683 128059023412252553906359025)
          ·
            refine ⟨96044267559189415429769269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128059023412252553906359025 96044267559189415429769269)
            ·
              refine ⟨9004150083674007696540869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96044267559189415429769269 9004150083674007696540869)
              ·
                refine ⟨1688278140688876443101413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9004150083674007696540869 1688278140688876443101413)
                ·
                  refine ⟨316552151379164333081515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688278140688876443101413 316552151379164333081515)
                  ·
                    rfl

theorem cell21_1387087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 4].length) (baseStart_1387087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387087 prefixEnd_1387087 := by exact prefixLift 1387087
  have htrace : WordTrace (prefixWord ++ tailWord_1387087) baseStart_1387087 baseEnd_1387087 := by
    simpa [prefixWord, tailWord_1387087, baseEnd_1387087] using wordTrace_append hprefix tailTrace_1387087
  have hstable : (prefixWord ++ tailWord_1387087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387087).length < 2 ^ (prefixWord ++ tailWord_1387087).sum := by decide
  have hdescent : baseEnd_1387087 < baseStart_1387087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387090 : List Nat := [3, 2, 2, 1, 2, 1, 3, 4, 3]
def baseStart_1387090 : Nat := 118140960795 + 1387090 * 2 ^ 59
def prefixEnd_1387090 : Nat := 4983230072969 + 3 ^ 40 * 1387090 * 2
def baseEnd_1387090 : Nat := 316552836020036994531509

theorem tailTrace_1387090 : CollatzResearch.WordTrace tailWord_1387090 prefixEnd_1387090 316552836020036994531509 := by
  unfold tailWord_1387090
  simp only [CollatzResearch.WordTrace]
  refine ⟨12647832136204325239211681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33727552363211533971231149 12647832136204325239211681)
  ·
    refine ⟨9485874102153243929408761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12647832136204325239211681 9485874102153243929408761)
    ·
      refine ⟨7114405576614932947056571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9485874102153243929408761 7114405576614932947056571)
      ·
        refine ⟨10671608364922399420584857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7114405576614932947056571 10671608364922399420584857)
        ·
          refine ⟨8003706273691799565438643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10671608364922399420584857 8003706273691799565438643)
          ·
            refine ⟨12005559410537699348157965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8003706273691799565438643 12005559410537699348157965)
            ·
              refine ⟨4502084778951637255559237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12005559410537699348157965 4502084778951637255559237)
              ·
                refine ⟨844140896053431985417357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4502084778951637255559237 844140896053431985417357)
                ·
                  refine ⟨316552836020036994531509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844140896053431985417357 316552836020036994531509)
                  ·
                    rfl

theorem cell21_1387090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_1387090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387090 prefixEnd_1387090 := by exact prefixLift 1387090
  have htrace : WordTrace (prefixWord ++ tailWord_1387090) baseStart_1387090 baseEnd_1387090 := by
    simpa [prefixWord, tailWord_1387090, baseEnd_1387090] using wordTrace_append hprefix tailTrace_1387090
  have hstable : (prefixWord ++ tailWord_1387090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387090).length < 2 ^ (prefixWord ++ tailWord_1387090).sum := by decide
  have hdescent : baseEnd_1387090 < baseStart_1387090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387287 : List Nat := [1, 1, 3, 4, 3, 1, 3, 5]
def baseStart_1387287 : Nat := 118140960795 + 1387287 * 2 ^ 59
def prefixEnd_1387287 : Nat := 4983230072969 + 3 ^ 40 * 1387287 * 2
def baseEnd_1387287 : Nat := 105532598034669476582591

theorem tailTrace_1387287 : CollatzResearch.WordTrace tailWord_1387287 prefixEnd_1387287 105532598034669476582591 := by
  unfold tailWord_1387287
  simp only [CollatzResearch.WordTrace]
  refine ⟨50598513725103603601768115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33732342483402402401178743 50598513725103603601768115)
  ·
    refine ⟨75897770587655405402652173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50598513725103603601768115 75897770587655405402652173)
    ·
      refine ⟨28461663970370777025994565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75897770587655405402652173 28461663970370777025994565)
      ·
        refine ⟨5336561994444520692373981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28461663970370777025994565 5336561994444520692373981)
        ·
          refine ⟨2001210747916695259640243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5336561994444520692373981 2001210747916695259640243)
          ·
            refine ⟨3001816121875042889460365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001210747916695259640243 3001816121875042889460365)
            ·
              refine ⟨1125681045703141083547637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3001816121875042889460365 1125681045703141083547637)
              ·
                refine ⟨105532598034669476582591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1125681045703141083547637 105532598034669476582591)
                ·
                  rfl

theorem cell21_1387287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 5].length) (baseStart_1387287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387287 prefixEnd_1387287 := by exact prefixLift 1387287
  have htrace : WordTrace (prefixWord ++ tailWord_1387287) baseStart_1387287 baseEnd_1387287 := by
    simpa [prefixWord, tailWord_1387287, baseEnd_1387287] using wordTrace_append hprefix tailTrace_1387287
  have hstable : (prefixWord ++ tailWord_1387287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387287).length < 2 ^ (prefixWord ++ tailWord_1387287).sum := by decide
  have hdescent : baseEnd_1387287 < baseStart_1387287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387315 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 6]
def baseStart_1387315 : Nat := 118140960795 + 1387315 * 2 ^ 59
def prefixEnd_1387315 : Nat := 4983230072969 + 3 ^ 40 * 1387315 * 2
def baseEnd_1387315 : Nat := 316604184085486603281049

theorem tailTrace_1387315 : CollatzResearch.WordTrace tailWord_1387315 prefixEnd_1387315 316604184085486603281049 := by
  unfold tailWord_1387315
  simp only [CollatzResearch.WordTrace]
  refine ⟨50599534969002164383787399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33733023312668109589191599 50599534969002164383787399)
  ·
    refine ⟨75899302453503246575681099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50599534969002164383787399 75899302453503246575681099)
    ·
      refine ⟨113848953680254869863521649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75899302453503246575681099 113848953680254869863521649)
      ·
        refine ⟨85386715260191152397641237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113848953680254869863521649 85386715260191152397641237)
        ·
          refine ⟨4002502277821460268639433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85386715260191152397641237 4002502277821460268639433)
          ·
            refine ⟨3001876708366095201479575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4002502277821460268639433 3001876708366095201479575)
            ·
              refine ⟨4502815062549142802219363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001876708366095201479575 4502815062549142802219363)
              ·
                refine ⟨6754222593823714203329045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4502815062549142802219363 6754222593823714203329045)
                ·
                  refine ⟨316604184085486603281049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6754222593823714203329045 316604184085486603281049)
                  ·
                    rfl

theorem cell21_1387315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 6].length) (baseStart_1387315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387315 prefixEnd_1387315 := by exact prefixLift 1387315
  have htrace : WordTrace (prefixWord ++ tailWord_1387315) baseStart_1387315 baseEnd_1387315 := by
    simpa [prefixWord, tailWord_1387315, baseEnd_1387315] using wordTrace_append hprefix tailTrace_1387315
  have hstable : (prefixWord ++ tailWord_1387315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387315).length < 2 ^ (prefixWord ++ tailWord_1387315).sum := by decide
  have hdescent : baseEnd_1387315 < baseStart_1387315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387377 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 5]
def baseStart_1387377 : Nat := 118140960795 + 1387377 * 2 ^ 59
def prefixEnd_1387377 : Nat := 4983230072969 + 3 ^ 40 * 1387377 * 2
def baseEnd_1387377 : Nat := 316618333330188273247589

theorem tailTrace_1387377 : CollatzResearch.WordTrace tailWord_1387377 prefixEnd_1387377 316618333330188273247589 := by
  unfold tailWord_1387377
  simp only [CollatzResearch.WordTrace]
  refine ⟨50601796294777548972544385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33734530863185032648362923 50601796294777548972544385)
  ·
    refine ⟨37951347221083161729408289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50601796294777548972544385 37951347221083161729408289)
    ·
      refine ⟨28463510415812371297056217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37951347221083161729408289 28463510415812371297056217)
      ·
        refine ⟨21347632811859278472792163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28463510415812371297056217 21347632811859278472792163)
        ·
          refine ⟨32021449217788917709188245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21347632811859278472792163 32021449217788917709188245)
          ·
            refine ⟨1501005432083855517618199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32021449217788917709188245 1501005432083855517618199)
            ·
              refine ⟨2251508148125783276427299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501005432083855517618199 2251508148125783276427299)
              ·
                refine ⟨3377262222188674914640949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251508148125783276427299 3377262222188674914640949)
                ·
                  refine ⟨316618333330188273247589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3377262222188674914640949 316618333330188273247589)
                  ·
                    rfl

theorem cell21_1387377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_1387377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387377 prefixEnd_1387377 := by exact prefixLift 1387377
  have htrace : WordTrace (prefixWord ++ tailWord_1387377) baseStart_1387377 baseEnd_1387377 := by
    simpa [prefixWord, tailWord_1387377, baseEnd_1387377] using wordTrace_append hprefix tailTrace_1387377
  have hstable : (prefixWord ++ tailWord_1387377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387377).length < 2 ^ (prefixWord ++ tailWord_1387377).sum := by decide
  have hdescent : baseEnd_1387377 < baseStart_1387377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387453 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 5]
def baseStart_1387453 : Nat := 118140960795 + 1387453 * 2 ^ 59
def prefixEnd_1387453 : Nat := 4983230072969 + 3 ^ 40 * 1387453 * 2
def baseEnd_1387453 : Nat := 316635677565629029980767

theorem tailTrace_1387453 : CollatzResearch.WordTrace tailWord_1387453 prefixEnd_1387453 316635677565629029980767 := by
  unfold tailWord_1387453
  simp only [CollatzResearch.WordTrace]
  refine ⟨50604568242502213952311013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33736378828334809301540675 50604568242502213952311013)
  ·
    refine ⟨9488356545469165116058315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50604568242502213952311013 9488356545469165116058315)
    ·
      refine ⟨14232534818203747674087473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9488356545469165116058315 14232534818203747674087473)
      ·
        refine ⟨10674401113652810755565605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14232534818203747674087473 10674401113652810755565605)
        ·
          refine ⟨2001450208809902016668551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10674401113652810755565605 2001450208809902016668551)
          ·
            refine ⟨3002175313214853025002827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001450208809902016668551 3002175313214853025002827)
            ·
              refine ⟨4503262969822279537504241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002175313214853025002827 4503262969822279537504241)
              ·
                refine ⟨3377447227366709653128181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4503262969822279537504241 3377447227366709653128181)
                ·
                  refine ⟨316635677565629029980767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3377447227366709653128181 316635677565629029980767)
                  ·
                    rfl

theorem cell21_1387453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_1387453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387453 prefixEnd_1387453 := by exact prefixLift 1387453
  have htrace : WordTrace (prefixWord ++ tailWord_1387453) baseStart_1387453 baseEnd_1387453 := by
    simpa [prefixWord, tailWord_1387453, baseEnd_1387453] using wordTrace_append hprefix tailTrace_1387453
  have hstable : (prefixWord ++ tailWord_1387453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387453).length < 2 ^ (prefixWord ++ tailWord_1387453).sum := by decide
  have hdescent : baseEnd_1387453 < baseStart_1387453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387462 : List Nat := [6, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1387462 : Nat := 118140960795 + 1387462 * 2 ^ 59
def prefixEnd_1387462 : Nat := 4983230072969 + 3 ^ 40 * 1387462 * 2
def baseEnd_1387462 : Nat := 316637731488247014330749

theorem tailTrace_1387462 : CollatzResearch.WordTrace tailWord_1387462 prefixEnd_1387462 316637731488247014330749 := by
  unfold tailWord_1387462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581403015608425265293395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33736597666313072326259093 1581403015608425265293395)
  ·
    refine ⟨2372104523412637897940093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1581403015608425265293395 2372104523412637897940093)
    ·
      refine ⟨889539196279739211727535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2372104523412637897940093 889539196279739211727535)
      ·
        refine ⟨1334308794419608817591303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889539196279739211727535 1334308794419608817591303)
        ·
          refine ⟨2001463191629413226386955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334308794419608817591303 2001463191629413226386955)
          ·
            refine ⟨3002194787444119839580433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001463191629413226386955 3002194787444119839580433)
            ·
              refine ⟨2251646090583089879685325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002194787444119839580433 2251646090583089879685325)
              ·
                refine ⟨844367283968658704881997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2251646090583089879685325 844367283968658704881997)
                ·
                  refine ⟨316637731488247014330749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844367283968658704881997 316637731488247014330749)
                  ·
                    rfl

theorem cell21_1387462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1387462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387462 prefixEnd_1387462 := by exact prefixLift 1387462
  have htrace : WordTrace (prefixWord ++ tailWord_1387462) baseStart_1387462 baseEnd_1387462 := by
    simpa [prefixWord, tailWord_1387462, baseEnd_1387462] using wordTrace_append hprefix tailTrace_1387462
  have hstable : (prefixWord ++ tailWord_1387462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387462).length < 2 ^ (prefixWord ++ tailWord_1387462).sum := by decide
  have hdescent : baseEnd_1387462 < baseStart_1387462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387470 : List Nat := [4, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_1387470 : Nat := 118140960795 + 1387470 * 2 ^ 59
def prefixEnd_1387470 : Nat := 4983230072969 + 3 ^ 40 * 1387470 * 2
def baseEnd_1387470 : Nat := 316639557197240778197399

theorem tailTrace_1387470 : CollatzResearch.WordTrace tailWord_1387470 prefixEnd_1387470 316639557197240778197399 := by
  unfold tailWord_1387470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325648535430078231959983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33736792188960417237119909 6325648535430078231959983)
  ·
    refine ⟨9488472803145117347939975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6325648535430078231959983 9488472803145117347939975)
    ·
      refine ⟨14232709204717676021909963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9488472803145117347939975 14232709204717676021909963)
      ·
        refine ⟨21349063807076514032864945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14232709204717676021909963 21349063807076514032864945)
        ·
          refine ⟨16011797855307385524648709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21349063807076514032864945 16011797855307385524648709)
          ·
            refine ⟨3002212097870134785871633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16011797855307385524648709 3002212097870134785871633)
            ·
              refine ⟨2251659073402601089403725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002212097870134785871633 2251659073402601089403725)
              ·
                refine ⟨844372152525975408526397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2251659073402601089403725 844372152525975408526397)
                ·
                  refine ⟨316639557197240778197399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844372152525975408526397 316639557197240778197399)
                  ·
                    rfl

theorem cell21_1387470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_1387470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387470 prefixEnd_1387470 := by exact prefixLift 1387470
  have htrace : WordTrace (prefixWord ++ tailWord_1387470) baseStart_1387470 baseEnd_1387470 := by
    simpa [prefixWord, tailWord_1387470, baseEnd_1387470] using wordTrace_append hprefix tailTrace_1387470
  have hstable : (prefixWord ++ tailWord_1387470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387470).length < 2 ^ (prefixWord ++ tailWord_1387470).sum := by decide
  have hdescent : baseEnd_1387470 < baseStart_1387470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387481 : List Nat := [1, 2, 1, 2, 5, 2, 8]
def baseStart_1387481 : Nat := 118140960795 + 1387481 * 2 ^ 59
def prefixEnd_1387481 : Nat := 4983230072969 + 3 ^ 40 * 1387481 * 2
def baseEnd_1387481 : Nat := 35182451949678578168227

theorem tailTrace_1387481 : CollatzResearch.WordTrace tailWord_1387481 prefixEnd_1387481 35182451949678578168227 := by
  unfold tailWord_1387481
  simp only [CollatzResearch.WordTrace]
  refine ⟨50605589486400774734330297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33737059657600516489553531 50605589486400774734330297)
  ·
    refine ⟨37954192114800581050747723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50605589486400774734330297 37954192114800581050747723)
    ·
      refine ⟨56931288172200871576121585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37954192114800581050747723 56931288172200871576121585)
      ·
        refine ⟨42698466129150653682091189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56931288172200871576121585 42698466129150653682091189)
        ·
          refine ⟨4002981199607873782696049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42698466129150653682091189 4002981199607873782696049)
          ·
            refine ⟨3002235899705905337022037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4002981199607873782696049 3002235899705905337022037)
            ·
              refine ⟨35182451949678578168227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3002235899705905337022037 35182451949678578168227)
              ·
                rfl

theorem cell21_1387481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 8].length) (baseStart_1387481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387481 prefixEnd_1387481 := by exact prefixLift 1387481
  have htrace : WordTrace (prefixWord ++ tailWord_1387481) baseStart_1387481 baseEnd_1387481 := by
    simpa [prefixWord, tailWord_1387481, baseEnd_1387481] using wordTrace_append hprefix tailTrace_1387481
  have hstable : (prefixWord ++ tailWord_1387481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387481).length < 2 ^ (prefixWord ++ tailWord_1387481).sum := by decide
  have hdescent : baseEnd_1387481 < baseStart_1387481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387543 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 6]
def baseStart_1387543 : Nat := 118140960795 + 1387543 * 2 ^ 59
def prefixEnd_1387543 : Nat := 4983230072969 + 3 ^ 40 * 1387543 * 2
def baseEnd_1387543 : Nat := 316656216791808873480583

theorem tailTrace_1387543 : CollatzResearch.WordTrace tailWord_1387543 prefixEnd_1387543 316656216791808873480583 := by
  unfold tailWord_1387543
  simp only [CollatzResearch.WordTrace]
  refine ⟨50607850812176159323087283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33738567208117439548724855 50607850812176159323087283)
  ·
    refine ⟨75911776218264238984630925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50607850812176159323087283 75911776218264238984630925)
    ·
      refine ⟨28466916081849089619236597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75911776218264238984630925 28466916081849089619236597)
      ·
        refine ⟨2668773382673352151803431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28466916081849089619236597 2668773382673352151803431)
        ·
          refine ⟨4003160074010028227705147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668773382673352151803431 4003160074010028227705147)
          ·
            refine ⟨6004740111015042341557721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4003160074010028227705147 6004740111015042341557721)
            ·
              refine ⟨4503555083261281756168291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6004740111015042341557721 4503555083261281756168291)
              ·
                refine ⟨6755332624891922634252437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4503555083261281756168291 6755332624891922634252437)
                ·
                  refine ⟨316656216791808873480583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6755332624891922634252437 316656216791808873480583)
                  ·
                    rfl

theorem cell21_1387543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 6].length) (baseStart_1387543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387543 prefixEnd_1387543 := by exact prefixLift 1387543
  have htrace : WordTrace (prefixWord ++ tailWord_1387543) baseStart_1387543 baseEnd_1387543 := by
    simpa [prefixWord, tailWord_1387543, baseEnd_1387543] using wordTrace_append hprefix tailTrace_1387543
  have hstable : (prefixWord ++ tailWord_1387543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387543).length < 2 ^ (prefixWord ++ tailWord_1387543).sum := by decide
  have hdescent : baseEnd_1387543 < baseStart_1387543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387546 : List Nat := [3, 1, 1, 3, 1, 2, 5, 2, 3]
def baseStart_1387546 : Nat := 118140960795 + 1387546 * 2 ^ 59
def prefixEnd_1387546 : Nat := 4983230072969 + 3 ^ 40 * 1387546 * 2
def baseEnd_1387546 : Nat := 316656901432681534930577

theorem tailTrace_1387546 : CollatzResearch.WordTrace tailWord_1387546 prefixEnd_1387546 316656901432681534930577 := by
  unfold tailWord_1387546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12651990057791322708861623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33738640154110193890297661 12651990057791322708861623)
  ·
    refine ⟨18977985086686984063292435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12651990057791322708861623 18977985086686984063292435)
    ·
      refine ⟨28466977630030476094938653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18977985086686984063292435 28466977630030476094938653)
      ·
        refine ⟨10675116611261428535601995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28466977630030476094938653 10675116611261428535601995)
        ·
          refine ⟨16012674916892142803402993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10675116611261428535601995 16012674916892142803402993)
          ·
            refine ⟨12009506187669107102552245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16012674916892142803402993 12009506187669107102552245)
            ·
              refine ⟨1125891205093978790864273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12009506187669107102552245 1125891205093978790864273)
              ·
                refine ⟨844418403820484093148205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1125891205093978790864273 844418403820484093148205)
                ·
                  refine ⟨316656901432681534930577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844418403820484093148205 316656901432681534930577)
                  ·
                    rfl

theorem cell21_1387546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_1387546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387546 prefixEnd_1387546 := by exact prefixLift 1387546
  have htrace : WordTrace (prefixWord ++ tailWord_1387546) baseStart_1387546 baseEnd_1387546 := by
    simpa [prefixWord, tailWord_1387546, baseEnd_1387546] using wordTrace_append hprefix tailTrace_1387546
  have hstable : (prefixWord ++ tailWord_1387546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387546).length < 2 ^ (prefixWord ++ tailWord_1387546).sum := by decide
  have hdescent : baseEnd_1387546 < baseStart_1387546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387557 : List Nat := [1, 3, 1, 2, 2, 2, 4, 6]
def baseStart_1387557 : Nat := 118140960795 + 1387557 * 2 ^ 59
def prefixEnd_1387557 : Nat := 4983230072969 + 3 ^ 40 * 1387557 * 2
def baseEnd_1387557 : Nat := 105553137260849320082407

theorem tailTrace_1387557 : CollatzResearch.WordTrace tailWord_1387557 prefixEnd_1387557 105553137260849320082407 := by
  unfold tailWord_1387557
  simp only [CollatzResearch.WordTrace]
  refine ⟨50608361434125439714096925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33738907622750293142731283 50608361434125439714096925)
  ·
    refine ⟨18978135537797039892786347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50608361434125439714096925 18978135537797039892786347)
    ·
      refine ⟨28467203306695559839179521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18978135537797039892786347 28467203306695559839179521)
      ·
        refine ⟨21350402480021669879384641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28467203306695559839179521 21350402480021669879384641)
        ·
          refine ⟨16012801860016252409538481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21350402480021669879384641 16012801860016252409538481)
          ·
            refine ⟨12009601395012189307153861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16012801860016252409538481 12009601395012189307153861)
            ·
              refine ⟨2251800261564785495091349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12009601395012189307153861 2251800261564785495091349)
              ·
                refine ⟨105553137260849320082407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2251800261564785495091349 105553137260849320082407)
                ·
                  rfl

theorem cell21_1387557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 6].length) (baseStart_1387557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387557 prefixEnd_1387557 := by exact prefixLift 1387557
  have htrace : WordTrace (prefixWord ++ tailWord_1387557) baseStart_1387557 baseEnd_1387557 := by
    simpa [prefixWord, tailWord_1387557, baseEnd_1387557] using wordTrace_append hprefix tailTrace_1387557
  have hstable : (prefixWord ++ tailWord_1387557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387557).length < 2 ^ (prefixWord ++ tailWord_1387557).sum := by decide
  have hdescent : baseEnd_1387557 < baseStart_1387557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387571 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 7]
def baseStart_1387571 : Nat := 118140960795 + 1387571 * 2 ^ 59
def prefixEnd_1387571 : Nat := 4983230072969 + 3 ^ 40 * 1387571 * 2
def baseEnd_1387571 : Nat := 316662606773287047013859

theorem tailTrace_1387571 : CollatzResearch.WordTrace tailWord_1387571 prefixEnd_1387571 316662606773287047013859 := by
  unfold tailWord_1387571
  simp only [CollatzResearch.WordTrace]
  refine ⟨50608872056074720105106567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33739248037383146736737711 50608872056074720105106567)
  ·
    refine ⟨75913308084112080157659851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50608872056074720105106567 75913308084112080157659851)
    ·
      refine ⟨113869962126168120236489777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75913308084112080157659851 113869962126168120236489777)
      ·
        refine ⟨85402471594626090177367333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113869962126168120236489777 85402471594626090177367333)
        ·
          refine ⟨16012963423992391908256375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85402471594626090177367333 16012963423992391908256375)
          ·
            refine ⟨24019445135988587862384563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16012963423992391908256375 24019445135988587862384563)
            ·
              refine ⟨36029167703982881793576845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24019445135988587862384563 36029167703982881793576845)
              ·
                refine ⟨13510937888993580672591317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36029167703982881793576845 13510937888993580672591317)
                ·
                  refine ⟨316662606773287047013859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13510937888993580672591317 316662606773287047013859)
                  ·
                    rfl

theorem cell21_1387571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_1387571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387571 prefixEnd_1387571 := by exact prefixLift 1387571
  have htrace : WordTrace (prefixWord ++ tailWord_1387571) baseStart_1387571 baseEnd_1387571 := by
    simpa [prefixWord, tailWord_1387571, baseEnd_1387571] using wordTrace_append hprefix tailTrace_1387571
  have hstable : (prefixWord ++ tailWord_1387571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387571).length < 2 ^ (prefixWord ++ tailWord_1387571).sum := by decide
  have hdescent : baseEnd_1387571 < baseStart_1387571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387574 : List Nat := [5, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1387574 : Nat := 118140960795 + 1387574 * 2 ^ 59
def prefixEnd_1387574 : Nat := 4983230072969 + 3 ^ 40 * 1387574 * 2
def baseEnd_1387574 : Nat := 105554430471386569487951

theorem tailTrace_1387574 : CollatzResearch.WordTrace tailWord_1387574 prefixEnd_1387574 105554430471386569487951 := by
  unfold tailWord_1387574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3163061342191490726091611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33739320983375901078310517 3163061342191490726091611)
  ·
    refine ⟨4744592013287236089137417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3163061342191490726091611 4744592013287236089137417)
    ·
      refine ⟨3558444009965427066853063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4744592013287236089137417 3558444009965427066853063)
      ·
        refine ⟨5337666014948140600279595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3558444009965427066853063 5337666014948140600279595)
        ·
          refine ⟨8006499022422210900419393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337666014948140600279595 8006499022422210900419393)
          ·
            refine ⟨6004874266816658175314545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8006499022422210900419393 6004874266816658175314545)
            ·
              refine ⟨4503655700112493631485909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6004874266816658175314545 4503655700112493631485909)
              ·
                refine ⟨105554430471386569487951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4503655700112493631485909 105554430471386569487951)
                ·
                  rfl

theorem cell21_1387574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1387574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387574 prefixEnd_1387574 := by exact prefixLift 1387574
  have htrace : WordTrace (prefixWord ++ tailWord_1387574) baseStart_1387574 baseEnd_1387574 := by
    simpa [prefixWord, tailWord_1387574, baseEnd_1387574] using wordTrace_append hprefix tailTrace_1387574
  have hstable : (prefixWord ++ tailWord_1387574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387574).length < 2 ^ (prefixWord ++ tailWord_1387574).sum := by decide
  have hdescent : baseEnd_1387574 < baseStart_1387574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387605 : List Nat := [1, 3, 2, 2, 1, 2, 3, 4, 3]
def baseStart_1387605 : Nat := 118140960795 + 1387605 * 2 ^ 59
def prefixEnd_1387605 : Nat := 4983230072969 + 3 ^ 40 * 1387605 * 2
def baseEnd_1387605 : Nat := 316670366036510543447123

theorem tailTrace_1387605 : CollatzResearch.WordTrace tailWord_1387605 prefixEnd_1387605 316670366036510543447123 := by
  unfold tailWord_1387605
  simp only [CollatzResearch.WordTrace]
  refine ⟨50610112137951543911844269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33740074758634362607896179 50610112137951543911844269)
  ·
    refine ⟨18978792051731828966941601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50610112137951543911844269 18978792051731828966941601)
    ·
      refine ⟨14234094038798871725206201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18978792051731828966941601 14234094038798871725206201)
      ·
        refine ⟨10675570529099153793904651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14234094038798871725206201 10675570529099153793904651)
        ·
          refine ⟨16013355793648730690856977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10675570529099153793904651 16013355793648730690856977)
          ·
            refine ⟨12010016845236548018142733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16013355793648730690856977 12010016845236548018142733)
            ·
              refine ⟨4503756316963705506803525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12010016845236548018142733 4503756316963705506803525)
              ·
                refine ⟨844454309430694782525661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4503756316963705506803525 844454309430694782525661)
                ·
                  refine ⟨316670366036510543447123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844454309430694782525661 316670366036510543447123)
                  ·
                    rfl

theorem cell21_1387605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_1387605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387605 prefixEnd_1387605 := by exact prefixLift 1387605
  have htrace : WordTrace (prefixWord ++ tailWord_1387605) baseStart_1387605 baseEnd_1387605 := by
    simpa [prefixWord, tailWord_1387605, baseEnd_1387605] using wordTrace_append hprefix tailTrace_1387605
  have hstable : (prefixWord ++ tailWord_1387605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387605).length < 2 ^ (prefixWord ++ tailWord_1387605).sum := by decide
  have hdescent : baseEnd_1387605 < baseStart_1387605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387653 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 4]
def baseStart_1387653 : Nat := 118140960795 + 1387653 * 2 ^ 59
def prefixEnd_1387653 : Nat := 4983230072969 + 3 ^ 40 * 1387653 * 2
def baseEnd_1387653 : Nat := 316681320290473126647025

theorem tailTrace_1387653 : CollatzResearch.WordTrace tailWord_1387653 prefixEnd_1387653 316681320290473126647025 := by
  unfold tailWord_1387653
  simp only [CollatzResearch.WordTrace]
  refine ⟨50611862841777648109591613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33741241894518432073061075 50611862841777648109591613)
  ·
    refine ⟨18979448565666618041096855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50611862841777648109591613 18979448565666618041096855)
    ·
      refine ⟨28469172848499927061645283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18979448565666618041096855 28469172848499927061645283)
      ·
        refine ⟨42703759272749890592467925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28469172848499927061645283 42703759272749890592467925)
        ·
          refine ⟨1000869357955075560760967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42703759272749890592467925 1000869357955075560760967)
          ·
            refine ⟨1501304036932613341141451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000869357955075560760967 1501304036932613341141451)
            ·
              refine ⟨2251956055398920011712177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501304036932613341141451 2251956055398920011712177)
              ·
                refine ⟨1688967041549190008784133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251956055398920011712177 1688967041549190008784133)
                ·
                  refine ⟨316681320290473126647025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688967041549190008784133 316681320290473126647025)
                  ·
                    rfl

theorem cell21_1387653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_1387653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387653 prefixEnd_1387653 := by exact prefixLift 1387653
  have htrace : WordTrace (prefixWord ++ tailWord_1387653) baseStart_1387653 baseEnd_1387653 := by
    simpa [prefixWord, tailWord_1387653, baseEnd_1387653] using wordTrace_append hprefix tailTrace_1387653
  have hstable : (prefixWord ++ tailWord_1387653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387653).length < 2 ^ (prefixWord ++ tailWord_1387653).sum := by decide
  have hdescent : baseEnd_1387653 < baseStart_1387653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387698 : List Nat := [3, 2, 1, 1, 1, 6, 1, 3, 3]
def baseStart_1387698 : Nat := 118140960795 + 1387698 * 2 ^ 59
def prefixEnd_1387698 : Nat := 4983230072969 + 3 ^ 40 * 1387698 * 2
def baseEnd_1387698 : Nat := 316691589903563048396933

theorem tailTrace_1387698 : CollatzResearch.WordTrace tailWord_1387698 prefixEnd_1387698 316691589903563048396933 := by
  unfold tailWord_1387698
  simp only [CollatzResearch.WordTrace]
  refine ⟨12653376031653655198744937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33742336084409747196653165 12653376031653655198744937)
  ·
    refine ⟨9490032023740241399058703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12653376031653655198744937 9490032023740241399058703)
    ·
      refine ⟨14235048035610362098588055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9490032023740241399058703 14235048035610362098588055)
      ·
        refine ⟨21352572053415543147882083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14235048035610362098588055 21352572053415543147882083)
        ·
          refine ⟨32028858080123314721823125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21352572053415543147882083 32028858080123314721823125)
          ·
            refine ⟨1501352722505780377585459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32028858080123314721823125 1501352722505780377585459)
            ·
              refine ⟨2252029083758670566378189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501352722505780377585459 2252029083758670566378189)
              ·
                refine ⟨844510906409501462391821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2252029083758670566378189 844510906409501462391821)
                ·
                  refine ⟨316691589903563048396933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844510906409501462391821 316691589903563048396933)
                  ·
                    rfl

theorem cell21_1387698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_1387698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387698 prefixEnd_1387698 := by exact prefixLift 1387698
  have htrace : WordTrace (prefixWord ++ tailWord_1387698) baseStart_1387698 baseEnd_1387698 := by
    simpa [prefixWord, tailWord_1387698, baseEnd_1387698] using wordTrace_append hprefix tailTrace_1387698
  have hstable : (prefixWord ++ tailWord_1387698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387698).length < 2 ^ (prefixWord ++ tailWord_1387698).sum := by decide
  have hdescent : baseEnd_1387698 < baseStart_1387698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387723 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 5]
def baseStart_1387723 : Nat := 118140960795 + 1387723 * 2 ^ 59
def prefixEnd_1387723 : Nat := 4983230072969 + 3 ^ 40 * 1387723 * 2
def baseEnd_1387723 : Nat := 316697295244168560480215

theorem tailTrace_1387723 : CollatzResearch.WordTrace tailWord_1387723 prefixEnd_1387723 316697295244168560480215 := by
  unfold tailWord_1387723
  simp only [CollatzResearch.WordTrace]
  refine ⟨50614415951524050064639823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33742943967682700043093215 50614415951524050064639823)
  ·
    refine ⟨75921623927286075096959735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50614415951524050064639823 75921623927286075096959735)
    ·
      refine ⟨113882435890929112645439603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75921623927286075096959735 113882435890929112645439603)
      ·
        refine ⟨170823653836393668968159405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113882435890929112645439603 170823653836393668968159405)
        ·
          refine ⟨64058870188647625863059777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170823653836393668968159405 64058870188647625863059777)
          ·
            refine ⟨48044152641485719397294833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64058870188647625863059777 48044152641485719397294833)
            ·
              refine ⟨36033114481114289547971125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48044152641485719397294833 36033114481114289547971125)
              ·
                refine ⟨3378104482604464645122293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36033114481114289547971125 3378104482604464645122293)
                ·
                  refine ⟨316697295244168560480215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3378104482604464645122293 316697295244168560480215)
                  ·
                    rfl

theorem cell21_1387723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_1387723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387723 prefixEnd_1387723 := by exact prefixLift 1387723
  have htrace : WordTrace (prefixWord ++ tailWord_1387723) baseStart_1387723 baseEnd_1387723 := by
    simpa [prefixWord, tailWord_1387723, baseEnd_1387723] using wordTrace_append hprefix tailTrace_1387723
  have hstable : (prefixWord ++ tailWord_1387723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387723).length < 2 ^ (prefixWord ++ tailWord_1387723).sum := by decide
  have hdescent : baseEnd_1387723 < baseStart_1387723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387726 : List Nat := [4, 1, 1, 1, 5, 1, 2, 6]
def baseStart_1387726 : Nat := 118140960795 + 1387726 * 2 ^ 59
def prefixEnd_1387726 : Nat := 4983230072969 + 3 ^ 40 * 1387726 * 2
def baseEnd_1387726 : Nat := 105565993295013740643403

theorem tailTrace_1387726 : CollatzResearch.WordTrace tailWord_1387726 prefixEnd_1387726 105565993295013740643403 := by
  unfold tailWord_1387726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6326815671314147697124879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33743016913675454384666021 6326815671314147697124879)
  ·
    refine ⟨9490223506971221545687319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6326815671314147697124879 9490223506971221545687319)
    ·
      refine ⟨14235335260456832318530979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9490223506971221545687319 14235335260456832318530979)
      ·
        refine ⟨21353002890685248477796469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14235335260456832318530979 21353002890685248477796469)
        ·
          refine ⟨2001844021001742044793419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21353002890685248477796469 2001844021001742044793419)
          ·
            refine ⟨3002766031502613067190129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001844021001742044793419 3002766031502613067190129)
            ·
              refine ⟨2252074523626959800392597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002766031502613067190129 2252074523626959800392597)
              ·
                refine ⟨105565993295013740643403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2252074523626959800392597 105565993295013740643403)
                ·
                  rfl

theorem cell21_1387726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_1387726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387726 prefixEnd_1387726 := by exact prefixLift 1387726
  have htrace : WordTrace (prefixWord ++ tailWord_1387726) baseStart_1387726 baseEnd_1387726 := by
    simpa [prefixWord, tailWord_1387726, baseEnd_1387726] using wordTrace_append hprefix tailTrace_1387726
  have hstable : (prefixWord ++ tailWord_1387726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387726).length < 2 ^ (prefixWord ++ tailWord_1387726).sum := by decide
  have hdescent : baseEnd_1387726 < baseStart_1387726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387774 : List Nat := [4, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_1387774 : Nat := 118140960795 + 1387774 * 2 ^ 59
def prefixEnd_1387774 : Nat := 4983230072969 + 3 ^ 40 * 1387774 * 2
def baseEnd_1387774 : Nat := 316708934139003805130111

theorem tailTrace_1387774 : CollatzResearch.WordTrace tailWord_1387774 prefixEnd_1387774 316708934139003805130111 := by
  unfold tailWord_1387774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6327034509292410721843297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33744184049559523849830917 6327034509292410721843297)
  ·
    refine ⟨4745275881969308041382473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6327034509292410721843297 4745275881969308041382473)
    ·
      refine ⟨3558956911476981031036855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4745275881969308041382473 3558956911476981031036855)
      ·
        refine ⟨5338435367215471546555283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3558956911476981031036855 5338435367215471546555283)
        ·
          refine ⟨8007653050823207319832925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5338435367215471546555283 8007653050823207319832925)
          ·
            refine ⟨3002869894058702744937347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8007653050823207319832925 3002869894058702744937347)
            ·
              refine ⟨4504304841088054117406021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002869894058702744937347 4504304841088054117406021)
              ·
                refine ⟨844557157704010147013629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4504304841088054117406021 844557157704010147013629)
                ·
                  refine ⟨316708934139003805130111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844557157704010147013629 316708934139003805130111)
                  ·
                    rfl

theorem cell21_1387774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_1387774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387774 prefixEnd_1387774 := by exact prefixLift 1387774
  have htrace : WordTrace (prefixWord ++ tailWord_1387774) baseStart_1387774 baseEnd_1387774 := by
    simpa [prefixWord, tailWord_1387774, baseEnd_1387774] using wordTrace_append hprefix tailTrace_1387774
  have hstable : (prefixWord ++ tailWord_1387774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387774).length < 2 ^ (prefixWord ++ tailWord_1387774).sum := by decide
  have hdescent : baseEnd_1387774 < baseStart_1387774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387802 : List Nat := [3, 1, 1, 3, 3, 2, 3, 5]
def baseStart_1387802 : Nat := 118140960795 + 1387802 * 2 ^ 59
def prefixEnd_1387802 : Nat := 4983230072969 + 3 ^ 40 * 1387802 * 2
def baseEnd_1387802 : Nat := 105571774706827326221129

theorem tailTrace_1387802 : CollatzResearch.WordTrace tailWord_1387802 prefixEnd_1387802 105571774706827326221129 := by
  unfold tailWord_1387802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12654324329559461639191415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33744864878825231037843773 12654324329559461639191415)
  ·
    refine ⟨18981486494339192458787123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12654324329559461639191415 18981486494339192458787123)
    ·
      refine ⟨28472229741508788688180685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18981486494339192458787123 28472229741508788688180685)
      ·
        refine ⟨10677086153065795758067757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28472229741508788688180685 10677086153065795758067757)
        ·
          refine ⟨4003907307399673409275409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10677086153065795758067757 4003907307399673409275409)
          ·
            refine ⟨3002930480549755056956557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4003907307399673409275409 3002930480549755056956557)
            ·
              refine ⟨1126098930206158146358709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3002930480549755056956557 1126098930206158146358709)
              ·
                refine ⟨105571774706827326221129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1126098930206158146358709 105571774706827326221129)
                ·
                  rfl

theorem cell21_1387802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_1387802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387802 prefixEnd_1387802 := by exact prefixLift 1387802
  have htrace : WordTrace (prefixWord ++ tailWord_1387802) baseStart_1387802 baseEnd_1387802 := by
    simpa [prefixWord, tailWord_1387802, baseEnd_1387802] using wordTrace_append hprefix tailTrace_1387802
  have hstable : (prefixWord ++ tailWord_1387802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387802).length < 2 ^ (prefixWord ++ tailWord_1387802).sum := by decide
  have hdescent : baseEnd_1387802 < baseStart_1387802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387833 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 5]
def baseStart_1387833 : Nat := 118140960795 + 1387833 * 2 ^ 59
def prefixEnd_1387833 : Nat := 4983230072969 + 3 ^ 40 * 1387833 * 2
def baseEnd_1387833 : Nat := 316722398742832813646657

theorem tailTrace_1387833 : CollatzResearch.WordTrace tailWord_1387833 prefixEnd_1387833 316722398742832813646657 := by
  unfold tailWord_1387833
  simp only [CollatzResearch.WordTrace]
  refine ⟨50618427981125538851144153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33745618654083692567429435 50618427981125538851144153)
  ·
    refine ⟨37963820985844154138358115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50618427981125538851144153 37963820985844154138358115)
    ·
      refine ⟨56945731478766231207537173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37963820985844154138358115 56945731478766231207537173)
      ·
        refine ⟨2669331163067167087853305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56945731478766231207537173 2669331163067167087853305)
        ·
          refine ⟨2001998372300375315889979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2669331163067167087853305 2001998372300375315889979)
          ·
            refine ⟨3002997558450562973834969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001998372300375315889979 3002997558450562973834969)
            ·
              refine ⟨2252248168837922230376227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002997558450562973834969 2252248168837922230376227)
              ·
                refine ⟨3378372253256883345564341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252248168837922230376227 3378372253256883345564341)
                ·
                  refine ⟨316722398742832813646657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3378372253256883345564341 316722398742832813646657)
                  ·
                    rfl

theorem cell21_1387833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_1387833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387833 prefixEnd_1387833 := by exact prefixLift 1387833
  have htrace : WordTrace (prefixWord ++ tailWord_1387833) baseStart_1387833 baseEnd_1387833 := by
    simpa [prefixWord, tailWord_1387833, baseEnd_1387833] using wordTrace_append hprefix tailTrace_1387833
  have hstable : (prefixWord ++ tailWord_1387833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387833).length < 2 ^ (prefixWord ++ tailWord_1387833).sum := by decide
  have hdescent : baseEnd_1387833 < baseStart_1387833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387853 : List Nat := [1, 6, 1, 3, 2, 1, 2, 5]
def baseStart_1387853 : Nat := 118140960795 + 1387853 * 2 ^ 59
def prefixEnd_1387853 : Nat := 4983230072969 + 3 ^ 40 * 1387853 * 2
def baseEnd_1387853 : Nat := 105575654338439074437761

theorem tailTrace_1387853 : CollatzResearch.WordTrace tailWord_1387853 prefixEnd_1387853 105575654338439074437761 := by
  unfold tailWord_1387853
  simp only [CollatzResearch.WordTrace]
  refine ⟨50619157441053082266872213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33746104960702054844581475 50619157441053082266872213)
  ·
    refine ⟨2372773005049363231259635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50619157441053082266872213 2372773005049363231259635)
    ·
      refine ⟨3559159507574044846889453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2372773005049363231259635 3559159507574044846889453)
      ·
        refine ⟨1334684815340266817583545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3559159507574044846889453 1334684815340266817583545)
        ·
          refine ⟨1001013611505200113187659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1334684815340266817583545 1001013611505200113187659)
          ·
            refine ⟨1501520417257800169781489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001013611505200113187659 1501520417257800169781489)
            ·
              refine ⟨1126140312943350127336117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1501520417257800169781489 1126140312943350127336117)
              ·
                refine ⟨105575654338439074437761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1126140312943350127336117 105575654338439074437761)
                ·
                  rfl

theorem cell21_1387853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 5].length) (baseStart_1387853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387853 prefixEnd_1387853 := by exact prefixLift 1387853
  have htrace : WordTrace (prefixWord ++ tailWord_1387853) baseStart_1387853 baseEnd_1387853 := by
    simpa [prefixWord, tailWord_1387853, baseEnd_1387853] using wordTrace_append hprefix tailTrace_1387853
  have hstable : (prefixWord ++ tailWord_1387853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387853).length < 2 ^ (prefixWord ++ tailWord_1387853).sum := by decide
  have hdescent : baseEnd_1387853 < baseStart_1387853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387861 : List Nat := [1, 3, 2, 2, 3, 2, 1, 7]
def baseStart_1387861 : Nat := 118140960795 + 1387861 * 2 ^ 59
def prefixEnd_1387861 : Nat := 4983230072969 + 3 ^ 40 * 1387861 * 2
def baseEnd_1387861 : Nat := 105576262908103662393311

theorem tailTrace_1387861 : CollatzResearch.WordTrace tailWord_1387861 prefixEnd_1387861 105576262908103662393311 := by
  unfold tailWord_1387861
  simp only [CollatzResearch.WordTrace]
  refine ⟨50619449225024099633163437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33746299483349399755442291 50619449225024099633163437)
  ·
    refine ⟨18982293459384037362436289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50619449225024099633163437 18982293459384037362436289)
    ·
      refine ⟨14236720094538028021827217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18982293459384037362436289 14236720094538028021827217)
      ·
        refine ⟨10677540070903521016370413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14236720094538028021827217 10677540070903521016370413)
        ·
          refine ⟨4004077526588820381138905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10677540070903521016370413 4004077526588820381138905)
          ·
            refine ⟨3003058144941615285854179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4004077526588820381138905 3003058144941615285854179)
            ·
              refine ⟨4504587217412422928781269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3003058144941615285854179 4504587217412422928781269)
              ·
                refine ⟨105576262908103662393311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4504587217412422928781269 105576262908103662393311)
                ·
                  rfl

theorem cell21_1387861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 7].length) (baseStart_1387861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1387861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1387861 prefixEnd_1387861 := by exact prefixLift 1387861
  have htrace : WordTrace (prefixWord ++ tailWord_1387861) baseStart_1387861 baseEnd_1387861 := by
    simpa [prefixWord, tailWord_1387861, baseEnd_1387861] using wordTrace_append hprefix tailTrace_1387861
  have hstable : (prefixWord ++ tailWord_1387861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387861).length < 2 ^ (prefixWord ++ tailWord_1387861).sum := by decide
  have hdescent : baseEnd_1387861 < baseStart_1387861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388041 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 8]
def baseStart_1388041 : Nat := 118140960795 + 1388041 * 2 ^ 59
def prefixEnd_1388041 : Nat := 4983230072969 + 3 ^ 40 * 1388041 * 2
def baseEnd_1388041 : Nat := 316769867176670674179565

theorem tailTrace_1388041 : CollatzResearch.WordTrace tailWord_1388041 prefixEnd_1388041 316769867176670674179565 := by
  unfold tailWord_1388041
  simp only [CollatzResearch.WordTrace]
  refine ⟨50626014364371990374715977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33750676242914660249810651 50626014364371990374715977)
  ·
    refine ⟨37969510773278992781036983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50626014364371990374715977 37969510773278992781036983)
    ·
      refine ⟨56954266159918489171555475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37969510773278992781036983 56954266159918489171555475)
      ·
        refine ⟨85431399239877733757333213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56954266159918489171555475 85431399239877733757333213)
        ·
          refine ⟨32036774714954150158999955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85431399239877733757333213 32036774714954150158999955)
          ·
            refine ⟨48055162072431225238499933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32036774714954150158999955 48055162072431225238499933)
            ·
              refine ⟨18020685777161709464437475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48055162072431225238499933 18020685777161709464437475)
              ·
                refine ⟨27031028665742564196656213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18020685777161709464437475 27031028665742564196656213)
                ·
                  refine ⟨316769867176670674179565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27031028665742564196656213 316769867176670674179565)
                  ·
                    rfl

theorem cell21_1388041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_1388041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388041 prefixEnd_1388041 := by exact prefixLift 1388041
  have htrace : WordTrace (prefixWord ++ tailWord_1388041) baseStart_1388041 baseEnd_1388041 := by
    simpa [prefixWord, tailWord_1388041, baseEnd_1388041] using wordTrace_append hprefix tailTrace_1388041
  have hstable : (prefixWord ++ tailWord_1388041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388041).length < 2 ^ (prefixWord ++ tailWord_1388041).sum := by decide
  have hdescent : baseEnd_1388041 < baseStart_1388041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388058 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_1388058 : Nat := 118140960795 + 1388058 * 2 ^ 59
def prefixEnd_1388058 : Nat := 4983230072969 + 3 ^ 40 * 1388058 * 2
def baseEnd_1388058 : Nat := 316773746808282422396197

theorem tailTrace_1388058 : CollatzResearch.WordTrace tailWord_1388058 prefixEnd_1388058 316773746808282422396197 := by
  unfold tailWord_1388058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12656658601327600569521207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33751089603540268185389885 12656658601327600569521207)
  ·
    refine ⟨18984987901991400854281811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12656658601327600569521207 18984987901991400854281811)
    ·
      refine ⟨28477481852987101281422717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18984987901991400854281811 28477481852987101281422717)
      ·
        refine ⟨10679055694870162980533519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28477481852987101281422717 10679055694870162980533519)
        ·
          refine ⟨16018583542305244470800279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10679055694870162980533519 16018583542305244470800279)
          ·
            refine ⟨24027875313457866706200419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16018583542305244470800279 24027875313457866706200419)
            ·
              refine ⟨36041812970186800059300629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24027875313457866706200419 36041812970186800059300629)
              ·
                refine ⟨1689459982977506252779717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36041812970186800059300629 1689459982977506252779717)
                ·
                  refine ⟨316773746808282422396197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1689459982977506252779717 316773746808282422396197)
                  ·
                    rfl

theorem cell21_1388058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_1388058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388058 prefixEnd_1388058 := by exact prefixLift 1388058
  have htrace : WordTrace (prefixWord ++ tailWord_1388058) baseStart_1388058 baseEnd_1388058 := by
    simpa [prefixWord, tailWord_1388058, baseEnd_1388058] using wordTrace_append hprefix tailTrace_1388058
  have hstable : (prefixWord ++ tailWord_1388058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388058).length < 2 ^ (prefixWord ++ tailWord_1388058).sum := by decide
  have hdescent : baseEnd_1388058 < baseStart_1388058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388230 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1388230 : Nat := 118140960795 + 1388230 * 2 ^ 59
def prefixEnd_1388230 : Nat := 4983230072969 + 3 ^ 40 * 1388230 * 2
def baseEnd_1388230 : Nat := 316812999551648345529179

theorem tailTrace_1388230 : CollatzResearch.WordTrace tailWord_1388230 prefixEnd_1388230 316812999551648345529179 := by
  unfold tailWord_1388230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582278367521477364167067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33755271840458183768897429 1582278367521477364167067)
  ·
    refine ⟨2373417551282216046250601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582278367521477364167067 2373417551282216046250601)
    ·
      refine ⟨1780063163461662034687951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2373417551282216046250601 1780063163461662034687951)
      ·
        refine ⟨2670094745192493052031927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780063163461662034687951 2670094745192493052031927)
        ·
          refine ⟨4005142117788739578047891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670094745192493052031927 4005142117788739578047891)
          ·
            refine ⟨6007713176683109367071837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005142117788739578047891 6007713176683109367071837)
            ·
              refine ⟨2252892441256166012651939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6007713176683109367071837 2252892441256166012651939)
              ·
                refine ⟨3379338661884249018977909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252892441256166012651939 3379338661884249018977909)
                ·
                  refine ⟨316812999551648345529179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3379338661884249018977909 316812999551648345529179)
                  ·
                    rfl

theorem cell21_1388230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1388230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388230 prefixEnd_1388230 := by exact prefixLift 1388230
  have htrace : WordTrace (prefixWord ++ tailWord_1388230) baseStart_1388230 baseEnd_1388230 := by
    simpa [prefixWord, tailWord_1388230, baseEnd_1388230] using wordTrace_append hprefix tailTrace_1388230
  have hstable : (prefixWord ++ tailWord_1388230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388230).length < 2 ^ (prefixWord ++ tailWord_1388230).sum := by decide
  have hdescent : baseEnd_1388230 < baseStart_1388230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388244 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1388244 : Nat := 118140960795 + 1388244 * 2 ^ 59
def prefixEnd_1388244 : Nat := 4983230072969 + 3 ^ 40 * 1388244 * 2
def baseEnd_1388244 : Nat := 316816194542387432295817

theorem tailTrace_1388244 : CollatzResearch.WordTrace tailWord_1388244 prefixEnd_1388244 316816194542387432295817 := by
  unfold tailWord_1388244
  simp only [CollatzResearch.WordTrace]
  refine ⟨25316709191318278022177893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33755612255091037362903857 25316709191318278022177893)
  ·
    refine ⟨4746882973372177129158355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25316709191318278022177893 4746882973372177129158355)
    ·
      refine ⟨7120324460058265693737533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4746882973372177129158355 7120324460058265693737533)
      ·
        refine ⟨2670121672521849635151575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7120324460058265693737533 2670121672521849635151575)
        ·
          refine ⟨4005182508782774452727363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670121672521849635151575 4005182508782774452727363)
          ·
            refine ⟨6007773763174161679091045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005182508782774452727363 6007773763174161679091045)
            ·
              refine ⟨1126457580595155314829571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6007773763174161679091045 1126457580595155314829571)
              ·
                refine ⟨1689686370892732972244357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126457580595155314829571 1689686370892732972244357)
                ·
                  refine ⟨316816194542387432295817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1689686370892732972244357 316816194542387432295817)
                  ·
                    rfl

theorem cell21_1388244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1388244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388244 prefixEnd_1388244 := by exact prefixLift 1388244
  have htrace : WordTrace (prefixWord ++ tailWord_1388244) baseStart_1388244 baseEnd_1388244 := by
    simpa [prefixWord, tailWord_1388244, baseEnd_1388244] using wordTrace_append hprefix tailTrace_1388244
  have hstable : (prefixWord ++ tailWord_1388244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388244).length < 2 ^ (prefixWord ++ tailWord_1388244).sum := by decide
  have hdescent : baseEnd_1388244 < baseStart_1388244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388289 : List Nat := [1, 2, 4, 1, 1, 1, 6, 2, 3]
def baseStart_1388289 : Nat := 118140960795 + 1388289 * 2 ^ 59
def prefixEnd_1388289 : Nat := 4983230072969 + 3 ^ 40 * 1388289 * 2
def baseEnd_1388289 : Nat := 316826464155477354045725

theorem tailTrace_1388289 : CollatzResearch.WordTrace tailWord_1388289 prefixEnd_1388289 316826464155477354045725 := by
  unfold tailWord_1388289
  simp only [CollatzResearch.WordTrace]
  refine ⟨50635059667473528729743921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33756706444982352486495947 50635059667473528729743921)
  ·
    refine ⟨37976294750605146547307941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50635059667473528729743921 37976294750605146547307941)
    ·
      refine ⟨7120555265738464977620239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37976294750605146547307941 7120555265738464977620239)
      ·
        refine ⟨10680832898607697466430359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7120555265738464977620239 10680832898607697466430359)
        ·
          refine ⟨16021249347911546199645539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10680832898607697466430359 16021249347911546199645539)
          ·
            refine ⟨24031874021867319299468309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16021249347911546199645539 24031874021867319299468309)
            ·
              refine ⟨1126494094775030592162577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24031874021867319299468309 1126494094775030592162577)
              ·
                refine ⟨844870571081272944121933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1126494094775030592162577 844870571081272944121933)
                ·
                  refine ⟨316826464155477354045725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844870571081272944121933 316826464155477354045725)
                  ·
                    rfl

theorem cell21_1388289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 3].length) (baseStart_1388289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388289 prefixEnd_1388289 := by exact prefixLift 1388289
  have htrace : WordTrace (prefixWord ++ tailWord_1388289) baseStart_1388289 baseEnd_1388289 := by
    simpa [prefixWord, tailWord_1388289, baseEnd_1388289] using wordTrace_append hprefix tailTrace_1388289
  have hstable : (prefixWord ++ tailWord_1388289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388289).length < 2 ^ (prefixWord ++ tailWord_1388289).sum := by decide
  have hdescent : baseEnd_1388289 < baseStart_1388289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388300 : List Nat := [2, 2, 1, 2, 2, 1, 5, 6]
def baseStart_1388300 : Nat := 118140960795 + 1388300 * 2 ^ 59
def prefixEnd_1388300 : Nat := 4983230072969 + 3 ^ 40 * 1388300 * 2
def baseEnd_1388300 : Nat := 105609658168447926454123

theorem tailTrace_1388300 : CollatzResearch.WordTrace tailWord_1388300 prefixEnd_1388300 105609658168447926454123 := by
  unfold tailWord_1388300
  simp only [CollatzResearch.WordTrace]
  refine ⟨25317730435216838804197177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33756973913622451738929569 25317730435216838804197177)
  ·
    refine ⟨18988297826412629103147883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25317730435216838804197177 18988297826412629103147883)
    ·
      refine ⟨28482446739618943654721825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18988297826412629103147883 28482446739618943654721825)
      ·
        refine ⟨21361835054714207741041369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28482446739618943654721825 21361835054714207741041369)
        ·
          refine ⟨16021376291035655805781027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21361835054714207741041369 16021376291035655805781027)
          ·
            refine ⟨24032064436553483708671541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16021376291035655805781027 24032064436553483708671541)
            ·
              refine ⟨2253006040926889097687957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24032064436553483708671541 2253006040926889097687957)
              ·
                refine ⟨105609658168447926454123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2253006040926889097687957 105609658168447926454123)
                ·
                  rfl

theorem cell21_1388300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_1388300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388300 prefixEnd_1388300 := by exact prefixLift 1388300
  have htrace : WordTrace (prefixWord ++ tailWord_1388300) baseStart_1388300 baseEnd_1388300 := by
    simpa [prefixWord, tailWord_1388300, baseEnd_1388300] using wordTrace_append hprefix tailTrace_1388300
  have hstable : (prefixWord ++ tailWord_1388300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388300).length < 2 ^ (prefixWord ++ tailWord_1388300).sum := by decide
  have hdescent : baseEnd_1388300 < baseStart_1388300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388348 : List Nat := [2, 2, 2, 2, 1, 1, 4, 4, 3]
def baseStart_1388348 : Nat := 118140960795 + 1388348 * 2 ^ 59
def prefixEnd_1388348 : Nat := 4983230072969 + 3 ^ 40 * 1388348 * 2
def baseEnd_1388348 : Nat := 316839928759306362562271

theorem tailTrace_1388348 : CollatzResearch.WordTrace tailWord_1388348 prefixEnd_1388348 316839928759306362562271 := by
  unfold tailWord_1388348
  simp only [CollatzResearch.WordTrace]
  refine ⟨25318605787129890903070849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33758141049506521204094465 25318605787129890903070849)
  ·
    refine ⟨18988954340347418177303137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25318605787129890903070849 18988954340347418177303137)
    ·
      refine ⟨14241715755260563632977353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18988954340347418177303137 14241715755260563632977353)
      ·
        refine ⟨10681286816445422724733015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14241715755260563632977353 10681286816445422724733015)
        ·
          refine ⟨16021930224668134087099523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10681286816445422724733015 16021930224668134087099523)
          ·
            refine ⟨24032895337002201130649285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16021930224668134087099523 24032895337002201130649285)
            ·
              refine ⟨4506167875687912711996741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24032895337002201130649285 4506167875687912711996741)
              ·
                refine ⟨844906476691483633499389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4506167875687912711996741 844906476691483633499389)
                ·
                  refine ⟨316839928759306362562271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844906476691483633499389 316839928759306362562271)
                  ·
                    rfl

theorem cell21_1388348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_1388348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388348 prefixEnd_1388348 := by exact prefixLift 1388348
  have htrace : WordTrace (prefixWord ++ tailWord_1388348) baseStart_1388348 baseEnd_1388348 := by
    simpa [prefixWord, tailWord_1388348, baseEnd_1388348] using wordTrace_append hprefix tailTrace_1388348
  have hstable : (prefixWord ++ tailWord_1388348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388348).length < 2 ^ (prefixWord ++ tailWord_1388348).sum := by decide
  have hdescent : baseEnd_1388348 < baseStart_1388348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388455 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 4]
def baseStart_1388455 : Nat := 118140960795 + 1388455 * 2 ^ 59
def prefixEnd_1388455 : Nat := 4983230072969 + 3 ^ 40 * 1388455 * 2
def baseEnd_1388455 : Nat := 316864347617097954278719

theorem tailTrace_1388455 : CollatzResearch.WordTrace tailWord_1388455 prefixEnd_1388455 316864347617097954278719 := by
  unfold tailWord_1388455
  simp only [CollatzResearch.WordTrace]
  refine ⟨50641114184872139080286819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33760742789914759386857879 50641114184872139080286819)
  ·
    refine ⟨75961671277308208620430229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50641114184872139080286819 75961671277308208620430229)
    ·
      refine ⟨3560703341123822279082667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75961671277308208620430229 3560703341123822279082667)
      ·
        refine ⟨5341055011685733418624001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560703341123822279082667 5341055011685733418624001)
        ·
          refine ⟨4005791258764300063968001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5341055011685733418624001 4005791258764300063968001)
          ·
            refine ⟨3004343444073225047976001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4005791258764300063968001 3004343444073225047976001)
            ·
              refine ⟨2253257583054918785982001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3004343444073225047976001 2253257583054918785982001)
              ·
                refine ⟨1689943187291189089486501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2253257583054918785982001 1689943187291189089486501)
                ·
                  refine ⟨316864347617097954278719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1689943187291189089486501 316864347617097954278719)
                  ·
                    rfl

theorem cell21_1388455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 4].length) (baseStart_1388455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388455 prefixEnd_1388455 := by exact prefixLift 1388455
  have htrace : WordTrace (prefixWord ++ tailWord_1388455) baseStart_1388455 baseEnd_1388455 := by
    simpa [prefixWord, tailWord_1388455, baseEnd_1388455] using wordTrace_append hprefix tailTrace_1388455
  have hstable : (prefixWord ++ tailWord_1388455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388455).length < 2 ^ (prefixWord ++ tailWord_1388455).sum := by decide
  have hdescent : baseEnd_1388455 < baseStart_1388455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388466 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1388466 : Nat := 118140960795 + 1388466 * 2 ^ 59
def prefixEnd_1388466 : Nat := 4983230072969 + 3 ^ 40 * 1388466 * 2
def baseEnd_1388466 : Nat := 316866857966964379595363

theorem tailTrace_1388466 : CollatzResearch.WordTrace tailWord_1388466 prefixEnd_1388466 316866857966964379595363 := by
  unfold tailWord_1388466
  simp only [CollatzResearch.WordTrace]
  refine ⟨12660378846958071989734313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33761010258554858639291501 12660378846958071989734313)
  ·
    refine ⟨9495284135218553992300735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12660378846958071989734313 9495284135218553992300735)
    ·
      refine ⟨14242926202827830988451103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9495284135218553992300735 14242926202827830988451103)
      ·
        refine ⟨21364389304241746482676655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14242926202827830988451103 21364389304241746482676655)
        ·
          refine ⟨32046583956362619724014983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21364389304241746482676655 32046583956362619724014983)
          ·
            refine ⟨48069875934543929586022475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32046583956362619724014983 48069875934543929586022475)
            ·
              refine ⟨72104813901815894379033713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48069875934543929586022475 72104813901815894379033713)
              ·
                refine ⟨54078610426361920784275285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72104813901815894379033713 54078610426361920784275285)
                ·
                  refine ⟨316866857966964379595363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54078610426361920784275285 316866857966964379595363)
                  ·
                    rfl

theorem cell21_1388466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1388466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388466 prefixEnd_1388466 := by exact prefixLift 1388466
  have htrace : WordTrace (prefixWord ++ tailWord_1388466) baseStart_1388466 baseEnd_1388466 := by
    simpa [prefixWord, tailWord_1388466, baseEnd_1388466] using wordTrace_append hprefix tailTrace_1388466
  have hstable : (prefixWord ++ tailWord_1388466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388466).length < 2 ^ (prefixWord ++ tailWord_1388466).sum := by decide
  have hdescent : baseEnd_1388466 < baseStart_1388466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388469 : List Nat := [1, 3, 3, 2, 1, 4, 1, 6]
def baseStart_1388469 : Nat := 118140960795 + 1388469 * 2 ^ 59
def prefixEnd_1388469 : Nat := 4983230072969 + 3 ^ 40 * 1388469 * 2
def baseEnd_1388469 : Nat := 105622514202612347015119

theorem tailTrace_1388469 : CollatzResearch.WordTrace tailWord_1388469 prefixEnd_1388469 105622514202612347015119 := by
  unfold tailWord_1388469
  simp only [CollatzResearch.WordTrace]
  refine ⟨50641624806821419471296461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33761083204547612980864307 50641624806821419471296461)
  ·
    refine ⟨18990609302558032301736173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50641624806821419471296461 18990609302558032301736173)
    ·
      refine ⟨7121478488459262113151065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18990609302558032301736173 7121478488459262113151065)
      ·
        refine ⟨5341108866344446584863299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7121478488459262113151065 5341108866344446584863299)
        ·
          refine ⟨8011663299516669877294949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5341108866344446584863299 8011663299516669877294949)
          ·
            refine ⟨1502186868659375601992803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8011663299516669877294949 1502186868659375601992803)
            ·
              refine ⟨2253280302989063402989205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502186868659375601992803 2253280302989063402989205)
              ·
                refine ⟨105622514202612347015119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2253280302989063402989205 105622514202612347015119)
                ·
                  rfl

theorem cell21_1388469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 6].length) (baseStart_1388469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388469 prefixEnd_1388469 := by exact prefixLift 1388469
  have htrace : WordTrace (prefixWord ++ tailWord_1388469) baseStart_1388469 baseEnd_1388469 := by
    simpa [prefixWord, tailWord_1388469, baseEnd_1388469] using wordTrace_append hprefix tailTrace_1388469
  have hstable : (prefixWord ++ tailWord_1388469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388469).length < 2 ^ (prefixWord ++ tailWord_1388469).sum := by decide
  have hdescent : baseEnd_1388469 < baseStart_1388469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388649 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 4]
def baseStart_1388649 : Nat := 118140960795 + 1388649 * 2 ^ 59
def prefixEnd_1388649 : Nat := 4983230072969 + 3 ^ 40 * 1388649 * 2
def baseEnd_1388649 : Nat := 316908621060196728044989

theorem tailTrace_1388649 : CollatzResearch.WordTrace tailWord_1388649 prefixEnd_1388649 316908621060196728044989 := by
  unfold tailWord_1388649
  simp only [CollatzResearch.WordTrace]
  refine ⟨50648189946169310212849001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33765459964112873475232667 50648189946169310212849001)
  ·
    refine ⟨37986142459626982659636751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50648189946169310212849001 37986142459626982659636751)
    ·
      refine ⟨56979213689440473989455127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37986142459626982659636751 56979213689440473989455127)
      ·
        refine ⟨85468820534160710984182691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56979213689440473989455127 85468820534160710984182691)
        ·
          refine ⟨128203230801241066476274037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85468820534160710984182691 128203230801241066476274037)
          ·
            refine ⟨12019052887616349982150691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128203230801241066476274037 12019052887616349982150691)
            ·
              refine ⟨18028579331424524973226037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12019052887616349982150691 18028579331424524973226037)
              ·
                refine ⟨1690179312321049216239941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18028579331424524973226037 1690179312321049216239941)
                ·
                  refine ⟨316908621060196728044989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1690179312321049216239941 316908621060196728044989)
                  ·
                    rfl

theorem cell21_1388649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_1388649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388649 prefixEnd_1388649 := by exact prefixLift 1388649
  have htrace : WordTrace (prefixWord ++ tailWord_1388649) baseStart_1388649 baseEnd_1388649 := by
    simpa [prefixWord, tailWord_1388649, baseEnd_1388649] using wordTrace_append hprefix tailTrace_1388649
  have hstable : (prefixWord ++ tailWord_1388649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388649).length < 2 ^ (prefixWord ++ tailWord_1388649).sum := by decide
  have hdescent : baseEnd_1388649 < baseStart_1388649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388680 : List Nat := [2, 1, 3, 4, 1, 2, 8]
def baseStart_1388680 : Nat := 118140960795 + 1388680 * 2 ^ 59
def prefixEnd_1388680 : Nat := 4983230072969 + 3 ^ 40 * 1388680 * 2
def baseEnd_1388680 : Nat := 35212855075838618114251

theorem tailTrace_1388680 : CollatzResearch.WordTrace tailWord_1388680 prefixEnd_1388680 35212855075838618114251 := by
  unfold tailWord_1388680
  simp only [CollatzResearch.WordTrace]
  refine ⟨25324660304528501253613747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33766213739371335004818329 25324660304528501253613747)
  ·
    refine ⟨37986990456792751880420621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25324660304528501253613747 37986990456792751880420621)
    ·
      refine ⟨14245121421297281955157733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37986990456792751880420621 14245121421297281955157733)
      ·
        refine ⟨2670960266493240366592075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14245121421297281955157733 2670960266493240366592075)
        ·
          refine ⟨4006440399739860549888113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670960266493240366592075 4006440399739860549888113)
          ·
            refine ⟨3004830299804895412416085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4006440399739860549888113 3004830299804895412416085)
            ·
              refine ⟨35212855075838618114251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3004830299804895412416085 35212855075838618114251)
              ·
                rfl

theorem cell21_1388680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 8].length) (baseStart_1388680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388680 prefixEnd_1388680 := by exact prefixLift 1388680
  have htrace : WordTrace (prefixWord ++ tailWord_1388680) baseStart_1388680 baseEnd_1388680 := by
    simpa [prefixWord, tailWord_1388680, baseEnd_1388680] using wordTrace_append hprefix tailTrace_1388680
  have hstable : (prefixWord ++ tailWord_1388680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388680).length < 2 ^ (prefixWord ++ tailWord_1388680).sum := by decide
  have hdescent : baseEnd_1388680 < baseStart_1388680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388784 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_1388784 : Nat := 118140960795 + 1388784 * 2 ^ 59
def prefixEnd_1388784 : Nat := 4983230072969 + 3 ^ 40 * 1388784 * 2
def baseEnd_1388784 : Nat := 316939429899466493294713

theorem tailTrace_1388784 : CollatzResearch.WordTrace tailWord_1388784 prefixEnd_1388784 316939429899466493294713 := by
  unfold tailWord_1388784
  simp only [CollatzResearch.WordTrace]
  refine ⟨25326556900340114134506703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33768742533786818846008937 25326556900340114134506703)
  ·
    refine ⟨37989835350510171201760055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25326556900340114134506703 37989835350510171201760055)
    ·
      refine ⟨56984753025765256802640083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37989835350510171201760055 56984753025765256802640083)
      ·
        refine ⟨85477129538647885203960125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56984753025765256802640083 85477129538647885203960125)
        ·
          refine ⟨32053923576992956951485047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85477129538647885203960125 32053923576992956951485047)
          ·
            refine ⟨48080885365489435427227571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32053923576992956951485047 48080885365489435427227571)
            ·
              refine ⟨72121328048234153140841357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48080885365489435427227571 72121328048234153140841357)
              ·
                refine ⟨27045498018087807427815509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72121328048234153140841357 27045498018087807427815509)
                ·
                  refine ⟨316939429899466493294713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27045498018087807427815509 316939429899466493294713)
                  ·
                    rfl

theorem cell21_1388784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_1388784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388784 prefixEnd_1388784 := by exact prefixLift 1388784
  have htrace : WordTrace (prefixWord ++ tailWord_1388784) baseStart_1388784 baseEnd_1388784 := by
    simpa [prefixWord, tailWord_1388784, baseEnd_1388784] using wordTrace_append hprefix tailTrace_1388784
  have hstable : (prefixWord ++ tailWord_1388784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388784).length < 2 ^ (prefixWord ++ tailWord_1388784).sum := by decide
  have hdescent : baseEnd_1388784 < baseStart_1388784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388787 : List Nat := [1, 1, 1, 2, 2, 4, 2, 5, 3]
def baseStart_1388787 : Nat := 118140960795 + 1388787 * 2 ^ 59
def prefixEnd_1388787 : Nat := 4983230072969 + 3 ^ 40 * 1388787 * 2
def baseEnd_1388787 : Nat := 316940114540339154744707

theorem tailTrace_1388787 : CollatzResearch.WordTrace tailWord_1388787 prefixEnd_1388787 316940114540339154744707 := by
  unfold tailWord_1388787
  simp only [CollatzResearch.WordTrace]
  refine ⟨50653223219669359781372615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33768815479779573187581743 50653223219669359781372615)
  ·
    refine ⟨75979834829504039672058923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50653223219669359781372615 75979834829504039672058923)
    ·
      refine ⟨113969752244256059508088385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75979834829504039672058923 113969752244256059508088385)
      ·
        refine ⟨85477314183192044631066289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113969752244256059508088385 85477314183192044631066289)
        ·
          refine ⟨64107985637394033473299717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85477314183192044631066289 64107985637394033473299717)
          ·
            refine ⟨12020247307011381276243697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64107985637394033473299717 12020247307011381276243697)
            ·
              refine ⟨9015185480258535957182773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12020247307011381276243697 9015185480258535957182773)
              ·
                refine ⟨845173638774237745985885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9015185480258535957182773 845173638774237745985885)
                ·
                  refine ⟨316940114540339154744707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845173638774237745985885 316940114540339154744707)
                  ·
                    rfl

theorem cell21_1388787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 3].length) (baseStart_1388787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388787 prefixEnd_1388787 := by exact prefixLift 1388787
  have htrace : WordTrace (prefixWord ++ tailWord_1388787) baseStart_1388787 baseEnd_1388787 := by
    simpa [prefixWord, tailWord_1388787, baseEnd_1388787] using wordTrace_append hprefix tailTrace_1388787
  have hstable : (prefixWord ++ tailWord_1388787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388787).length < 2 ^ (prefixWord ++ tailWord_1388787).sum := by decide
  have hdescent : baseEnd_1388787 < baseStart_1388787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388863 : List Nat := [1, 1, 2, 2, 4, 1, 1, 6, 3]
def baseStart_1388863 : Nat := 118140960795 + 1388863 * 2 ^ 59
def prefixEnd_1388863 : Nat := 4983230072969 + 3 ^ 40 * 1388863 * 2
def baseEnd_1388863 : Nat := 316957458775779911477885

theorem tailTrace_1388863 : CollatzResearch.WordTrace tailWord_1388863 prefixEnd_1388863 316957458775779911477885 := by
  unfold tailWord_1388863
  simp only [CollatzResearch.WordTrace]
  refine ⟨50655995167394024761139243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33770663444929349840759495 50655995167394024761139243)
  ·
    refine ⟨75983992751091037141708865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50655995167394024761139243 75983992751091037141708865)
    ·
      refine ⟨56987994563318277856281649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75983992751091037141708865 56987994563318277856281649)
      ·
        refine ⟨42740995922488708392211237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56987994563318277856281649 42740995922488708392211237)
        ·
          refine ⟨8013936735466632823539607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42740995922488708392211237 8013936735466632823539607)
          ·
            refine ⟨12020905103199949235309411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8013936735466632823539607 12020905103199949235309411)
            ·
              refine ⟨18031357654799923852964117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12020905103199949235309411 18031357654799923852964117)
              ·
                refine ⟨845219890068746430607693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18031357654799923852964117 845219890068746430607693)
                ·
                  refine ⟨316957458775779911477885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845219890068746430607693 316957458775779911477885)
                  ·
                    rfl

theorem cell21_1388863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 3].length) (baseStart_1388863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388863 prefixEnd_1388863 := by exact prefixLift 1388863
  have htrace : WordTrace (prefixWord ++ tailWord_1388863) baseStart_1388863 baseEnd_1388863 := by
    simpa [prefixWord, tailWord_1388863, baseEnd_1388863] using wordTrace_append hprefix tailTrace_1388863
  have hstable : (prefixWord ++ tailWord_1388863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388863).length < 2 ^ (prefixWord ++ tailWord_1388863).sum := by decide
  have hdescent : baseEnd_1388863 < baseStart_1388863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388908 : List Nat := [2, 2, 1, 1, 6, 2, 7]
def baseStart_1388908 : Nat := 118140960795 + 1388908 * 2 ^ 59
def prefixEnd_1388908 : Nat := 4983230072969 + 3 ^ 40 * 1388908 * 2
def baseEnd_1388908 : Nat := 35218636487652203691977

theorem tailTrace_1388908 : CollatzResearch.WordTrace tailWord_1388908 prefixEnd_1388908 35218636487652203691977 := by
  unfold tailWord_1388908
  simp only [CollatzResearch.WordTrace]
  refine ⟨25328818226115498723263689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33771757634820664964351585 25328818226115498723263689)
  ·
    refine ⟨18996613669586624042447767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25328818226115498723263689 18996613669586624042447767)
    ·
      refine ⟨28494920504379936063671651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18996613669586624042447767 28494920504379936063671651)
      ·
        refine ⟨42742380756569904095507477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28494920504379936063671651 42742380756569904095507477)
        ·
          refine ⟨2003549097964214254476913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42742380756569904095507477 2003549097964214254476913)
          ·
            refine ⟨1502661823473160690857685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2003549097964214254476913 1502661823473160690857685)
            ·
              refine ⟨35218636487652203691977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1502661823473160690857685 35218636487652203691977)
              ·
                rfl

theorem cell21_1388908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 7].length) (baseStart_1388908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388908 prefixEnd_1388908 := by exact prefixLift 1388908
  have htrace : WordTrace (prefixWord ++ tailWord_1388908) baseStart_1388908 baseEnd_1388908 := by
    simpa [prefixWord, tailWord_1388908, baseEnd_1388908] using wordTrace_append hprefix tailTrace_1388908
  have hstable : (prefixWord ++ tailWord_1388908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388908).length < 2 ^ (prefixWord ++ tailWord_1388908).sum := by decide
  have hdescent : baseEnd_1388908 < baseStart_1388908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388967 : List Nat := [1, 1, 6, 1, 1, 11]
def baseStart_1388967 : Nat := 118140960795 + 1388967 * 2 ^ 59
def prefixEnd_1388967 : Nat := 4983230072969 + 3 ^ 40 * 1388967 * 2
def baseEnd_1388967 : Nat := 11740044184914771916457

theorem tailTrace_1388967 : CollatzResearch.WordTrace tailWord_1388967 prefixEnd_1388967 11740044184914771916457 := by
  unfold tailWord_1388967
  simp only [CollatzResearch.WordTrace]
  refine ⟨50659788359017250522925155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33773192239344833681950103 50659788359017250522925155)
  ·
    refine ⟨75989682538525875784387733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50659788359017250522925155 75989682538525875784387733)
    ·
      refine ⟨3562016368993400427393175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75989682538525875784387733 3562016368993400427393175)
      ·
        refine ⟨5343024553490100641089763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562016368993400427393175 5343024553490100641089763)
        ·
          refine ⟨8014536830235150961634645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5343024553490100641089763 8014536830235150961634645)
          ·
            refine ⟨11740044184914771916457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8014536830235150961634645 11740044184914771916457)
            ·
              rfl

theorem cell21_1388967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 11].length) (baseStart_1388967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388967 prefixEnd_1388967 := by exact prefixLift 1388967
  have htrace : WordTrace (prefixWord ++ tailWord_1388967) baseStart_1388967 baseEnd_1388967 := by
    simpa [prefixWord, tailWord_1388967, baseEnd_1388967] using wordTrace_append hprefix tailTrace_1388967
  have hstable : (prefixWord ++ tailWord_1388967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388967).length < 2 ^ (prefixWord ++ tailWord_1388967).sum := by decide
  have hdescent : baseEnd_1388967 < baseStart_1388967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388973 : List Nat := [1, 5, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1388973 : Nat := 118140960795 + 1388973 * 2 ^ 59
def prefixEnd_1388973 : Nat := 4983230072969 + 3 ^ 40 * 1388973 * 2
def baseEnd_1388973 : Nat := 316982562274444164644327

theorem tailTrace_1388973 : CollatzResearch.WordTrace tailWord_1388973 prefixEnd_1388973 316982562274444164644327 := by
  unfold tailWord_1388973
  simp only [CollatzResearch.WordTrace]
  refine ⟨50660007196995513547643573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33773338131330342365095715 50660007196995513547643573)
  ·
    refine ⟨4749375674718329395091585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50660007196995513547643573 4749375674718329395091585)
    ·
      refine ⟨3562031756038747046318689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4749375674718329395091585 3562031756038747046318689)
      ·
        refine ⟨2671523817029060284739017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3562031756038747046318689 2671523817029060284739017)
        ·
          refine ⟨2003642862771795213554263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2671523817029060284739017 2003642862771795213554263)
          ·
            refine ⟨3005464294157692820331395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003642862771795213554263 3005464294157692820331395)
            ·
              refine ⟨4508196441236539230497093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005464294157692820331395 4508196441236539230497093)
              ·
                refine ⟨845286832731851105718205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4508196441236539230497093 845286832731851105718205)
                ·
                  refine ⟨316982562274444164644327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845286832731851105718205 316982562274444164644327)
                  ·
                    rfl

theorem cell21_1388973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1388973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1388973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1388973 prefixEnd_1388973 := by exact prefixLift 1388973
  have htrace : WordTrace (prefixWord ++ tailWord_1388973) baseStart_1388973 baseEnd_1388973 := by
    simpa [prefixWord, tailWord_1388973, baseEnd_1388973] using wordTrace_append hprefix tailTrace_1388973
  have hstable : (prefixWord ++ tailWord_1388973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388973).length < 2 ^ (prefixWord ++ tailWord_1388973).sum := by decide
  have hdescent : baseEnd_1388973 < baseStart_1388973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389060 : List Nat := [2, 3, 2, 3, 1, 2, 1, 7]
def baseStart_1389060 : Nat := 118140960795 + 1389060 * 2 ^ 59
def prefixEnd_1389060 : Nat := 4983230072969 + 3 ^ 40 * 1389060 * 2
def baseEnd_1389060 : Nat := 105667472286583782231383

theorem tailTrace_1389060 : CollatzResearch.WordTrace tailWord_1389060 prefixEnd_1389060 105667472286583782231383 := by
  unfold tailWord_1389060
  simp only [CollatzResearch.WordTrace]
  refine ⟨25331590173840163703030317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33775453565120218270707089 25331590173840163703030317)
  ·
    refine ⟨9499346315190061388636369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25331590173840163703030317 9499346315190061388636369)
    ·
      refine ⟨7124509736392546041477277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9499346315190061388636369 7124509736392546041477277)
      ·
        refine ⟨2671691151147204765553979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7124509736392546041477277 2671691151147204765553979)
        ·
          refine ⟨4007536726720807148330969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671691151147204765553979 4007536726720807148330969)
          ·
            refine ⟨3005652545040605361248227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4007536726720807148330969 3005652545040605361248227)
            ·
              refine ⟨4508478817560908041872341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005652545040605361248227 4508478817560908041872341)
              ·
                refine ⟨105667472286583782231383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4508478817560908041872341 105667472286583782231383)
                ·
                  rfl

theorem cell21_1389060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_1389060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389060 prefixEnd_1389060 := by exact prefixLift 1389060
  have htrace : WordTrace (prefixWord ++ tailWord_1389060) baseStart_1389060 baseEnd_1389060 := by
    simpa [prefixWord, tailWord_1389060, baseEnd_1389060] using wordTrace_append hprefix tailTrace_1389060
  have hstable : (prefixWord ++ tailWord_1389060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389060).length < 2 ^ (prefixWord ++ tailWord_1389060).sum := by decide
  have hdescent : baseEnd_1389060 < baseStart_1389060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389091 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 5]
def baseStart_1389091 : Nat := 118140960795 + 1389091 * 2 ^ 59
def prefixEnd_1389091 : Nat := 4983230072969 + 3 ^ 40 * 1389091 * 2
def baseEnd_1389091 : Nat := 317009491482102181677419

theorem tailTrace_1389091 : CollatzResearch.WordTrace tailWord_1389091 prefixEnd_1389091 317009491482102181677419 := by
  unfold tailWord_1389091
  simp only [CollatzResearch.WordTrace]
  refine ⟨50664311010568019700439127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33776207340378679800292751 50664311010568019700439127)
  ·
    refine ⟨75996466515852029550658691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50664311010568019700439127 75996466515852029550658691)
    ·
      refine ⟨113994699773778044325988037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75996466515852029550658691 113994699773778044325988037)
      ·
        refine ⟨21374006207583383311122757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113994699773778044325988037 21374006207583383311122757)
        ·
          refine ⟨4007626163921884370835517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21374006207583383311122757 4007626163921884370835517)
          ·
            refine ⟨1502859811470706639063319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4007626163921884370835517 1502859811470706639063319)
            ·
              refine ⟨2254289717206059958594979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502859811470706639063319 2254289717206059958594979)
              ·
                refine ⟨3381434575809089937892469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254289717206059958594979 3381434575809089937892469)
                ·
                  refine ⟨317009491482102181677419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3381434575809089937892469 317009491482102181677419)
                  ·
                    rfl

theorem cell21_1389091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 5].length) (baseStart_1389091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389091 prefixEnd_1389091 := by exact prefixLift 1389091
  have htrace : WordTrace (prefixWord ++ tailWord_1389091) baseStart_1389091 baseEnd_1389091 := by
    simpa [prefixWord, tailWord_1389091, baseEnd_1389091] using wordTrace_append hprefix tailTrace_1389091
  have hstable : (prefixWord ++ tailWord_1389091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389091).length < 2 ^ (prefixWord ++ tailWord_1389091).sum := by decide
  have hdescent : baseEnd_1389091 < baseStart_1389091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389229 : List Nat := [1, 5, 2, 1, 1, 4, 2, 5]
def baseStart_1389229 : Nat := 118140960795 + 1389229 * 2 ^ 59
def prefixEnd_1389229 : Nat := 4983230072969 + 3 ^ 40 * 1389229 * 2
def baseEnd_1389229 : Nat := 105680328320748202792379

theorem tailTrace_1389229 : CollatzResearch.WordTrace tailWord_1389229 prefixEnd_1389229 105680328320748202792379 := by
  unfold tailWord_1389229
  simp only [CollatzResearch.WordTrace]
  refine ⟨50669344284068069268962741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33779562856045379512641827 50669344284068069268962741)
  ·
    refine ⟨4750251026631381493965257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50669344284068069268962741 4750251026631381493965257)
    ·
      refine ⟨3562688269973536120473943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4750251026631381493965257 3562688269973536120473943)
      ·
        refine ⟨5344032404960304180710915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562688269973536120473943 5344032404960304180710915)
        ·
          refine ⟨8016048607440456271066373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344032404960304180710915 8016048607440456271066373)
          ·
            refine ⟨1503009113895085550824945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8016048607440456271066373 1503009113895085550824945)
            ·
              refine ⟨1127256835421314163118709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1503009113895085550824945 1127256835421314163118709)
              ·
                refine ⟨105680328320748202792379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1127256835421314163118709 105680328320748202792379)
                ·
                  rfl

theorem cell21_1389229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 5].length) (baseStart_1389229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389229 prefixEnd_1389229 := by exact prefixLift 1389229
  have htrace : WordTrace (prefixWord ++ tailWord_1389229) baseStart_1389229 baseEnd_1389229 := by
    simpa [prefixWord, tailWord_1389229, baseEnd_1389229] using wordTrace_append hprefix tailTrace_1389229
  have hstable : (prefixWord ++ tailWord_1389229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389229).length < 2 ^ (prefixWord ++ tailWord_1389229).sum := by decide
  have hdescent : baseEnd_1389229 < baseStart_1389229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389271 : List Nat := [1, 1, 3, 2, 1, 5, 2, 6]
def baseStart_1389271 : Nat := 118140960795 + 1389271 * 2 ^ 59
def prefixEnd_1389271 : Nat := 4983230072969 + 3 ^ 40 * 1389271 * 2
def baseEnd_1389271 : Nat := 105683523311487289559017

theorem tailTrace_1389271 : CollatzResearch.WordTrace tailWord_1389271 prefixEnd_1389271 105683523311487289559017 := by
  unfold tailWord_1389271
  simp only [CollatzResearch.WordTrace]
  refine ⟨50670876149915910441991667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33780584099943940294661111 50670876149915910441991667)
  ·
    refine ⟨76006314224873865662987501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50670876149915910441991667 76006314224873865662987501)
    ·
      refine ⟨28502367834327699623620313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76006314224873865662987501 28502367834327699623620313)
      ·
        refine ⟨21376775875745774717715235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28502367834327699623620313 21376775875745774717715235)
        ·
          refine ⟨32065163813618662076572853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21376775875745774717715235 32065163813618662076572853)
          ·
            refine ⟨3006109107526749569678705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32065163813618662076572853 3006109107526749569678705)
            ·
              refine ⟨2254581830645062177259029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3006109107526749569678705 2254581830645062177259029)
              ·
                refine ⟨105683523311487289559017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2254581830645062177259029 105683523311487289559017)
                ·
                  rfl

theorem cell21_1389271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 6].length) (baseStart_1389271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389271 prefixEnd_1389271 := by exact prefixLift 1389271
  have htrace : WordTrace (prefixWord ++ tailWord_1389271) baseStart_1389271 baseEnd_1389271 := by
    simpa [prefixWord, tailWord_1389271, baseEnd_1389271] using wordTrace_append hprefix tailTrace_1389271
  have hstable : (prefixWord ++ tailWord_1389271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389271).length < 2 ^ (prefixWord ++ tailWord_1389271).sum := by decide
  have hdescent : baseEnd_1389271 < baseStart_1389271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389361 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 7]
def baseStart_1389361 : Nat := 118140960795 + 1389361 * 2 ^ 59
def prefixEnd_1389361 : Nat := 4983230072969 + 3 ^ 40 * 1389361 * 2
def baseEnd_1389361 : Nat := 317071109160641712176867

theorem tailTrace_1389361 : CollatzResearch.WordTrace tailWord_1389361 prefixEnd_1389361 317071109160641712176867 := by
  unfold tailWord_1389361
  simp only [CollatzResearch.WordTrace]
  refine ⟨50674158719589855812767937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33782772479726570541845291 50674158719589855812767937)
  ·
    refine ⟨38005619039692391859575953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50674158719589855812767937 38005619039692391859575953)
    ·
      refine ⟨28504214279769293894681965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38005619039692391859575953 28504214279769293894681965)
      ·
        refine ⟨10689080354913485210505737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28504214279769293894681965 10689080354913485210505737)
        ·
          refine ⟨8016810266185113907879303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10689080354913485210505737 8016810266185113907879303)
          ·
            refine ⟨12025215399277670861818955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8016810266185113907879303 12025215399277670861818955)
            ·
              refine ⟨18037823098916506292728433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12025215399277670861818955 18037823098916506292728433)
              ·
                refine ⟨13528367324187379719546325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18037823098916506292728433 13528367324187379719546325)
                ·
                  refine ⟨317071109160641712176867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13528367324187379719546325 317071109160641712176867)
                  ·
                    rfl

theorem cell21_1389361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_1389361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389361 prefixEnd_1389361 := by exact prefixLift 1389361
  have htrace : WordTrace (prefixWord ++ tailWord_1389361) baseStart_1389361 baseEnd_1389361 := by
    simpa [prefixWord, tailWord_1389361, baseEnd_1389361] using wordTrace_append hprefix tailTrace_1389361
  have hstable : (prefixWord ++ tailWord_1389361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389361).length < 2 ^ (prefixWord ++ tailWord_1389361).sum := by decide
  have hdescent : baseEnd_1389361 < baseStart_1389361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389364 : List Nat := [2, 5, 1, 1, 3, 1, 8]
def baseStart_1389364 : Nat := 118140960795 + 1389364 * 2 ^ 59
def prefixEnd_1389364 : Nat := 4983230072969 + 3 ^ 40 * 1389364 * 2
def baseEnd_1389364 : Nat := 35230199311279374847429

theorem tailTrace_1389364 : CollatzResearch.WordTrace tailWord_1389364 prefixEnd_1389364 35230199311279374847429 := by
  unfold tailWord_1389364
  simp only [CollatzResearch.WordTrace]
  refine ⟨25337134069289493662563573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33782845425719324883418097 25337134069289493662563573)
  ·
    refine ⟨2375356318995890030865335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25337134069289493662563573 2375356318995890030865335)
    ·
      refine ⟨3563034478493835046298003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2375356318995890030865335 3563034478493835046298003)
      ·
        refine ⟨5344551717740752569447005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3563034478493835046298003 5344551717740752569447005)
        ·
          refine ⟨2004206894152782213542627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5344551717740752569447005 2004206894152782213542627)
          ·
            refine ⟨3006310341229173320313941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004206894152782213542627 3006310341229173320313941)
            ·
              refine ⟨35230199311279374847429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3006310341229173320313941 35230199311279374847429)
              ·
                rfl

theorem cell21_1389364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 8].length) (baseStart_1389364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389364 prefixEnd_1389364 := by exact prefixLift 1389364
  have htrace : WordTrace (prefixWord ++ tailWord_1389364) baseStart_1389364 baseEnd_1389364 := by
    simpa [prefixWord, tailWord_1389364, baseEnd_1389364] using wordTrace_append hprefix tailTrace_1389364
  have hstable : (prefixWord ++ tailWord_1389364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389364).length < 2 ^ (prefixWord ++ tailWord_1389364).sum := by decide
  have hdescent : baseEnd_1389364 < baseStart_1389364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389392 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_1389392 : Nat := 118140960795 + 1389392 * 2 ^ 59
def prefixEnd_1389392 : Nat := 4983230072969 + 3 ^ 40 * 1389392 * 2
def baseEnd_1389392 : Nat := 317078183782992547160137

theorem tailTrace_1389392 : CollatzResearch.WordTrace tailWord_1389392 prefixEnd_1389392 317078183782992547160137 := by
  unfold tailWord_1389392
  simp only [CollatzResearch.WordTrace]
  refine ⟨25337644691238774053573215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33783526254985032071430953 25337644691238774053573215)
  ·
    refine ⟨38006467036858161080359823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25337644691238774053573215 38006467036858161080359823)
    ·
      refine ⟨57009700555287241620539735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38006467036858161080359823 57009700555287241620539735)
      ·
        refine ⟨85514550832930862430809603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57009700555287241620539735 85514550832930862430809603)
        ·
          refine ⟨128271826249396293646214405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85514550832930862430809603 128271826249396293646214405)
          ·
            refine ⟨24050967421761805058665201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128271826249396293646214405 24050967421761805058665201)
            ·
              refine ⟨18038225566321353793998901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24050967421761805058665201 18038225566321353793998901)
              ·
                refine ⟨1691083646842626918187397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18038225566321353793998901 1691083646842626918187397)
                ·
                  refine ⟨317078183782992547160137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1691083646842626918187397 317078183782992547160137)
                  ·
                    rfl

theorem cell21_1389392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_1389392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389392 prefixEnd_1389392 := by exact prefixLift 1389392
  have htrace : WordTrace (prefixWord ++ tailWord_1389392) baseStart_1389392 baseEnd_1389392 := by
    simpa [prefixWord, tailWord_1389392, baseEnd_1389392] using wordTrace_append hprefix tailTrace_1389392
  have hstable : (prefixWord ++ tailWord_1389392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389392).length < 2 ^ (prefixWord ++ tailWord_1389392).sum := by decide
  have hdescent : baseEnd_1389392 < baseStart_1389392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389412 : List Nat := [2, 3, 1, 1, 4, 3, 1, 3, 3]
def baseStart_1389412 : Nat := 118140960795 + 1389412 * 2 ^ 59
def prefixEnd_1389412 : Nat := 4983230072969 + 3 ^ 40 * 1389412 * 2
def baseEnd_1389412 : Nat := 317082748055476956826763

theorem tailTrace_1389412 : CollatzResearch.WordTrace tailWord_1389412 prefixEnd_1389412 317082748055476956826763 := by
  unfold tailWord_1389412
  simp only [CollatzResearch.WordTrace]
  refine ⟨25338009421202545761437245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33784012561603394348582993 25338009421202545761437245)
  ·
    refine ⟨9501753532950954660538967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25338009421202545761437245 9501753532950954660538967)
    ·
      refine ⟨14252630299426431990808451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9501753532950954660538967 14252630299426431990808451)
      ·
        refine ⟨21378945449139647986212677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14252630299426431990808451 21378945449139647986212677)
        ·
          refine ⟨4008552271713683997414877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21378945449139647986212677 4008552271713683997414877)
          ·
            refine ⟨1503207101892631499030579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4008552271713683997414877 1503207101892631499030579)
            ·
              refine ⟨2254810652838947248545869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503207101892631499030579 2254810652838947248545869)
              ·
                refine ⟨845553994814605218204701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2254810652838947248545869 845553994814605218204701)
                ·
                  refine ⟨317082748055476956826763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845553994814605218204701 317082748055476956826763)
                  ·
                    rfl

theorem cell21_1389412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_1389412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389412 prefixEnd_1389412 := by exact prefixLift 1389412
  have htrace : WordTrace (prefixWord ++ tailWord_1389412) baseStart_1389412 baseEnd_1389412 := by
    simpa [prefixWord, tailWord_1389412, baseEnd_1389412] using wordTrace_append hprefix tailTrace_1389412
  have hstable : (prefixWord ++ tailWord_1389412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389412).length < 2 ^ (prefixWord ++ tailWord_1389412).sum := by decide
  have hdescent : baseEnd_1389412 < baseStart_1389412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389561 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 4]
def baseStart_1389561 : Nat := 118140960795 + 1389561 * 2 ^ 59
def prefixEnd_1389561 : Nat := 4983230072969 + 3 ^ 40 * 1389561 * 2
def baseEnd_1389561 : Nat := 317116751885485808843125

theorem tailTrace_1389561 : CollatzResearch.WordTrace tailWord_1389561 prefixEnd_1389561 317116751885485808843125 := by
  unfold tailWord_1389561
  simp only [CollatzResearch.WordTrace]
  refine ⟨50681453318865289970048537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33787635545910193313365691 50681453318865289970048537)
  ·
    refine ⟨38011089989148967477536403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50681453318865289970048537 38011089989148967477536403)
    ·
      refine ⟨57016634983723451216304605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38011089989148967477536403 57016634983723451216304605)
      ·
        refine ⟨21381238118896294206114227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57016634983723451216304605 21381238118896294206114227)
        ·
          refine ⟨32071857178344441309171341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21381238118896294206114227 32071857178344441309171341)
          ·
            refine ⟨12026946441879165490939253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32071857178344441309171341 12026946441879165490939253)
            ·
              refine ⟨1127526228926171764775555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12026946441879165490939253 1127526228926171764775555)
              ·
                refine ⟨1691289343389257647163333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127526228926171764775555 1691289343389257647163333)
                ·
                  refine ⟨317116751885485808843125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1691289343389257647163333 317116751885485808843125)
                  ·
                    rfl

theorem cell21_1389561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_1389561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389561 prefixEnd_1389561 := by exact prefixLift 1389561
  have htrace : WordTrace (prefixWord ++ tailWord_1389561) baseStart_1389561 baseEnd_1389561 := by
    simpa [prefixWord, tailWord_1389561, baseEnd_1389561] using wordTrace_append hprefix tailTrace_1389561
  have hstable : (prefixWord ++ tailWord_1389561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389561).length < 2 ^ (prefixWord ++ tailWord_1389561).sum := by decide
  have hdescent : baseEnd_1389561 < baseStart_1389561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389685 : List Nat := [1, 3, 4, 3, 1, 1, 3, 5]
def baseStart_1389685 : Nat := 118140960795 + 1389685 * 2 ^ 59
def prefixEnd_1389685 : Nat := 4983230072969 + 3 ^ 40 * 1389685 * 2
def baseEnd_1389685 : Nat := 105715016791629716258735

theorem tailTrace_1389685 : CollatzResearch.WordTrace tailWord_1389685 prefixEnd_1389685 105715016791629716258735 := by
  unfold tailWord_1389685
  simp only [CollatzResearch.WordTrace]
  refine ⟨50685975970416059147562509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33790650646944039431708339 50685975970416059147562509)
  ·
    refine ⟨19007240988906022180335941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50685975970416059147562509 19007240988906022180335941)
    ·
      refine ⟨3563857685419879158812989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19007240988906022180335941 3563857685419879158812989)
      ·
        refine ⟨1336446632032454684554871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3563857685419879158812989 1336446632032454684554871)
        ·
          refine ⟨2004669948048682026832307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336446632032454684554871 2004669948048682026832307)
          ·
            refine ⟨3007004922073023040248461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004669948048682026832307 3007004922073023040248461)
            ·
              refine ⟨1127626845777383640093173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3007004922073023040248461 1127626845777383640093173)
              ·
                refine ⟨105715016791629716258735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1127626845777383640093173 105715016791629716258735)
                ·
                  rfl

theorem cell21_1389685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 5].length) (baseStart_1389685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389685 prefixEnd_1389685 := by exact prefixLift 1389685
  have htrace : WordTrace (prefixWord ++ tailWord_1389685) baseStart_1389685 baseEnd_1389685 := by
    simpa [prefixWord, tailWord_1389685, baseEnd_1389685] using wordTrace_append hprefix tailTrace_1389685
  have hstable : (prefixWord ++ tailWord_1389685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389685).length < 2 ^ (prefixWord ++ tailWord_1389685).sum := by decide
  have hdescent : baseEnd_1389685 < baseStart_1389685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389750 : List Nat := [5, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1389750 : Nat := 118140960795 + 1389750 * 2 ^ 59
def prefixEnd_1389750 : Nat := 4983230072969 + 3 ^ 40 * 1389750 * 2
def baseEnd_1389750 : Nat := 317159884260463480192739

theorem tailTrace_1389750 : CollatzResearch.WordTrace tailWord_1389750 prefixEnd_1389750 317159884260463480192739 := by
  unfold tailWord_1389750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168021669698785953042419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33792231143453716832452469 3168021669698785953042419)
  ·
    refine ⟨4752032504548178929563629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3168021669698785953042419 4752032504548178929563629)
    ·
      refine ⟨1782012189205567098586361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4752032504548178929563629 1782012189205567098586361)
      ·
        refine ⟨1336509141904175323939771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1782012189205567098586361 1336509141904175323939771)
        ·
          refine ⟨2004763712856262985909657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336509141904175323939771 2004763712856262985909657)
          ·
            refine ⟨1503572784642197239432243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2004763712856262985909657 1503572784642197239432243)
            ·
              refine ⟨2255359176963295859148365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503572784642197239432243 2255359176963295859148365)
              ·
                refine ⟨845759691361235947180637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2255359176963295859148365 845759691361235947180637)
                ·
                  refine ⟨317159884260463480192739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845759691361235947180637 317159884260463480192739)
                  ·
                    rfl

theorem cell21_1389750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1389750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389750 prefixEnd_1389750 := by exact prefixLift 1389750
  have htrace : WordTrace (prefixWord ++ tailWord_1389750) baseStart_1389750 baseEnd_1389750 := by
    simpa [prefixWord, tailWord_1389750, baseEnd_1389750] using wordTrace_append hprefix tailTrace_1389750
  have hstable : (prefixWord ++ tailWord_1389750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389750).length < 2 ^ (prefixWord ++ tailWord_1389750).sum := by decide
  have hdescent : baseEnd_1389750 < baseStart_1389750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389826 : List Nat := [3, 4, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1389826 : Nat := 118140960795 + 1389826 * 2 ^ 59
def prefixEnd_1389826 : Nat := 4983230072969 + 3 ^ 40 * 1389826 * 2
def baseEnd_1389826 : Nat := 317177228495904236925917

theorem tailTrace_1389826 : CollatzResearch.WordTrace tailWord_1389826 prefixEnd_1389826 317177228495904236925917 := by
  unfold tailWord_1389826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12672779665726310057111333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33794079108603493485630221 12672779665726310057111333)
  ·
    refine ⟨2376146187323683135708375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12672779665726310057111333 2376146187323683135708375)
    ·
      refine ⟨3564219280985524703562563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2376146187323683135708375 3564219280985524703562563)
      ·
        refine ⟨5346328921478287055343845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3564219280985524703562563 5346328921478287055343845)
        ·
          refine ⟨1002436672777178822876971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5346328921478287055343845 1002436672777178822876971)
          ·
            refine ⟨1503655009165768234315457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002436672777178822876971 1503655009165768234315457)
            ·
              refine ⟨1127741256874326175736593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1503655009165768234315457 1127741256874326175736593)
              ·
                refine ⟨845805942655744631802445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127741256874326175736593 845805942655744631802445)
                ·
                  refine ⟨317177228495904236925917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845805942655744631802445 317177228495904236925917)
                  ·
                    rfl

theorem cell21_1389826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1389826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389826 prefixEnd_1389826 := by exact prefixLift 1389826
  have htrace : WordTrace (prefixWord ++ tailWord_1389826) baseStart_1389826 baseEnd_1389826 := by
    simpa [prefixWord, tailWord_1389826, baseEnd_1389826] using wordTrace_append hprefix tailTrace_1389826
  have hstable : (prefixWord ++ tailWord_1389826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389826).length < 2 ^ (prefixWord ++ tailWord_1389826).sum := by decide
  have hdescent : baseEnd_1389826 < baseStart_1389826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389848 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_1389848 : Nat := 118140960795 + 1389848 * 2 ^ 59
def prefixEnd_1389848 : Nat := 4983230072969 + 3 ^ 40 * 1389848 * 2
def baseEnd_1389848 : Nat := 317182249195637087559205

theorem tailTrace_1389848 : CollatzResearch.WordTrace tailWord_1389848 prefixEnd_1389848 317182249195637087559205 := by
  unfold tailWord_1389848
  simp only [CollatzResearch.WordTrace]
  refine ⟨25345960534412768992873099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33794614045883691990497465 25345960534412768992873099)
  ·
    refine ⟨38018940801619153489309649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25345960534412768992873099 38018940801619153489309649)
    ·
      refine ⟨28514205601214365116982237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38018940801619153489309649 28514205601214365116982237)
      ·
        refine ⟨10692827100455386918868339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28514205601214365116982237 10692827100455386918868339)
        ·
          refine ⟨16039240650683080378302509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10692827100455386918868339 16039240650683080378302509)
          ·
            refine ⟨6014715244006155141863441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16039240650683080378302509 6014715244006155141863441)
            ·
              refine ⟨4511036433004616356397581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6014715244006155141863441 4511036433004616356397581)
              ·
                refine ⟨1691638662376731133649093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4511036433004616356397581 1691638662376731133649093)
                ·
                  refine ⟨317182249195637087559205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1691638662376731133649093 317182249195637087559205)
                  ·
                    rfl

theorem cell21_1389848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_1389848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1389848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1389848 prefixEnd_1389848 := by exact prefixLift 1389848
  have htrace : WordTrace (prefixWord ++ tailWord_1389848) baseStart_1389848 baseEnd_1389848 := by
    simpa [prefixWord, tailWord_1389848, baseEnd_1389848] using wordTrace_append hprefix tailTrace_1389848
  have hstable : (prefixWord ++ tailWord_1389848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389848).length < 2 ^ (prefixWord ++ tailWord_1389848).sum := by decide
  have hdescent : baseEnd_1389848 < baseStart_1389848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390059 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 4]
def baseStart_1390059 : Nat := 118140960795 + 1390059 * 2 ^ 59
def prefixEnd_1390059 : Nat := 4983230072969 + 3 ^ 40 * 1390059 * 2
def baseEnd_1390059 : Nat := 317230402270347609542107

theorem tailTrace_1390059 : CollatzResearch.WordTrace tailWord_1390059 prefixEnd_1390059 317230402270347609542107 := by
  unfold tailWord_1390059
  simp only [CollatzResearch.WordTrace]
  refine ⟨50699616871061121021677231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33799744580707414014451487 50699616871061121021677231)
  ·
    refine ⟨76049425306591681532515847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50699616871061121021677231 76049425306591681532515847)
    ·
      refine ⟨114074137959887522298773771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76049425306591681532515847 114074137959887522298773771)
      ·
        refine ⟨171111206939831283448160657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114074137959887522298773771 171111206939831283448160657)
        ·
          refine ⟨128333405204873462586120493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171111206939831283448160657 128333405204873462586120493)
          ·
            refine ⟨48125026951827548469795185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128333405204873462586120493 48125026951827548469795185)
            ·
              refine ⟨36093770213870661352346389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48125026951827548469795185 36093770213870661352346389)
              ·
                refine ⟨1691895478775187250891237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36093770213870661352346389 1691895478775187250891237)
                ·
                  refine ⟨317230402270347609542107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1691895478775187250891237 317230402270347609542107)
                  ·
                    rfl

theorem cell21_1390059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 4].length) (baseStart_1390059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390059 prefixEnd_1390059 := by exact prefixLift 1390059
  have htrace : WordTrace (prefixWord ++ tailWord_1390059) baseStart_1390059 baseEnd_1390059 := by
    simpa [prefixWord, tailWord_1390059, baseEnd_1390059] using wordTrace_append hprefix tailTrace_1390059
  have hstable : (prefixWord ++ tailWord_1390059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390059).length < 2 ^ (prefixWord ++ tailWord_1390059).sum := by decide
  have hdescent : baseEnd_1390059 < baseStart_1390059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390062 : List Nat := [4, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_1390062 : Nat := 118140960795 + 1390062 * 2 ^ 59
def prefixEnd_1390062 : Nat := 4983230072969 + 3 ^ 40 * 1390062 * 2
def baseEnd_1390062 : Nat := 317231086911220270992101

theorem tailTrace_1390062 : CollatzResearch.WordTrace tailWord_1390062 prefixEnd_1390062 317231086911220270992101 := by
  unfold tailWord_1390062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337465786256281566754555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33799817526700168356024293 6337465786256281566754555)
  ·
    refine ⟨9506198679384422350131833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6337465786256281566754555 9506198679384422350131833)
    ·
      refine ⟨7129649009538316762598875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9506198679384422350131833 7129649009538316762598875)
      ·
        refine ⟨10694473514307475143898313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7129649009538316762598875 10694473514307475143898313)
        ·
          refine ⟨8020855135730606357923735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10694473514307475143898313 8020855135730606357923735)
          ·
            refine ⟨12031282703595909536885603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8020855135730606357923735 12031282703595909536885603)
            ·
              refine ⟨18046924055393864305328405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12031282703595909536885603 18046924055393864305328405)
              ·
                refine ⟨845949565096587389312269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18046924055393864305328405 845949565096587389312269)
                ·
                  refine ⟨317231086911220270992101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845949565096587389312269 317231086911220270992101)
                  ·
                    rfl

theorem cell21_1390062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_1390062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390062 prefixEnd_1390062 := by exact prefixLift 1390062
  have htrace : WordTrace (prefixWord ++ tailWord_1390062) baseStart_1390062 baseEnd_1390062 := by
    simpa [prefixWord, tailWord_1390062, baseEnd_1390062] using wordTrace_append hprefix tailTrace_1390062
  have hstable : (prefixWord ++ tailWord_1390062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390062).length < 2 ^ (prefixWord ++ tailWord_1390062).sum := by decide
  have hdescent : baseEnd_1390062 < baseStart_1390062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390073 : List Nat := [1, 2, 1, 3, 1, 2, 1, 10]
def baseStart_1390073 : Nat := 118140960795 + 1390073 * 2 ^ 59
def prefixEnd_1390073 : Nat := 4983230072969 + 3 ^ 40 * 1390073 * 2
def baseEnd_1390073 : Nat := 105744532420362232102915

theorem tailTrace_1390073 : CollatzResearch.WordTrace tailWord_1390073 prefixEnd_1390073 105744532420362232102915 := by
  unfold tailWord_1390073
  simp only [CollatzResearch.WordTrace]
  refine ⟨50700127493010401412686873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33800084995340267608457915 50700127493010401412686873)
  ·
    refine ⟨38025095619757801059515155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50700127493010401412686873 38025095619757801059515155)
    ·
      refine ⟨57037643429636701589272733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38025095619757801059515155 57037643429636701589272733)
      ·
        refine ⟨21389116286113763095977275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57037643429636701589272733 21389116286113763095977275)
        ·
          refine ⟨32083674429170644643965913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21389116286113763095977275 32083674429170644643965913)
          ·
            refine ⟨24062755821877983482974435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32083674429170644643965913 24062755821877983482974435)
            ·
              refine ⟨36094133732816975224461653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24062755821877983482974435 36094133732816975224461653)
              ·
                refine ⟨105744532420362232102915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36094133732816975224461653 105744532420362232102915)
                ·
                  rfl

theorem cell21_1390073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 10].length) (baseStart_1390073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390073 prefixEnd_1390073 := by exact prefixLift 1390073
  have htrace : WordTrace (prefixWord ++ tailWord_1390073) baseStart_1390073 baseEnd_1390073 := by
    simpa [prefixWord, tailWord_1390073, baseEnd_1390073] using wordTrace_append hprefix tailTrace_1390073
  have hstable : (prefixWord ++ tailWord_1390073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390073).length < 2 ^ (prefixWord ++ tailWord_1390073).sum := by decide
  have hdescent : baseEnd_1390073 < baseStart_1390073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390090 : List Nat := [3, 1, 2, 2, 2, 3, 1, 7]
def baseStart_1390090 : Nat := 118140960795 + 1390090 * 2 ^ 59
def prefixEnd_1390090 : Nat := 4983230072969 + 3 ^ 40 * 1390090 * 2
def baseEnd_1390090 : Nat := 105745825630899481508459

theorem tailTrace_1390090 : CollatzResearch.WordTrace tailWord_1390090 prefixEnd_1390090 105745825630899481508459 := by
  unfold tailWord_1390090
  simp only [CollatzResearch.WordTrace]
  refine ⟨12675186883487203329013931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33800498355965875544037149 12675186883487203329013931)
  ·
    refine ⟨19012780325230804993520897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12675186883487203329013931 19012780325230804993520897)
    ·
      refine ⟨14259585243923103745140673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19012780325230804993520897 14259585243923103745140673)
      ·
        refine ⟨10694688932942327808855505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14259585243923103745140673 10694688932942327808855505)
        ·
          refine ⟨8021016699706745856641629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10694688932942327808855505 8021016699706745856641629)
          ·
            refine ⟨3007881262390029696240611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8021016699706745856641629 3007881262390029696240611)
            ·
              refine ⟨4511821893585044544360917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007881262390029696240611 4511821893585044544360917)
              ·
                refine ⟨105745825630899481508459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4511821893585044544360917 105745825630899481508459)
                ·
                  rfl

theorem cell21_1390090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_1390090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390090 prefixEnd_1390090 := by exact prefixLift 1390090
  have htrace : WordTrace (prefixWord ++ tailWord_1390090) baseStart_1390090 baseEnd_1390090 := by
    simpa [prefixWord, tailWord_1390090, baseEnd_1390090] using wordTrace_append hprefix tailTrace_1390090
  have hstable : (prefixWord ++ tailWord_1390090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390090).length < 2 ^ (prefixWord ++ tailWord_1390090).sum := by decide
  have hdescent : baseEnd_1390090 < baseStart_1390090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390149 : List Nat := [1, 3, 1, 1, 1, 4, 1, 9]
def baseStart_1390149 : Nat := 118140960795 + 1390149 * 2 ^ 59
def prefixEnd_1390149 : Nat := 4983230072969 + 3 ^ 40 * 1390149 * 2
def baseEnd_1390149 : Nat := 105750313832175817680641

theorem tailTrace_1390149 : CollatzResearch.WordTrace tailWord_1390149 prefixEnd_1390149 105750313832175817680641 := by
  unfold tailWord_1390149
  simp only [CollatzResearch.WordTrace]
  refine ⟨50702899440735066392453501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33801932960490044261635667 50702899440735066392453501)
  ·
    refine ⟨19013587290275649897170063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50702899440735066392453501 19013587290275649897170063)
    ·
      refine ⟨28520380935413474845755095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19013587290275649897170063 28520380935413474845755095)
      ·
        refine ⟨42780571403120212268632643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28520380935413474845755095 42780571403120212268632643)
        ·
          refine ⟨64170857104680318402948965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42780571403120212268632643 64170857104680318402948965)
          ·
            refine ⟨12032035707127559700552931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64170857104680318402948965 12032035707127559700552931)
            ·
              refine ⟨18048053560691339550829397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12032035707127559700552931 18048053560691339550829397)
              ·
                refine ⟨105750313832175817680641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18048053560691339550829397 105750313832175817680641)
                ·
                  rfl

theorem cell21_1390149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 9].length) (baseStart_1390149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390149 prefixEnd_1390149 := by exact prefixLift 1390149
  have htrace : WordTrace (prefixWord ++ tailWord_1390149) baseStart_1390149 baseEnd_1390149 := by
    simpa [prefixWord, tailWord_1390149, baseEnd_1390149] using wordTrace_append hprefix tailTrace_1390149
  have hstable : (prefixWord ++ tailWord_1390149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390149).length < 2 ^ (prefixWord ++ tailWord_1390149).sum := by decide
  have hdescent : baseEnd_1390149 < baseStart_1390149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390172 : List Nat := [2, 2, 4, 1, 2, 3, 2, 2, 3]
def baseStart_1390172 : Nat := 118140960795 + 1390172 * 2 ^ 59
def prefixEnd_1390172 : Nat := 4983230072969 + 3 ^ 40 * 1390172 * 2
def baseEnd_1390172 : Nat := 317256190409884524158543

theorem tailTrace_1390172 : CollatzResearch.WordTrace tailWord_1390172 prefixEnd_1390172 317256190409884524158543 := by
  unfold tailWord_1390172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25351869159825870660270385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33802492213101160880360513 25351869159825870660270385)
  ·
    refine ⟨19013901869869402995202789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25351869159825870660270385 19013901869869402995202789)
    ·
      refine ⟨3565106600600513061600523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19013901869869402995202789 3565106600600513061600523)
      ·
        refine ⟨5347659900900769592400785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3565106600600513061600523 5347659900900769592400785)
        ·
          refine ⟨4010744925675577194300589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5347659900900769592400785 4010744925675577194300589)
          ·
            refine ⟨1504029347128341447862721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4010744925675577194300589 1504029347128341447862721)
            ·
              refine ⟨1128022010346256085897041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504029347128341447862721 1128022010346256085897041)
              ·
                refine ⟨846016507759692064422781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128022010346256085897041 846016507759692064422781)
                ·
                  refine ⟨317256190409884524158543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846016507759692064422781 317256190409884524158543)
                  ·
                    rfl

theorem cell21_1390172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_1390172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390172 prefixEnd_1390172 := by exact prefixLift 1390172
  have htrace : WordTrace (prefixWord ++ tailWord_1390172) baseStart_1390172 baseEnd_1390172 := by
    simpa [prefixWord, tailWord_1390172, baseEnd_1390172] using wordTrace_append hprefix tailTrace_1390172
  have hstable : (prefixWord ++ tailWord_1390172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390172).length < 2 ^ (prefixWord ++ tailWord_1390172).sum := by decide
  have hdescent : baseEnd_1390172 < baseStart_1390172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390197 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 7]
def baseStart_1390197 : Nat := 118140960795 + 1390197 * 2 ^ 59
def prefixEnd_1390197 : Nat := 4983230072969 + 3 ^ 40 * 1390197 * 2
def baseEnd_1390197 : Nat := 317261895750490036241825

theorem tailTrace_1390197 : CollatzResearch.WordTrace tailWord_1390197 prefixEnd_1390197 317261895750490036241825 := by
  unfold tailWord_1390197
  simp only [CollatzResearch.WordTrace]
  refine ⟨50704650144561170590200845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33803100096374113726800563 50704650144561170590200845)
  ·
    refine ⟨19014243804210438971325317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50704650144561170590200845 19014243804210438971325317)
    ·
      refine ⟨3565170713289457307123497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19014243804210438971325317 3565170713289457307123497)
      ·
        refine ⟨2673878034967092980342623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3565170713289457307123497 2673878034967092980342623)
        ·
          refine ⟨4010817052450639470513935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673878034967092980342623 4010817052450639470513935)
          ·
            refine ⟨6016225578675959205770903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4010817052450639470513935 6016225578675959205770903)
            ·
              refine ⟨9024338368013938808656355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6016225578675959205770903 9024338368013938808656355)
              ·
                refine ⟨13536507552020908212984533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9024338368013938808656355 13536507552020908212984533)
                ·
                  refine ⟨317261895750490036241825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13536507552020908212984533 317261895750490036241825)
                  ·
                    rfl

theorem cell21_1390197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_1390197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390197 prefixEnd_1390197 := by exact prefixLift 1390197
  have htrace : WordTrace (prefixWord ++ tailWord_1390197) baseStart_1390197 baseEnd_1390197 := by
    simpa [prefixWord, tailWord_1390197, baseEnd_1390197] using wordTrace_append hprefix tailTrace_1390197
  have hstable : (prefixWord ++ tailWord_1390197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390197).length < 2 ^ (prefixWord ++ tailWord_1390197).sum := by decide
  have hdescent : baseEnd_1390197 < baseStart_1390197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390256 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_1390256 : Nat := 118140960795 + 1390256 * 2 ^ 59
def prefixEnd_1390256 : Nat := 4983230072969 + 3 ^ 40 * 1390256 * 2
def baseEnd_1390256 : Nat := 317275360354319044758371

theorem tailTrace_1390256 : CollatzResearch.WordTrace tailWord_1390256 prefixEnd_1390256 317275360354319044758371 := by
  unfold tailWord_1390256
  simp only [CollatzResearch.WordTrace]
  refine ⟨25353401025673711833299311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33804534700898282444399081 25353401025673711833299311)
  ·
    refine ⟨38030101538510567749948967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25353401025673711833299311 38030101538510567749948967)
    ·
      refine ⟨57045152307765851624923451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38030101538510567749948967 57045152307765851624923451)
      ·
        refine ⟨85567728461648777437385177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57045152307765851624923451 85567728461648777437385177)
        ·
          refine ⟨64175796346236583078038883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85567728461648777437385177 64175796346236583078038883)
          ·
            refine ⟨96263694519354874617058325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64175796346236583078038883 96263694519354874617058325)
            ·
              refine ⟨4512360680594759747674609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96263694519354874617058325 4512360680594759747674609)
              ·
                refine ⟨3384270510446069810755957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4512360680594759747674609 3384270510446069810755957)
                ·
                  refine ⟨317275360354319044758371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3384270510446069810755957 317275360354319044758371)
                  ·
                    rfl

theorem cell21_1390256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_1390256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390256 prefixEnd_1390256 := by exact prefixLift 1390256
  have htrace : WordTrace (prefixWord ++ tailWord_1390256) baseStart_1390256 baseEnd_1390256 := by
    simpa [prefixWord, tailWord_1390256, baseEnd_1390256] using wordTrace_append hprefix tailTrace_1390256
  have hstable : (prefixWord ++ tailWord_1390256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390256).length < 2 ^ (prefixWord ++ tailWord_1390256).sum := by decide
  have hdescent : baseEnd_1390256 < baseStart_1390256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390290 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_1390290 : Nat := 118140960795 + 1390290 * 2 ^ 59
def prefixEnd_1390290 : Nat := 4983230072969 + 3 ^ 40 * 1390290 * 2
def baseEnd_1390290 : Nat := 317283119617542541191635

theorem tailTrace_1390290 : CollatzResearch.WordTrace tailWord_1390290 prefixEnd_1390290 317283119617542541191635 := by
  unfold tailWord_1390290
  simp only [CollatzResearch.WordTrace]
  refine ⟨12677010533306061868334081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33805361422149498315557549 12677010533306061868334081)
  ·
    refine ⟨9507757899979546401250561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12677010533306061868334081 9507757899979546401250561)
    ·
      refine ⟨7130818424984659800937921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9507757899979546401250561 7130818424984659800937921)
      ·
        refine ⟨5348113818738494850703441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7130818424984659800937921 5348113818738494850703441)
        ·
          refine ⟨4011085364053871138027581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5348113818738494850703441 4011085364053871138027581)
          ·
            refine ⟨1504157011520201676760343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4011085364053871138027581 1504157011520201676760343)
            ·
              refine ⟨2256235517280302515140515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504157011520201676760343 2256235517280302515140515)
              ·
                refine ⟨3384353275920453772710773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2256235517280302515140515 3384353275920453772710773)
                ·
                  refine ⟨317283119617542541191635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3384353275920453772710773 317283119617542541191635)
                  ·
                    rfl

theorem cell21_1390290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_1390290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390290 prefixEnd_1390290 := by exact prefixLift 1390290
  have htrace : WordTrace (prefixWord ++ tailWord_1390290) baseStart_1390290 baseEnd_1390290 := by
    simpa [prefixWord, tailWord_1390290, baseEnd_1390290] using wordTrace_append hprefix tailTrace_1390290
  have hstable : (prefixWord ++ tailWord_1390290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390290).length < 2 ^ (prefixWord ++ tailWord_1390290).sum := by decide
  have hdescent : baseEnd_1390290 < baseStart_1390290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390304 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 4]
def baseStart_1390304 : Nat := 118140960795 + 1390304 * 2 ^ 59
def prefixEnd_1390304 : Nat := 4983230072969 + 3 ^ 40 * 1390304 * 2
def baseEnd_1390304 : Nat := 317286314608281627958273

theorem tailTrace_1390304 : CollatzResearch.WordTrace tailWord_1390304 prefixEnd_1390304 317286314608281627958273 := by
  unfold tailWord_1390304
  simp only [CollatzResearch.WordTrace]
  refine ⟨25354276377586763932172983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33805701836782351909563977 25354276377586763932172983)
  ·
    refine ⟨38031414566380145898259475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25354276377586763932172983 38031414566380145898259475)
    ·
      refine ⟨57047121849570218847389213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38031414566380145898259475 57047121849570218847389213)
      ·
        refine ⟨21392670693588832067770955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57047121849570218847389213 21392670693588832067770955)
        ·
          refine ⟨32089006040383248101656433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21392670693588832067770955 32089006040383248101656433)
          ·
            refine ⟨24066754530287436076242325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32089006040383248101656433 24066754530287436076242325)
            ·
              refine ⟨1128129118607223566073859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24066754530287436076242325 1128129118607223566073859)
              ·
                refine ⟨1692193677910835349110789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128129118607223566073859 1692193677910835349110789)
                ·
                  refine ⟨317286314608281627958273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1692193677910835349110789 317286314608281627958273)
                  ·
                    rfl

theorem cell21_1390304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_1390304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390304 prefixEnd_1390304 := by exact prefixLift 1390304
  have htrace : WordTrace (prefixWord ++ tailWord_1390304) baseStart_1390304 baseEnd_1390304 := by
    simpa [prefixWord, tailWord_1390304, baseEnd_1390304] using wordTrace_append hprefix tailTrace_1390304
  have hstable : (prefixWord ++ tailWord_1390304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390304).length < 2 ^ (prefixWord ++ tailWord_1390304).sum := by decide
  have hdescent : baseEnd_1390304 < baseStart_1390304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390397 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 4]
def baseStart_1390397 : Nat := 118140960795 + 1390397 * 2 ^ 59
def prefixEnd_1390397 : Nat := 4983230072969 + 3 ^ 40 * 1390397 * 2
def baseEnd_1390397 : Nat := 317307538475334132908083

theorem tailTrace_1390397 : CollatzResearch.WordTrace tailWord_1390397 prefixEnd_1390397 317307538475334132908083 := by
  unfold tailWord_1390397
  simp only [CollatzResearch.WordTrace]
  refine ⟨50711944743836604747481445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33807963162557736498320963 50711944743836604747481445)
  ·
    refine ⟨9508489639469363390152771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50711944743836604747481445 9508489639469363390152771)
    ·
      refine ⟨14262734459204045085229157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9508489639469363390152771 14262734459204045085229157)
      ·
        refine ⟨2674262711100758453480467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14262734459204045085229157 2674262711100758453480467)
        ·
          refine ⟨4011394066651137680220701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2674262711100758453480467 4011394066651137680220701)
          ·
            refine ⟨1504272774994176630082763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4011394066651137680220701 1504272774994176630082763)
            ·
              refine ⟨2256409162491264945124145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504272774994176630082763 2256409162491264945124145)
              ·
                refine ⟨1692306871868448708843109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2256409162491264945124145 1692306871868448708843109)
                ·
                  refine ⟨317307538475334132908083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1692306871868448708843109 317307538475334132908083)
                  ·
                    rfl

theorem cell21_1390397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_1390397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390397 prefixEnd_1390397 := by exact prefixLift 1390397
  have htrace : WordTrace (prefixWord ++ tailWord_1390397) baseStart_1390397 baseEnd_1390397 := by
    simpa [prefixWord, tailWord_1390397, baseEnd_1390397] using wordTrace_append hprefix tailTrace_1390397
  have hstable : (prefixWord ++ tailWord_1390397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390397).length < 2 ^ (prefixWord ++ tailWord_1390397).sum := by decide
  have hdescent : baseEnd_1390397 < baseStart_1390397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390408 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_1390408 : Nat := 118140960795 + 1390408 * 2 ^ 59
def prefixEnd_1390408 : Nat := 4983230072969 + 3 ^ 40 * 1390408 * 2
def baseEnd_1390408 : Nat := 317310048825200558224727

theorem tailTrace_1390408 : CollatzResearch.WordTrace tailWord_1390408 prefixEnd_1390408 317310048825200558224727 := by
  unfold tailWord_1390408
  simp only [CollatzResearch.WordTrace]
  refine ⟨25356172973398376813065939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33808230631197835750754585 25356172973398376813065939)
  ·
    refine ⟨38034259460097565219598909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25356172973398376813065939 38034259460097565219598909)
    ·
      refine ⟨14262847297536586957349591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38034259460097565219598909 14262847297536586957349591)
      ·
        refine ⟨21394270946304880436024387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14262847297536586957349591 21394270946304880436024387)
        ·
          refine ⟨32091406419457320654036581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21394270946304880436024387 32091406419457320654036581)
          ·
            refine ⟨6017138703648247622631859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32091406419457320654036581 6017138703648247622631859)
            ·
              refine ⟨9025708055472371433947789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017138703648247622631859 9025708055472371433947789)
              ·
                refine ⟨3384640520802139287730421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9025708055472371433947789 3384640520802139287730421)
                ·
                  refine ⟨317310048825200558224727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3384640520802139287730421 317310048825200558224727)
                  ·
                    rfl

theorem cell21_1390408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_1390408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390408 prefixEnd_1390408 := by exact prefixLift 1390408
  have htrace : WordTrace (prefixWord ++ tailWord_1390408) baseStart_1390408 baseEnd_1390408 := by
    simpa [prefixWord, tailWord_1390408, baseEnd_1390408] using wordTrace_append hprefix tailTrace_1390408
  have hstable : (prefixWord ++ tailWord_1390408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390408).length < 2 ^ (prefixWord ++ tailWord_1390408).sum := by decide
  have hdescent : baseEnd_1390408 < baseStart_1390408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390428 : List Nat := [2, 2, 4, 2, 2, 2, 2, 5]
def baseStart_1390428 : Nat := 118140960795 + 1390428 * 2 ^ 59
def prefixEnd_1390428 : Nat := 4983230072969 + 3 ^ 40 * 1390428 * 2
def baseEnd_1390428 : Nat := 105771537699228322630451

theorem tailTrace_1390428 : CollatzResearch.WordTrace tailWord_1390428 prefixEnd_1390428 105771537699228322630451 := by
  unfold tailWord_1390428
  simp only [CollatzResearch.WordTrace]
  refine ⟨25356537703362148520929969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33808716937816198027906625 25356537703362148520929969)
  ·
    refine ⟨19017403277521611390697477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25356537703362148520929969 19017403277521611390697477)
    ·
      refine ⟨3565763114535302135755777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19017403277521611390697477 3565763114535302135755777)
      ·
        refine ⟨2674322335901476601816833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3565763114535302135755777 2674322335901476601816833)
        ·
          refine ⟨2005741751926107451362625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2674322335901476601816833 2005741751926107451362625)
          ·
            refine ⟨1504306313944580588521969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005741751926107451362625 1504306313944580588521969)
            ·
              refine ⟨1128229735458435441391477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504306313944580588521969 1128229735458435441391477)
              ·
                refine ⟨105771537699228322630451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1128229735458435441391477 105771537699228322630451)
                ·
                  rfl

theorem cell21_1390428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_1390428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390428 prefixEnd_1390428 := by exact prefixLift 1390428
  have htrace : WordTrace (prefixWord ++ tailWord_1390428) baseStart_1390428 baseEnd_1390428 := by
    simpa [prefixWord, tailWord_1390428, baseEnd_1390428] using wordTrace_append hprefix tailTrace_1390428
  have hstable : (prefixWord ++ tailWord_1390428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390428).length < 2 ^ (prefixWord ++ tailWord_1390428).sum := by decide
  have hdescent : baseEnd_1390428 < baseStart_1390428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390510 : List Nat := [4, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_1390510 : Nat := 118140960795 + 1390510 * 2 ^ 59
def prefixEnd_1390510 : Nat := 4983230072969 + 3 ^ 40 * 1390510 * 2
def baseEnd_1390510 : Nat := 317333326614871047524519

theorem tailTrace_1390510 : CollatzResearch.WordTrace tailWord_1390510 prefixEnd_1390510 317333326614871047524519 := by
  unfold tailWord_1390510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6339508274053403130793123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33810710794951483364229989 6339508274053403130793123)
  ·
    refine ⟨9509262411080104696189685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6339508274053403130793123 9509262411080104696189685)
    ·
      refine ⟨891493351038759815267783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9509262411080104696189685 891493351038759815267783)
      ·
        refine ⟨1337240026558139722901675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891493351038759815267783 1337240026558139722901675)
        ·
          refine ⟨2005860039837209584352513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337240026558139722901675 2005860039837209584352513)
          ·
            refine ⟨1504395029877907188264385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005860039837209584352513 1504395029877907188264385)
            ·
              refine ⟨1128296272408430391198289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504395029877907188264385 1128296272408430391198289)
              ·
                refine ⟨846222204306322793398717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128296272408430391198289 846222204306322793398717)
                ·
                  refine ⟨317333326614871047524519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846222204306322793398717 317333326614871047524519)
                  ·
                    rfl

theorem cell21_1390510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_1390510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390510 prefixEnd_1390510 := by exact prefixLift 1390510
  have htrace : WordTrace (prefixWord ++ tailWord_1390510) baseStart_1390510 baseEnd_1390510 := by
    simpa [prefixWord, tailWord_1390510, baseEnd_1390510] using wordTrace_append hprefix tailTrace_1390510
  have hstable : (prefixWord ++ tailWord_1390510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390510).length < 2 ^ (prefixWord ++ tailWord_1390510).sum := by decide
  have hdescent : baseEnd_1390510 < baseStart_1390510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390515 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 4]
def baseStart_1390515 : Nat := 118140960795 + 1390515 * 2 ^ 59
def prefixEnd_1390515 : Nat := 4983230072969 + 3 ^ 40 * 1390515 * 2
def baseEnd_1390515 : Nat := 317334467682992149941175

theorem tailTrace_1390515 : CollatzResearch.WordTrace tailWord_1390515 prefixEnd_1390515 317334467682992149941175 := by
  unfold tailWord_1390515
  simp only [CollatzResearch.WordTrace]
  refine ⟨50716248557409110900276999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33810832371606073933517999 50716248557409110900276999)
  ·
    refine ⟨76074372836113666350415499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50716248557409110900276999 76074372836113666350415499)
    ·
      refine ⟨114111559254170499525623249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76074372836113666350415499 114111559254170499525623249)
      ·
        refine ⟨85583669440627874644217437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114111559254170499525623249 85583669440627874644217437)
        ·
          refine ⟨32093876040235452991581539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85583669440627874644217437 32093876040235452991581539)
          ·
            refine ⟨48140814060353179487372309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32093876040235452991581539 48140814060353179487372309)
            ·
              refine ⟨2256600659079055288470577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48140814060353179487372309 2256600659079055288470577)
              ·
                refine ⟨1692450494309291466352933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2256600659079055288470577 1692450494309291466352933)
                ·
                  refine ⟨317334467682992149941175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1692450494309291466352933 317334467682992149941175)
                  ·
                    rfl

theorem cell21_1390515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 4].length) (baseStart_1390515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390515 prefixEnd_1390515 := by exact prefixLift 1390515
  have htrace : WordTrace (prefixWord ++ tailWord_1390515) baseStart_1390515 baseEnd_1390515 := by
    simpa [prefixWord, tailWord_1390515, baseEnd_1390515] using wordTrace_append hprefix tailTrace_1390515
  have hstable : (prefixWord ++ tailWord_1390515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390515).length < 2 ^ (prefixWord ++ tailWord_1390515).sum := by decide
  have hdescent : baseEnd_1390515 < baseStart_1390515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390577 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 5]
def baseStart_1390577 : Nat := 118140960795 + 1390577 * 2 ^ 59
def prefixEnd_1390577 : Nat := 4983230072969 + 3 ^ 40 * 1390577 * 2
def baseEnd_1390577 : Nat := 317348616927693819907715

theorem tailTrace_1390577 : CollatzResearch.WordTrace tailWord_1390577 prefixEnd_1390577 317348616927693819907715 := by
  unfold tailWord_1390577
  simp only [CollatzResearch.WordTrace]
  refine ⟨50718509883184495489033985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33812339922122996992689323 50718509883184495489033985)
  ·
    refine ⟨38038882412388371616775489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50718509883184495489033985 38038882412388371616775489)
    ·
      refine ⟨28529161809291278712581617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38038882412388371616775489 28529161809291278712581617)
      ·
        refine ⟨21396871356968459034436213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28529161809291278712581617 21396871356968459034436213)
        ·
          refine ⟨2005956689715793034478395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21396871356968459034436213 2005956689715793034478395)
          ·
            refine ⟨3008935034573689551717593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005956689715793034478395 3008935034573689551717593)
            ·
              refine ⟨2256701275930267163788195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3008935034573689551717593 2256701275930267163788195)
              ·
                refine ⟨3385051913895400745682293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2256701275930267163788195 3385051913895400745682293)
                ·
                  refine ⟨317348616927693819907715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3385051913895400745682293 317348616927693819907715)
                  ·
                    rfl

theorem cell21_1390577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_1390577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390577 prefixEnd_1390577 := by exact prefixLift 1390577
  have htrace : WordTrace (prefixWord ++ tailWord_1390577) baseStart_1390577 baseEnd_1390577 := by
    simpa [prefixWord, tailWord_1390577, baseEnd_1390577] using wordTrace_append hprefix tailTrace_1390577
  have hstable : (prefixWord ++ tailWord_1390577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390577).length < 2 ^ (prefixWord ++ tailWord_1390577).sum := by decide
  have hdescent : baseEnd_1390577 < baseStart_1390577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390684 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_1390684 : Nat := 118140960795 + 1390684 * 2 ^ 59
def prefixEnd_1390684 : Nat := 4983230072969 + 3 ^ 40 * 1390684 * 2
def baseEnd_1390684 : Nat := 317373035785485411624163

theorem tailTrace_1390684 : CollatzResearch.WordTrace tailWord_1390684 prefixEnd_1390684 317373035785485411624163 := by
  unfold tailWord_1390684
  simp only [CollatzResearch.WordTrace]
  refine ⟨25361206246898426381589553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33814941662531235175452737 25361206246898426381589553)
  ·
    refine ⟨19020904685173819786192165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25361206246898426381589553 19020904685173819786192165)
    ·
      refine ⟨3566419628470091209911031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19020904685173819786192165 3566419628470091209911031)
      ·
        refine ⟨5349629442705136814866547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3566419628470091209911031 5349629442705136814866547)
        ·
          refine ⟨8024444164057705222299821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5349629442705136814866547 8024444164057705222299821)
          ·
            refine ⟨3009166561521639458362433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8024444164057705222299821 3009166561521639458362433)
            ·
              refine ⟨2256874921141229593771825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009166561521639458362433 2256874921141229593771825)
              ·
                refine ⟨1692656190855922195328869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2256874921141229593771825 1692656190855922195328869)
                ·
                  refine ⟨317373035785485411624163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1692656190855922195328869 317373035785485411624163)
                  ·
                    rfl

theorem cell21_1390684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_1390684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390684 prefixEnd_1390684 := by exact prefixLift 1390684
  have htrace : WordTrace (prefixWord ++ tailWord_1390684) baseStart_1390684 baseEnd_1390684 := by
    simpa [prefixWord, tailWord_1390684, baseEnd_1390684] using wordTrace_append hprefix tailTrace_1390684
  have hstable : (prefixWord ++ tailWord_1390684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390684).length < 2 ^ (prefixWord ++ tailWord_1390684).sum := by decide
  have hdescent : baseEnd_1390684 < baseStart_1390684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390729 : List Nat := [1, 2, 1, 1, 4, 2, 4, 3, 3]
def baseStart_1390729 : Nat := 118140960795 + 1390729 * 2 ^ 59
def prefixEnd_1390729 : Nat := 4983230072969 + 3 ^ 40 * 1390729 * 2
def baseEnd_1390729 : Nat := 317383305398575333374071

theorem tailTrace_1390729 : CollatzResearch.WordTrace tailWord_1390729 prefixEnd_1390729 317383305398575333374071 := by
  unfold tailWord_1390729
  simp only [CollatzResearch.WordTrace]
  refine ⟨50724053778633825448567241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33816035852422550299044827 50724053778633825448567241)
  ·
    refine ⟨38043040333975369086425431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50724053778633825448567241 38043040333975369086425431)
    ·
      refine ⟨57064560500963053629638147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38043040333975369086425431 57064560500963053629638147)
      ·
        refine ⟨85596840751444580444457221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57064560500963053629638147 85596840751444580444457221)
        ·
          refine ⟨16049407640895858833335729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85596840751444580444457221 16049407640895858833335729)
          ·
            refine ⟨12037055730671894125001797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16049407640895858833335729 12037055730671894125001797)
            ·
              refine ⟨2256947949500980148437837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12037055730671894125001797 2256947949500980148437837)
              ·
                refine ⟨846355481062867555664189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2256947949500980148437837 846355481062867555664189)
                ·
                  refine ⟨317383305398575333374071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846355481062867555664189 317383305398575333374071)
                  ·
                    rfl

theorem cell21_1390729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 3].length) (baseStart_1390729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390729 prefixEnd_1390729 := by exact prefixLift 1390729
  have htrace : WordTrace (prefixWord ++ tailWord_1390729) baseStart_1390729 baseEnd_1390729 := by
    simpa [prefixWord, tailWord_1390729, baseEnd_1390729] using wordTrace_append hprefix tailTrace_1390729
  have hstable : (prefixWord ++ tailWord_1390729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390729).length < 2 ^ (prefixWord ++ tailWord_1390729).sum := by decide
  have hdescent : baseEnd_1390729 < baseStart_1390729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390743 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 6]
def baseStart_1390743 : Nat := 118140960795 + 1390743 * 2 ^ 59
def prefixEnd_1390743 : Nat := 4983230072969 + 3 ^ 40 * 1390743 * 2
def baseEnd_1390743 : Nat := 317386500389314420140709

theorem tailTrace_1390743 : CollatzResearch.WordTrace tailWord_1390743 prefixEnd_1390743 317386500389314420140709 := by
  unfold tailWord_1390743
  simp only [CollatzResearch.WordTrace]
  refine ⟨50724564400583105839576883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33816376267055403893051255 50724564400583105839576883)
  ·
    refine ⟨76086846600874658759365325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50724564400583105839576883 76086846600874658759365325)
    ·
      refine ⟨28532567475327997034761997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76086846600874658759365325 28532567475327997034761997)
      ·
        refine ⟨10699712803247998888035749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28532567475327997034761997 10699712803247998888035749)
        ·
          refine ⟨2006196150608999791506703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10699712803247998888035749 2006196150608999791506703)
          ·
            refine ⟨3009294225913499687260055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006196150608999791506703 3009294225913499687260055)
            ·
              refine ⟨4513941338870249530890083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009294225913499687260055 4513941338870249530890083)
              ·
                refine ⟨6770912008305374296335125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513941338870249530890083 6770912008305374296335125)
                ·
                  refine ⟨317386500389314420140709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6770912008305374296335125 317386500389314420140709)
                  ·
                    rfl

theorem cell21_1390743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 6].length) (baseStart_1390743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390743 prefixEnd_1390743 := by exact prefixLift 1390743
  have htrace : WordTrace (prefixWord ++ tailWord_1390743) baseStart_1390743 baseEnd_1390743 := by
    simpa [prefixWord, tailWord_1390743, baseEnd_1390743] using wordTrace_append hprefix tailTrace_1390743
  have hstable : (prefixWord ++ tailWord_1390743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390743).length < 2 ^ (prefixWord ++ tailWord_1390743).sum := by decide
  have hdescent : baseEnd_1390743 < baseStart_1390743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390892 : List Nat := [2, 2, 1, 1, 1, 3, 2, 9]
def baseStart_1390892 : Nat := 118140960795 + 1390892 * 2 ^ 59
def prefixEnd_1390892 : Nat := 4983230072969 + 3 ^ 40 * 1390892 * 2
def baseEnd_1390892 : Nat := 105806834739774424052357

theorem tailTrace_1390892 : CollatzResearch.WordTrace tailWord_1390892 prefixEnd_1390892 105806834739774424052357 := by
  unfold tailWord_1390892
  simp only [CollatzResearch.WordTrace]
  refine ⟨25364999438521652143375465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33819999251362202857833953 25364999438521652143375465)
  ·
    refine ⟨19023749578891239107531599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25364999438521652143375465 19023749578891239107531599)
    ·
      refine ⟨28535624368336858661297399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19023749578891239107531599 28535624368336858661297399)
      ·
        refine ⟨42803436552505287991946099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28535624368336858661297399 42803436552505287991946099)
        ·
          refine ⟨64205154828757931987919149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42803436552505287991946099 64205154828757931987919149)
          ·
            refine ⟨24076933060784224495469681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64205154828757931987919149 24076933060784224495469681)
            ·
              refine ⟨18057699795588168371602261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24076933060784224495469681 18057699795588168371602261)
              ·
                refine ⟨105806834739774424052357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18057699795588168371602261 105806834739774424052357)
                ·
                  rfl

theorem cell21_1390892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_1390892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390892 prefixEnd_1390892 := by exact prefixLift 1390892
  have htrace : WordTrace (prefixWord ++ tailWord_1390892) baseStart_1390892 baseEnd_1390892 := by
    simpa [prefixWord, tailWord_1390892, baseEnd_1390892] using wordTrace_append hprefix tailTrace_1390892
  have hstable : (prefixWord ++ tailWord_1390892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390892).length < 2 ^ (prefixWord ++ tailWord_1390892).sum := by decide
  have hdescent : baseEnd_1390892 < baseStart_1390892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390898 : List Nat := [3, 2, 1, 1, 5, 1, 2, 3, 3]
def baseStart_1390898 : Nat := 118140960795 + 1390898 * 2 ^ 59
def prefixEnd_1390898 : Nat := 4983230072969 + 3 ^ 40 * 1390898 * 2
def baseEnd_1390898 : Nat := 317421873501068595057059

theorem tailTrace_1390898 : CollatzResearch.WordTrace tailWord_1390898 prefixEnd_1390898 317421873501068595057059 := by
  unfold tailWord_1390898
  simp only [CollatzResearch.WordTrace]
  refine ⟨12682554428755391827867337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33820145143347711540979565 12682554428755391827867337)
  ·
    refine ⟨9511915821566543870900503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12682554428755391827867337 9511915821566543870900503)
    ·
      refine ⟨14267873732349815806350755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9511915821566543870900503 14267873732349815806350755)
      ·
        refine ⟨21401810598524723709526133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14267873732349815806350755 21401810598524723709526133)
        ·
          refine ⟨2006419743611692847768075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21401810598524723709526133 2006419743611692847768075)
          ·
            refine ⟨3009629615417539271652113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006419743611692847768075 3009629615417539271652113)
            ·
              refine ⟨2257222211563154453739085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009629615417539271652113 2257222211563154453739085)
              ·
                refine ⟨846458329336182920152157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257222211563154453739085 846458329336182920152157)
                ·
                  refine ⟨317421873501068595057059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846458329336182920152157 317421873501068595057059)
                  ·
                    rfl

theorem cell21_1390898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_1390898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390898 prefixEnd_1390898 := by exact prefixLift 1390898
  have htrace : WordTrace (prefixWord ++ tailWord_1390898) baseStart_1390898 baseEnd_1390898 := by
    simpa [prefixWord, tailWord_1390898, baseEnd_1390898] using wordTrace_append hprefix tailTrace_1390898
  have hstable : (prefixWord ++ tailWord_1390898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390898).length < 2 ^ (prefixWord ++ tailWord_1390898).sum := by decide
  have hdescent : baseEnd_1390898 < baseStart_1390898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390985 : List Nat := [1, 2, 1, 1, 6, 2, 2, 6]
def baseStart_1390985 : Nat := 118140960795 + 1390985 * 2 ^ 59
def prefixEnd_1390985 : Nat := 4983230072969 + 3 ^ 40 * 1390985 * 2
def baseEnd_1390985 : Nat := 105813909362125259035627

theorem tailTrace_1390985 : CollatzResearch.WordTrace tailWord_1390985 prefixEnd_1390985 105813909362125259035627 := by
  unfold tailWord_1390985
  simp only [CollatzResearch.WordTrace]
  refine ⟨50733390865706381169886409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33822260577137587446590939 50733390865706381169886409)
  ·
    refine ⟨38050043149279785877414807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50733390865706381169886409 38050043149279785877414807)
    ·
      refine ⟨57075064723919678816122211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38050043149279785877414807 57075064723919678816122211)
      ·
        refine ⟨85612597085879518224183317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57075064723919678816122211 85612597085879518224183317)
        ·
          refine ⟨4013090488400602416758593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85612597085879518224183317 4013090488400602416758593)
          ·
            refine ⟨3009817866300451812568945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4013090488400602416758593 3009817866300451812568945)
            ·
              refine ⟨2257363399725338859426709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009817866300451812568945 2257363399725338859426709)
              ·
                refine ⟨105813909362125259035627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2257363399725338859426709 105813909362125259035627)
                ·
                  rfl

theorem cell21_1390985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 6].length) (baseStart_1390985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390985 prefixEnd_1390985 := by exact prefixLift 1390985
  have htrace : WordTrace (prefixWord ++ tailWord_1390985) baseStart_1390985 baseEnd_1390985 := by
    simpa [prefixWord, tailWord_1390985, baseEnd_1390985] using wordTrace_append hprefix tailTrace_1390985
  have hstable : (prefixWord ++ tailWord_1390985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390985).length < 2 ^ (prefixWord ++ tailWord_1390985).sum := by decide
  have hdescent : baseEnd_1390985 < baseStart_1390985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390988 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 4]
def baseStart_1390988 : Nat := 118140960795 + 1390988 * 2 ^ 59
def prefixEnd_1390988 : Nat := 4983230072969 + 3 ^ 40 * 1390988 * 2
def baseEnd_1390988 : Nat := 317442412727248438556875

theorem tailTrace_1390988 : CollatzResearch.WordTrace tailWord_1390988 prefixEnd_1390988 317442412727248438556875 := by
  unfold tailWord_1390988
  simp only [CollatzResearch.WordTrace]
  refine ⟨25366750142347756341122809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33822333523130341788163745 25366750142347756341122809)
  ·
    refine ⟨19025062606760817255842107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25366750142347756341122809 19025062606760817255842107)
    ·
      refine ⟨28537593910141225883763161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19025062606760817255842107 28537593910141225883763161)
      ·
        refine ⟨21403195432605919412822371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28537593910141225883763161 21403195432605919412822371)
        ·
          refine ⟨32104793148908879119233557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21403195432605919412822371 32104793148908879119233557)
          ·
            refine ⟨1504912178855103708714073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32104793148908879119233557 1504912178855103708714073)
            ·
              refine ⟨1128684134141327781535555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504912178855103708714073 1128684134141327781535555)
              ·
                refine ⟨1693026201211991672303333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128684134141327781535555 1693026201211991672303333)
                ·
                  refine ⟨317442412727248438556875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1693026201211991672303333 317442412727248438556875)
                  ·
                    rfl

theorem cell21_1390988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_1390988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390988 prefixEnd_1390988 := by exact prefixLift 1390988
  have htrace : WordTrace (prefixWord ++ tailWord_1390988) baseStart_1390988 baseEnd_1390988 := by
    simpa [prefixWord, tailWord_1390988, baseEnd_1390988] using wordTrace_append hprefix tailTrace_1390988
  have hstable : (prefixWord ++ tailWord_1390988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390988).length < 2 ^ (prefixWord ++ tailWord_1390988).sum := by decide
  have hdescent : baseEnd_1390988 < baseStart_1390988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390999 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 5]
def baseStart_1390999 : Nat := 118140960795 + 1390999 * 2 ^ 59
def prefixEnd_1390999 : Nat := 4983230072969 + 3 ^ 40 * 1390999 * 2
def baseEnd_1390999 : Nat := 317444923077114863873519

theorem tailTrace_1390999 : CollatzResearch.WordTrace tailWord_1390999 prefixEnd_1390999 317444923077114863873519 := by
  unfold tailWord_1390999
  simp only [CollatzResearch.WordTrace]
  refine ⟨50733901487655661560896051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33822600991770441040597367 50733901487655661560896051)
  ·
    refine ⟨76100852231483492341344077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50733901487655661560896051 76100852231483492341344077)
    ·
      refine ⟨28537819586806309628004029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76100852231483492341344077 28537819586806309628004029)
      ·
        refine ⟨10701682345052366110501511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28537819586806309628004029 10701682345052366110501511)
        ·
          refine ⟨16052523517578549165752267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10701682345052366110501511 16052523517578549165752267)
          ·
            refine ⟨24078785276367823748628401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16052523517578549165752267 24078785276367823748628401)
            ·
              refine ⟨18059088957275867811471301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24078785276367823748628401 18059088957275867811471301)
              ·
                refine ⟨3386079179489225214650869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18059088957275867811471301 3386079179489225214650869)
                ·
                  refine ⟨317444923077114863873519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3386079179489225214650869 317444923077114863873519)
                  ·
                    rfl

theorem cell21_1390999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_1390999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1390999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1390999 prefixEnd_1390999 := by exact prefixLift 1390999
  have htrace : WordTrace (prefixWord ++ tailWord_1390999) baseStart_1390999 baseEnd_1390999 := by
    simpa [prefixWord, tailWord_1390999, baseEnd_1390999] using wordTrace_append hprefix tailTrace_1390999
  have hstable : (prefixWord ++ tailWord_1390999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390999).length < 2 ^ (prefixWord ++ tailWord_1390999).sum := by decide
  have hdescent : baseEnd_1390999 < baseStart_1390999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391033 : List Nat := [1, 2, 1, 4, 3, 2, 1, 4, 3]
def baseStart_1391033 : Nat := 118140960795 + 1391033 * 2 ^ 59
def prefixEnd_1391033 : Nat := 4983230072969 + 3 ^ 40 * 1391033 * 2
def baseEnd_1391033 : Nat := 317452682340338360306783

theorem tailTrace_1391033 : CollatzResearch.WordTrace tailWord_1391033 prefixEnd_1391033 317452682340338360306783 := by
  unfold tailWord_1391033
  simp only [CollatzResearch.WordTrace]
  refine ⟨50735141569532485367633753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33823427713021656911755835 50735141569532485367633753)
  ·
    refine ⟨38051356177149364025725315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50735141569532485367633753 38051356177149364025725315)
    ·
      refine ⟨57077034265724046038587973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38051356177149364025725315 57077034265724046038587973)
      ·
        refine ⟨10701943924823258632235245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57077034265724046038587973 10701943924823258632235245)
        ·
          refine ⟨4013228971808721987088217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10701943924823258632235245 4013228971808721987088217)
          ·
            refine ⟨3009921728856541490316163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4013228971808721987088217 3009921728856541490316163)
            ·
              refine ⟨4514882593284812235474245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009921728856541490316163 4514882593284812235474245)
              ·
                refine ⟨846540486240902294151421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4514882593284812235474245 846540486240902294151421)
                ·
                  refine ⟨317452682340338360306783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846540486240902294151421 317452682340338360306783)
                  ·
                    rfl

theorem cell21_1391033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 3].length) (baseStart_1391033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391033 prefixEnd_1391033 := by exact prefixLift 1391033
  have htrace : WordTrace (prefixWord ++ tailWord_1391033) baseStart_1391033 baseEnd_1391033 := by
    simpa [prefixWord, tailWord_1391033, baseEnd_1391033] using wordTrace_append hprefix tailTrace_1391033
  have hstable : (prefixWord ++ tailWord_1391033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391033).length < 2 ^ (prefixWord ++ tailWord_1391033).sum := by decide
  have hdescent : baseEnd_1391033 < baseStart_1391033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391143 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 5]
def baseStart_1391143 : Nat := 118140960795 + 1391143 * 2 ^ 59
def prefixEnd_1391143 : Nat := 4983230072969 + 3 ^ 40 * 1391143 * 2
def baseEnd_1391143 : Nat := 317477785839002613473225

theorem tailTrace_1391143 : CollatzResearch.WordTrace tailWord_1391143 prefixEnd_1391143 317477785839002613473225 := by
  unfold tailWord_1391143
  simp only [CollatzResearch.WordTrace]
  refine ⟨50739153599133974154138083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33826102399422649436092055 50739153599133974154138083)
  ·
    refine ⟨76108730398700961231207125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50739153599133974154138083 76108730398700961231207125)
    ·
      refine ⟨1783798368719553778856417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 76108730398700961231207125 1783798368719553778856417)
      ·
        refine ⟨1337848776539665334142313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1783798368719553778856417 1337848776539665334142313)
        ·
          refine ⟨1003386582404749000606735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1337848776539665334142313 1003386582404749000606735)
          ·
            refine ⟨1505079873607123500910103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003386582404749000606735 1505079873607123500910103)
            ·
              refine ⟨2257619810410685251365155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505079873607123500910103 2257619810410685251365155)
              ·
                refine ⟨3386429715616027877047733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257619810410685251365155 3386429715616027877047733)
                ·
                  refine ⟨317477785839002613473225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3386429715616027877047733 317477785839002613473225)
                  ·
                    rfl

theorem cell21_1391143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 5].length) (baseStart_1391143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391143 prefixEnd_1391143 := by exact prefixLift 1391143
  have htrace : WordTrace (prefixWord ++ tailWord_1391143) baseStart_1391143 baseEnd_1391143 := by
    simpa [prefixWord, tailWord_1391143, baseEnd_1391143] using wordTrace_append hprefix tailTrace_1391143
  have hstable : (prefixWord ++ tailWord_1391143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391143).length < 2 ^ (prefixWord ++ tailWord_1391143).sum := by decide
  have hdescent : baseEnd_1391143 < baseStart_1391143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391196 : List Nat := [2, 2, 4, 1, 12]
def baseStart_1391196 : Nat := 118140960795 + 1391196 * 2 ^ 59
def prefixEnd_1391196 : Nat := 4983230072969 + 3 ^ 40 * 1391196 * 2
def baseEnd_1391196 : Nat := 3919628162482546902343

theorem tailTrace_1391196 : CollatzResearch.WordTrace tailWord_1391196 prefixEnd_1391196 3919628162482546902343 := by
  unfold tailWord_1391196
  simp only [CollatzResearch.WordTrace]
  refine ⟨25370543333970982102908721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33827391111961309470544961 25370543333970982102908721)
  ·
    refine ⟨19027907500478236577181541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25370543333970982102908721 19027907500478236577181541)
    ·
      refine ⟨3567732656339669358221539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19027907500478236577181541 3567732656339669358221539)
      ·
        refine ⟨5351598984509504037332309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567732656339669358221539 5351598984509504037332309)
        ·
          refine ⟨3919628162482546902343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5351598984509504037332309 3919628162482546902343)
          ·
            rfl

theorem cell21_1391196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 12].length) (baseStart_1391196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391196 prefixEnd_1391196 := by exact prefixLift 1391196
  have htrace : WordTrace (prefixWord ++ tailWord_1391196) baseStart_1391196 baseEnd_1391196 := by
    simpa [prefixWord, tailWord_1391196, baseEnd_1391196] using wordTrace_append hprefix tailTrace_1391196
  have hstable : (prefixWord ++ tailWord_1391196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391196).length < 2 ^ (prefixWord ++ tailWord_1391196).sum := by decide
  have hdescent : baseEnd_1391196 < baseStart_1391196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391213 : List Nat := [1, 5, 1, 1, 3, 1, 3, 6]
def baseStart_1391213 : Nat := 118140960795 + 1391213 * 2 ^ 59
def prefixEnd_1391213 : Nat := 4983230072969 + 3 ^ 40 * 1391213 * 2
def baseEnd_1391213 : Nat := 105831253597566015768805

theorem tailTrace_1391213 : CollatzResearch.WordTrace tailWord_1391213 prefixEnd_1391213 105831253597566015768805 := by
  unfold tailWord_1391213
  simp only [CollatzResearch.WordTrace]
  refine ⟨50741706708880376109186293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33827804472586917406124195 50741706708880376109186293)
  ·
    refine ⟨4757035003957535260236215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50741706708880376109186293 4757035003957535260236215)
    ·
      refine ⟨7135552505936302890354323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4757035003957535260236215 7135552505936302890354323)
      ·
        refine ⟨10703328758904454335531485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7135552505936302890354323 10703328758904454335531485)
        ·
          refine ⟨4013748284589170375824307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10703328758904454335531485 4013748284589170375824307)
          ·
            refine ⟨6020622426883755563736461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013748284589170375824307 6020622426883755563736461)
            ·
              refine ⟨2257733410081408336401173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6020622426883755563736461 2257733410081408336401173)
              ·
                refine ⟨105831253597566015768805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2257733410081408336401173 105831253597566015768805)
                ·
                  rfl

theorem cell21_1391213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 6].length) (baseStart_1391213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391213 prefixEnd_1391213 := by exact prefixLift 1391213
  have htrace : WordTrace (prefixWord ++ tailWord_1391213) baseStart_1391213 baseEnd_1391213 := by
    simpa [prefixWord, tailWord_1391213, baseEnd_1391213] using wordTrace_append hprefix tailTrace_1391213
  have hstable : (prefixWord ++ tailWord_1391213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391213).length < 2 ^ (prefixWord ++ tailWord_1391213).sum := by decide
  have hdescent : baseEnd_1391213 < baseStart_1391213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391241 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 6]
def baseStart_1391241 : Nat := 118140960795 + 1391241 * 2 ^ 59
def prefixEnd_1391241 : Nat := 4983230072969 + 3 ^ 40 * 1391241 * 2
def baseEnd_1391241 : Nat := 317500150774176220839691

theorem tailTrace_1391241 : CollatzResearch.WordTrace tailWord_1391241 prefixEnd_1391241 317500150774176220839691 := by
  unfold tailWord_1391241
  simp only [CollatzResearch.WordTrace]
  refine ⟨50742727952778936891205577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33828485301852624594137051 50742727952778936891205577)
  ·
    refine ⟨38057045964584202668404183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50742727952778936891205577 38057045964584202668404183)
    ·
      refine ⟨57085568946876304002606275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38057045964584202668404183 57085568946876304002606275)
      ·
        refine ⟨85628353420314456003909413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57085568946876304002606275 85628353420314456003909413)
        ·
          refine ⟨16055316266308960500733015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85628353420314456003909413 16055316266308960500733015)
          ·
            refine ⟨24082974399463440751099523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16055316266308960500733015 24082974399463440751099523)
            ·
              refine ⟨36124461599195161126649285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24082974399463440751099523 36124461599195161126649285)
              ·
                refine ⟨6773336549849092711246741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36124461599195161126649285 6773336549849092711246741)
                ·
                  refine ⟨317500150774176220839691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6773336549849092711246741 317500150774176220839691)
                  ·
                    rfl

theorem cell21_1391241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_1391241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391241 prefixEnd_1391241 := by exact prefixLift 1391241
  have htrace : WordTrace (prefixWord ++ tailWord_1391241) baseStart_1391241 baseEnd_1391241 := by
    simpa [prefixWord, tailWord_1391241, baseEnd_1391241] using wordTrace_append hprefix tailTrace_1391241
  have hstable : (prefixWord ++ tailWord_1391241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391241).length < 2 ^ (prefixWord ++ tailWord_1391241).sum := by decide
  have hdescent : baseEnd_1391241 < baseStart_1391241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391320 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 5]
def baseStart_1391320 : Nat := 118140960795 + 1391320 * 2 ^ 59
def prefixEnd_1391320 : Nat := 4983230072969 + 3 ^ 40 * 1391320 * 2
def baseEnd_1391320 : Nat := 317518179650489639022863

theorem tailTrace_1391320 : CollatzResearch.WordTrace tailWord_1391320 prefixEnd_1391320 317518179650489639022863 := by
  unfold tailWord_1391320
  simp only [CollatzResearch.WordTrace]
  refine ⟨25372804659746366691665707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33830406212995155588887609 25372804659746366691665707)
  ·
    refine ⟨38059206989619550037498561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25372804659746366691665707 38059206989619550037498561)
    ·
      refine ⟨28544405242214662528123921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38059206989619550037498561 28544405242214662528123921)
      ·
        refine ⟨21408303931660996896092941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28544405242214662528123921 21408303931660996896092941)
        ·
          refine ⟨8028113974372873836034853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21408303931660996896092941 8028113974372873836034853)
          ·
            refine ⟨1505271370194913844256535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8028113974372873836034853 1505271370194913844256535)
            ·
              refine ⟨2257907055292370766384803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505271370194913844256535 2257907055292370766384803)
              ·
                refine ⟨3386860582938556149577205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257907055292370766384803 3386860582938556149577205)
                ·
                  refine ⟨317518179650489639022863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3386860582938556149577205 317518179650489639022863)
                  ·
                    rfl

theorem cell21_1391320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_1391320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391320 prefixEnd_1391320 := by exact prefixLift 1391320
  have htrace : WordTrace (prefixWord ++ tailWord_1391320) baseStart_1391320 baseEnd_1391320 := by
    simpa [prefixWord, tailWord_1391320, baseEnd_1391320] using wordTrace_append hprefix tailTrace_1391320
  have hstable : (prefixWord ++ tailWord_1391320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391320).length < 2 ^ (prefixWord ++ tailWord_1391320).sum := by decide
  have hdescent : baseEnd_1391320 < baseStart_1391320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391396 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_1391396 : Nat := 118140960795 + 1391396 * 2 ^ 59
def prefixEnd_1391396 : Nat := 4983230072969 + 3 ^ 40 * 1391396 * 2
def baseEnd_1391396 : Nat := 317535523885930395756041

theorem tailTrace_1391396 : CollatzResearch.WordTrace tailWord_1391396 prefixEnd_1391396 317535523885930395756041 := by
  unfold tailWord_1391396
  simp only [CollatzResearch.WordTrace]
  refine ⟨25374190633608699181549021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33832254178144932242065361 25374190633608699181549021)
  ·
    refine ⟨9515321487603262193080883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25374190633608699181549021 9515321487603262193080883)
    ·
      refine ⟨14272982231404893289621325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9515321487603262193080883 14272982231404893289621325)
      ·
        refine ⟨5352368336776834983607997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14272982231404893289621325 5352368336776834983607997)
        ·
          refine ⟨2007138126291313118852999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5352368336776834983607997 2007138126291313118852999)
          ·
            refine ⟨3010707189436969678279499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007138126291313118852999 3010707189436969678279499)
            ·
              refine ⟨4516060784155454517419249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3010707189436969678279499 4516060784155454517419249)
              ·
                refine ⟨3387045588116590888064437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4516060784155454517419249 3387045588116590888064437)
                ·
                  refine ⟨317535523885930395756041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3387045588116590888064437 317535523885930395756041)
                  ·
                    rfl

theorem cell21_1391396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_1391396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391396 prefixEnd_1391396 := by exact prefixLift 1391396
  have htrace : WordTrace (prefixWord ++ tailWord_1391396) baseStart_1391396 baseEnd_1391396 := by
    simpa [prefixWord, tailWord_1391396, baseEnd_1391396] using wordTrace_append hprefix tailTrace_1391396
  have hstable : (prefixWord ++ tailWord_1391396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391396).length < 2 ^ (prefixWord ++ tailWord_1391396).sum := by decide
  have hdescent : baseEnd_1391396 < baseStart_1391396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391413 : List Nat := [1, 3, 3, 1, 3, 2, 2, 3, 3]
def baseStart_1391413 : Nat := 118140960795 + 1391413 * 2 ^ 59
def prefixEnd_1391413 : Nat := 4983230072969 + 3 ^ 40 * 1391413 * 2
def baseEnd_1391413 : Nat := 317539403517542143972673

theorem tailTrace_1391413 : CollatzResearch.WordTrace tailWord_1391413 prefixEnd_1391413 317539403517542143972673 := by
  unfold tailWord_1391413
  simp only [CollatzResearch.WordTrace]
  refine ⟨50749001308155810266466893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33832667538770540177644595 50749001308155810266466893)
  ·
    refine ⟨19030875490558428849925085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50749001308155810266466893 19030875490558428849925085)
    ·
      refine ⟨7136578308959410818721907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19030875490558428849925085 7136578308959410818721907)
      ·
        refine ⟨10704867463439116228082861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7136578308959410818721907 10704867463439116228082861)
        ·
          refine ⟨4014325298789668585531073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10704867463439116228082861 4014325298789668585531073)
          ·
            refine ⟨3010743974092251439148305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4014325298789668585531073 3010743974092251439148305)
            ·
              refine ⟨2258057980569188579361229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3010743974092251439148305 2258057980569188579361229)
              ·
                refine ⟨846771742713445717260461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2258057980569188579361229 846771742713445717260461)
                ·
                  refine ⟨317539403517542143972673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846771742713445717260461 317539403517542143972673)
                  ·
                    rfl

theorem cell21_1391413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_1391413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391413 prefixEnd_1391413 := by exact prefixLift 1391413
  have htrace : WordTrace (prefixWord ++ tailWord_1391413) baseStart_1391413 baseEnd_1391413 := by
    simpa [prefixWord, tailWord_1391413, baseEnd_1391413] using wordTrace_append hprefix tailTrace_1391413
  have hstable : (prefixWord ++ tailWord_1391413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391413).length < 2 ^ (prefixWord ++ tailWord_1391413).sum := by decide
  have hdescent : baseEnd_1391413 < baseStart_1391413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391430 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1391430 : Nat := 118140960795 + 1391430 * 2 ^ 59
def prefixEnd_1391430 : Nat := 4983230072969 + 3 ^ 40 * 1391430 * 2
def baseEnd_1391430 : Nat := 317543283149153892189305

theorem tailTrace_1391430 : CollatzResearch.WordTrace tailWord_1391430 prefixEnd_1391430 317543283149153892189305 := by
  unfold tailWord_1391430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1585925667159194442807367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33833080899396148113223829 1585925667159194442807367)
  ·
    refine ⟨2378888500738791664211051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1585925667159194442807367 2378888500738791664211051)
    ·
      refine ⟨3568332751108187496316577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2378888500738791664211051 3568332751108187496316577)
      ·
        refine ⟨2676249563331140622237433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3568332751108187496316577 2676249563331140622237433)
        ·
          refine ⟨2007187172498355466678075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2676249563331140622237433 2007187172498355466678075)
          ·
            refine ⟨3010780758747533200017113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007187172498355466678075 3010780758747533200017113)
            ·
              refine ⟨2258085569060649900012835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3010780758747533200017113 2258085569060649900012835)
              ·
                refine ⟨3387128353590974850019253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258085569060649900012835 3387128353590974850019253)
                ·
                  refine ⟨317543283149153892189305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3387128353590974850019253 317543283149153892189305)
                  ·
                    rfl

theorem cell21_1391430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1391430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391430 prefixEnd_1391430 := by exact prefixLift 1391430
  have htrace : WordTrace (prefixWord ++ tailWord_1391430) baseStart_1391430 baseEnd_1391430 := by
    simpa [prefixWord, tailWord_1391430, baseEnd_1391430] using wordTrace_append hprefix tailTrace_1391430
  have hstable : (prefixWord ++ tailWord_1391430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391430).length < 2 ^ (prefixWord ++ tailWord_1391430).sum := by decide
  have hdescent : baseEnd_1391430 < baseStart_1391430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391444 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1391444 : Nat := 118140960795 + 1391444 * 2 ^ 59
def prefixEnd_1391444 : Nat := 4983230072969 + 3 ^ 40 * 1391444 * 2
def baseEnd_1391444 : Nat := 317546478139892978955943

theorem tailTrace_1391444 : CollatzResearch.WordTrace tailWord_1391444 prefixEnd_1391444 317546478139892978955943 := by
  unfold tailWord_1391444
  simp only [CollatzResearch.WordTrace]
  refine ⟨25375065985521751280422693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33833421314029001707230257 25375065985521751280422693)
  ·
    refine ⟨4757824872285328365079255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25375065985521751280422693 4757824872285328365079255)
    ·
      refine ⟨7136737308427992547618883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4757824872285328365079255 7136737308427992547618883)
      ·
        refine ⟨10705105962641988821428325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7136737308427992547618883 10705105962641988821428325)
        ·
          refine ⟨2007207367995372904017811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10705105962641988821428325 2007207367995372904017811)
          ·
            refine ⟨3010811051993059356026717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007207367995372904017811 3010811051993059356026717)
            ·
              refine ⟨1129054144497397258510019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3010811051993059356026717 1129054144497397258510019)
              ·
                refine ⟨1693581216746095887765029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129054144497397258510019 1693581216746095887765029)
                ·
                  refine ⟨317546478139892978955943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1693581216746095887765029 317546478139892978955943)
                  ·
                    rfl

theorem cell21_1391444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1391444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391444 prefixEnd_1391444 := by exact prefixLift 1391444
  have htrace : WordTrace (prefixWord ++ tailWord_1391444) baseStart_1391444 baseEnd_1391444 := by
    simpa [prefixWord, tailWord_1391444, baseEnd_1391444] using wordTrace_append hprefix tailTrace_1391444
  have hstable : (prefixWord ++ tailWord_1391444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391444).length < 2 ^ (prefixWord ++ tailWord_1391444).sum := by decide
  have hdescent : baseEnd_1391444 < baseStart_1391444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391472 : List Nat := [2, 1, 1, 1, 4, 1, 5, 3, 3]
def baseStart_1391472 : Nat := 118140960795 + 1391472 * 2 ^ 59
def prefixEnd_1391472 : Nat := 4983230072969 + 3 ^ 40 * 1391472 * 2
def baseEnd_1391472 : Nat := 317552868121371152489219

theorem tailTrace_1391472 : CollatzResearch.WordTrace tailWord_1391472 prefixEnd_1391472 317552868121371152489219 := by
  unfold tailWord_1391472
  simp only [CollatzResearch.WordTrace]
  refine ⟨25375576607471031671432335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33834102143294708895243113 25375576607471031671432335)
  ·
    refine ⟨38063364911206547507148503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25375576607471031671432335 38063364911206547507148503)
    ·
      refine ⟨57095047366809821260722755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38063364911206547507148503 57095047366809821260722755)
      ·
        refine ⟨85642571050214731891084133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57095047366809821260722755 85642571050214731891084133)
        ·
          refine ⟨16057982071915262229578275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85642571050214731891084133 16057982071915262229578275)
          ·
            refine ⟨24086973107872893344367413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16057982071915262229578275 24086973107872893344367413)
            ·
              refine ⟨2258153728863083751034445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24086973107872893344367413 2258153728863083751034445)
              ·
                refine ⟨846807648323656406637917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2258153728863083751034445 846807648323656406637917)
                ·
                  refine ⟨317552868121371152489219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846807648323656406637917 317552868121371152489219)
                  ·
                    rfl

theorem cell21_1391472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 3].length) (baseStart_1391472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391472 prefixEnd_1391472 := by exact prefixLift 1391472
  have htrace : WordTrace (prefixWord ++ tailWord_1391472) baseStart_1391472 baseEnd_1391472 := by
    simpa [prefixWord, tailWord_1391472, baseEnd_1391472] using wordTrace_append hprefix tailTrace_1391472
  have hstable : (prefixWord ++ tailWord_1391472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391472).length < 2 ^ (prefixWord ++ tailWord_1391472).sum := by decide
  have hdescent : baseEnd_1391472 < baseStart_1391472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391483 : List Nat := [1, 1, 1, 1, 1, 5, 11]
def baseStart_1391483 : Nat := 118140960795 + 1391483 * 2 ^ 59
def prefixEnd_1391483 : Nat := 4983230072969 + 3 ^ 40 * 1391483 * 2
def baseEnd_1391483 : Nat := 35283930941248619756207

theorem tailTrace_1391483 : CollatzResearch.WordTrace tailWord_1391483 prefixEnd_1391483 35283930941248619756207 := by
  unfold tailWord_1391483
  simp only [CollatzResearch.WordTrace]
  refine ⟨50751554417902212221515103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33834369611934808147676735 50751554417902212221515103)
  ·
    refine ⟨76127331626853318332272655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50751554417902212221515103 76127331626853318332272655)
    ·
      refine ⟨114190997440279977498408983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76127331626853318332272655 114190997440279977498408983)
      ·
        refine ⟨171286496160419966247613475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114190997440279977498408983 171286496160419966247613475)
        ·
          refine ⟨256929744240629949371420213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171286496160419966247613475 256929744240629949371420213)
          ·
            refine ⟨24087163522559057753570645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256929744240629949371420213 24087163522559057753570645)
            ·
              refine ⟨35283930941248619756207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24087163522559057753570645 35283930941248619756207)
              ·
                rfl

theorem cell21_1391483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 11].length) (baseStart_1391483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391483 prefixEnd_1391483 := by exact prefixLift 1391483
  have htrace : WordTrace (prefixWord ++ tailWord_1391483) baseStart_1391483 baseEnd_1391483 := by
    simpa [prefixWord, tailWord_1391483, baseEnd_1391483] using wordTrace_append hprefix tailTrace_1391483
  have hstable : (prefixWord ++ tailWord_1391483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391483).length < 2 ^ (prefixWord ++ tailWord_1391483).sum := by decide
  have hdescent : baseEnd_1391483 < baseStart_1391483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391652 : List Nat := [2, 3, 1, 4, 1, 1, 9]
def baseStart_1391652 : Nat := 118140960795 + 1391652 * 2 ^ 59
def prefixEnd_1391652 : Nat := 4983230072969 + 3 ^ 40 * 1391652 * 2
def baseEnd_1391652 : Nat := 35288216285970093276539

theorem tailTrace_1391652 : CollatzResearch.WordTrace tailWord_1391652 prefixEnd_1391652 35288216285970093276539 := by
  unfold tailWord_1391652
  simp only [CollatzResearch.WordTrace]
  refine ⟨25378859177144977042208605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33838478902859969389611473 25378859177144977042208605)
  ·
    refine ⟨9517072191429366390828227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25378859177144977042208605 9517072191429366390828227)
    ·
      refine ⟨14275608287144049586242341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9517072191429366390828227 14275608287144049586242341)
      ·
        refine ⟨2676676553839509297420439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14275608287144049586242341 2676676553839509297420439)
        ·
          refine ⟨4015014830759263946130659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676676553839509297420439 4015014830759263946130659)
          ·
            refine ⟨6022522246138895919195989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015014830759263946130659 6022522246138895919195989)
            ·
              refine ⟨35288216285970093276539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6022522246138895919195989 35288216285970093276539)
              ·
                rfl

theorem cell21_1391652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 9].length) (baseStart_1391652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391652 prefixEnd_1391652 := by exact prefixLift 1391652
  have htrace : WordTrace (prefixWord ++ tailWord_1391652) baseStart_1391652 baseEnd_1391652 := by
    simpa [prefixWord, tailWord_1391652, baseEnd_1391652] using wordTrace_append hprefix tailTrace_1391652
  have hstable : (prefixWord ++ tailWord_1391652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391652).length < 2 ^ (prefixWord ++ tailWord_1391652).sum := by decide
  have hdescent : baseEnd_1391652 < baseStart_1391652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391658 : List Nat := [3, 1, 4, 1, 3, 1, 3, 2, 3]
def baseStart_1391658 : Nat := 118140960795 + 1391658 * 2 ^ 59
def prefixEnd_1391658 : Nat := 4983230072969 + 3 ^ 40 * 1391658 * 2
def baseEnd_1391658 : Nat := 317595315855476162388839

theorem tailTrace_1391658 : CollatzResearch.WordTrace tailWord_1391658 prefixEnd_1391658 317595315855476162388839 := by
  unfold tailWord_1391658
  simp only [CollatzResearch.WordTrace]
  refine ⟨12689484298067054277283907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33838624794845478072757085 12689484298067054277283907)
  ·
    refine ⟨19034226447100581415925861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12689484298067054277283907 19034226447100581415925861)
    ·
      refine ⟨3568917458831359015486099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19034226447100581415925861 3568917458831359015486099)
      ·
        refine ⟨5353376188247038523229149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3568917458831359015486099 5353376188247038523229149)
        ·
          refine ⟨2007516070592639446210931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5353376188247038523229149 2007516070592639446210931)
          ·
            refine ⟨3011274105888959169316397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007516070592639446210931 3011274105888959169316397)
            ·
              refine ⟨1129227789708359688493649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3011274105888959169316397 1129227789708359688493649)
              ·
                refine ⟨846920842281269766370237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129227789708359688493649 846920842281269766370237)
                ·
                  refine ⟨317595315855476162388839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846920842281269766370237 317595315855476162388839)
                  ·
                    rfl

theorem cell21_1391658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_1391658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391658 prefixEnd_1391658 := by exact prefixLift 1391658
  have htrace : WordTrace (prefixWord ++ tailWord_1391658) baseStart_1391658 baseEnd_1391658 := by
    simpa [prefixWord, tailWord_1391658, baseEnd_1391658] using wordTrace_append hprefix tailTrace_1391658
  have hstable : (prefixWord ++ tailWord_1391658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391658).length < 2 ^ (prefixWord ++ tailWord_1391658).sum := by decide
  have hdescent : baseEnd_1391658 < baseStart_1391658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391745 : List Nat := [1, 2, 4, 2, 2, 2, 3, 5]
def baseStart_1391745 : Nat := 118140960795 + 1391745 * 2 ^ 59
def prefixEnd_1391745 : Nat := 4983230072969 + 3 ^ 40 * 1391745 * 2
def baseEnd_1391745 : Nat := 105871723480261114812887

theorem tailTrace_1391745 : CollatzResearch.WordTrace tailWord_1391745 prefixEnd_1391745 105871723480261114812887 := by
  unfold tailWord_1391745
  simp only [CollatzResearch.WordTrace]
  refine ⟨50761110342953030967552689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33840740228635353978368459 50761110342953030967552689)
  ·
    refine ⟨38070832757214773225664517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50761110342953030967552689 38070832757214773225664517)
    ·
      refine ⟨7138281141977769979812097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38070832757214773225664517 7138281141977769979812097)
      ·
        refine ⟨5353710856483327484859073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7138281141977769979812097 5353710856483327484859073)
        ·
          refine ⟨4015283142362495613644305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5353710856483327484859073 4015283142362495613644305)
          ·
            refine ⟨3011462356771871710233229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4015283142362495613644305 3011462356771871710233229)
            ·
              refine ⟨1129298383789451891337461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3011462356771871710233229 1129298383789451891337461)
              ·
                refine ⟨105871723480261114812887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1129298383789451891337461 105871723480261114812887)
                ·
                  rfl

theorem cell21_1391745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 5].length) (baseStart_1391745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391745 prefixEnd_1391745 := by exact prefixLift 1391745
  have htrace : WordTrace (prefixWord ++ tailWord_1391745) baseStart_1391745 baseEnd_1391745 := by
    simpa [prefixWord, tailWord_1391745, baseEnd_1391745] using wordTrace_append hprefix tailTrace_1391745
  have hstable : (prefixWord ++ tailWord_1391745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391745).length < 2 ^ (prefixWord ++ tailWord_1391745).sum := by decide
  have hdescent : baseEnd_1391745 < baseStart_1391745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391773 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 6]
def baseStart_1391773 : Nat := 118140960795 + 1391773 * 2 ^ 59
def prefixEnd_1391773 : Nat := 4983230072969 + 3 ^ 40 * 1391773 * 2
def baseEnd_1391773 : Nat := 317621560422261517971937

theorem tailTrace_1391773 : CollatzResearch.WordTrace tailWord_1391773 prefixEnd_1391773 317621560422261517971937 := by
  unfold tailWord_1391773
  simp only [CollatzResearch.WordTrace]
  refine ⟨50762131586851591749571973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33841421057901061166381315 50762131586851591749571973)
  ·
    refine ⟨9517899672534673453044745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50762131586851591749571973 9517899672534673453044745)
    ·
      refine ⟨7138424754401005089783559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9517899672534673453044745 7138424754401005089783559)
      ·
        refine ⟨10707637131601507634675339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7138424754401005089783559 10707637131601507634675339)
        ·
          refine ⟨16061455697402261452013009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10707637131601507634675339 16061455697402261452013009)
          ·
            refine ⟨12046091773051696089009757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16061455697402261452013009 12046091773051696089009757)
            ·
              refine ⟨4517284414894386033378659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12046091773051696089009757 4517284414894386033378659)
              ·
                refine ⟨6775926622341579050067989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517284414894386033378659 6775926622341579050067989)
                ·
                  refine ⟨317621560422261517971937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6775926622341579050067989 317621560422261517971937)
                  ·
                    rfl

theorem cell21_1391773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_1391773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391773 prefixEnd_1391773 := by exact prefixLift 1391773
  have htrace : WordTrace (prefixWord ++ tailWord_1391773) baseStart_1391773 baseEnd_1391773 := by
    simpa [prefixWord, tailWord_1391773, baseEnd_1391773] using wordTrace_append hprefix tailTrace_1391773
  have hstable : (prefixWord ++ tailWord_1391773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391773).length < 2 ^ (prefixWord ++ tailWord_1391773).sum := by decide
  have hdescent : baseEnd_1391773 < baseStart_1391773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391804 : List Nat := [2, 2, 2, 3, 2, 2, 1, 7]
def baseStart_1391804 : Nat := 118140960795 + 1391804 * 2 ^ 59
def prefixEnd_1391804 : Nat := 4983230072969 + 3 ^ 40 * 1391804 * 2
def baseEnd_1391804 : Nat := 105876211681537450985069

theorem tailTrace_1391804 : CollatzResearch.WordTrace tailWord_1391804 prefixEnd_1391804 105876211681537450985069 := by
  unfold tailWord_1391804
  simp only [CollatzResearch.WordTrace]
  refine ⟨25381631124869642021975233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33842174833159522695966977 25381631124869642021975233)
  ·
    refine ⟨19036223343652231516481425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25381631124869642021975233 19036223343652231516481425)
    ·
      refine ⟨14277167507739173637361069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19036223343652231516481425 14277167507739173637361069)
      ·
        refine ⟨5353937815402190114010401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14277167507739173637361069 5353937815402190114010401)
        ·
          refine ⟨4015453361551642585507801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5353937815402190114010401 4015453361551642585507801)
          ·
            refine ⟨3011590021163731939130851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4015453361551642585507801 3011590021163731939130851)
            ·
              refine ⟨4517385031745597908696277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3011590021163731939130851 4517385031745597908696277)
              ·
                refine ⟨105876211681537450985069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4517385031745597908696277 105876211681537450985069)
                ·
                  rfl

theorem cell21_1391804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_1391804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391804 prefixEnd_1391804 := by exact prefixLift 1391804
  have htrace : WordTrace (prefixWord ++ tailWord_1391804) baseStart_1391804 baseEnd_1391804 := by
    simpa [prefixWord, tailWord_1391804, baseEnd_1391804] using wordTrace_append hprefix tailTrace_1391804
  have hstable : (prefixWord ++ tailWord_1391804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391804).length < 2 ^ (prefixWord ++ tailWord_1391804).sum := by decide
  have hdescent : baseEnd_1391804 < baseStart_1391804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391880 : List Nat := [2, 1, 3, 2, 5, 8]
def baseStart_1391880 : Nat := 118140960795 + 1391880 * 2 ^ 59
def prefixEnd_1391880 : Nat := 4983230072969 + 3 ^ 40 * 1391880 * 2
def baseEnd_1391880 : Nat := 11764665899261226284755

theorem tailTrace_1391880 : CollatzResearch.WordTrace tailWord_1391880 prefixEnd_1391880 11764665899261226284755 := by
  unfold tailWord_1391880
  simp only [CollatzResearch.WordTrace]
  refine ⟨25383017098731974511858547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33844022798309299349144729 25383017098731974511858547)
  ·
    refine ⟨38074525648097961767787821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25383017098731974511858547 38074525648097961767787821)
    ·
      refine ⟨14277947118036735662920433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38074525648097961767787821 14277947118036735662920433)
      ·
        refine ⟨10708460338527551747190325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14277947118036735662920433 10708460338527551747190325)
        ·
          refine ⟨1003918156736957976299093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10708460338527551747190325 1003918156736957976299093)
          ·
            refine ⟨11764665899261226284755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1003918156736957976299093 11764665899261226284755)
            ·
              rfl

theorem cell21_1391880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 8].length) (baseStart_1391880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391880 prefixEnd_1391880 := by exact prefixLift 1391880
  have htrace : WordTrace (prefixWord ++ tailWord_1391880) baseStart_1391880 baseEnd_1391880 := by
    simpa [prefixWord, tailWord_1391880, baseEnd_1391880] using wordTrace_append hprefix tailTrace_1391880
  have hstable : (prefixWord ++ tailWord_1391880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391880).length < 2 ^ (prefixWord ++ tailWord_1391880).sum := by decide
  have hdescent : baseEnd_1391880 < baseStart_1391880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391984 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_1391984 : Nat := 118140960795 + 1391984 * 2 ^ 59
def prefixEnd_1391984 : Nat := 4983230072969 + 3 ^ 40 * 1391984 * 2
def baseEnd_1391984 : Nat := 317669713496972039954839

theorem tailTrace_1391984 : CollatzResearch.WordTrace tailWord_1391984 prefixEnd_1391984 317669713496972039954839 := by
  unfold tailWord_1391984
  simp only [CollatzResearch.WordTrace]
  refine ⟨25384913694543587392751503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33846551592724783190335337 25384913694543587392751503)
  ·
    refine ⟨38077370541815381089127255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25384913694543587392751503 38077370541815381089127255)
    ·
      refine ⟨57116055812723071633690883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38077370541815381089127255 57116055812723071633690883)
      ·
        refine ⟨85674083719084607450536325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57116055812723071633690883 85674083719084607450536325)
        ·
          refine ⟨16063890697328363896975561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85674083719084607450536325 16063890697328363896975561)
          ·
            refine ⟨12047918022996272922731671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16063890697328363896975561 12047918022996272922731671)
            ·
              refine ⟨18071877034494409384097507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12047918022996272922731671 18071877034494409384097507)
              ·
                refine ⟨27107815551741614076146261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18071877034494409384097507 27107815551741614076146261)
                ·
                  refine ⟨317669713496972039954839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27107815551741614076146261 317669713496972039954839)
                  ·
                    rfl

theorem cell21_1391984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_1391984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1391984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1391984 prefixEnd_1391984 := by exact prefixLift 1391984
  have htrace : WordTrace (prefixWord ++ tailWord_1391984) baseStart_1391984 baseEnd_1391984 := by
    simpa [prefixWord, tailWord_1391984, baseEnd_1391984] using wordTrace_append hprefix tailTrace_1391984
  have hstable : (prefixWord ++ tailWord_1391984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391984).length < 2 ^ (prefixWord ++ tailWord_1391984).sum := by decide
  have hdescent : baseEnd_1391984 < baseStart_1391984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392122 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_1392122 : Nat := 118140960795 + 1392122 * 2 ^ 59
def prefixEnd_1392122 : Nat := 4983230072969 + 3 ^ 40 * 1392122 * 2
def baseEnd_1392122 : Nat := 317701206977114466654557

theorem tailTrace_1392122 : CollatzResearch.WordTrace tailWord_1392122 prefixEnd_1392122 317701206977114466654557 := by
  unfold tailWord_1392122
  simp only [CollatzResearch.WordTrace]
  refine ⟨12693715165646806088506655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33849907108391482902684413 12693715165646806088506655)
  ·
    refine ⟨19040572748470209132759983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12693715165646806088506655 19040572748470209132759983)
    ·
      refine ⟨28560859122705313699139975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19040572748470209132759983 28560859122705313699139975)
      ·
        refine ⟨42841288684057970548709963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28560859122705313699139975 42841288684057970548709963)
        ·
          refine ⟨64261933026086955823064945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42841288684057970548709963 64261933026086955823064945)
          ·
            refine ⟨48196449769565216867298709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64261933026086955823064945 48196449769565216867298709)
            ·
              refine ⟨2259208582948369540654627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48196449769565216867298709 2259208582948369540654627)
              ·
                refine ⟨3388812874422554310981941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259208582948369540654627 3388812874422554310981941)
                ·
                  refine ⟨317701206977114466654557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3388812874422554310981941 317701206977114466654557)
                  ·
                    rfl

theorem cell21_1392122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_1392122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392122 prefixEnd_1392122 := by exact prefixLift 1392122
  have htrace : WordTrace (prefixWord ++ tailWord_1392122) baseStart_1392122 baseEnd_1392122 := by
    simpa [prefixWord, tailWord_1392122, baseEnd_1392122] using wordTrace_append hprefix tailTrace_1392122
  have hstable : (prefixWord ++ tailWord_1392122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392122).length < 2 ^ (prefixWord ++ tailWord_1392122).sum := by decide
  have hdescent : baseEnd_1392122 < baseStart_1392122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392142 : List Nat := [4, 1, 1, 2, 5, 1, 2, 5]
def baseStart_1392142 : Nat := 118140960795 + 1392142 * 2 ^ 59
def prefixEnd_1392142 : Nat := 4983230072969 + 3 ^ 40 * 1392142 * 2
def baseEnd_1392142 : Nat := 105901923749866292107061

theorem tailTrace_1392142 : CollatzResearch.WordTrace tailWord_1392142 prefixEnd_1392142 105901923749866292107061 := by
  unfold tailWord_1392142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6346948765314345971219335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33850393415009845179836453 6346948765314345971219335)
  ·
    refine ⟨9520423147971518956829003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6346948765314345971219335 9520423147971518956829003)
    ·
      refine ⟨14280634721957278435243505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9520423147971518956829003 14280634721957278435243505)
      ·
        refine ⟨10710476041467958826432629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14280634721957278435243505 10710476041467958826432629)
        ·
          refine ⟨1004107128887621139978059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10710476041467958826432629 1004107128887621139978059)
          ·
            refine ⟨1506160693331431709967089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004107128887621139978059 1506160693331431709967089)
            ·
              refine ⟨1129620519998573782475317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1506160693331431709967089 1129620519998573782475317)
              ·
                refine ⟨105901923749866292107061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1129620519998573782475317 105901923749866292107061)
                ·
                  rfl

theorem cell21_1392142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_1392142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392142 prefixEnd_1392142 := by exact prefixLift 1392142
  have htrace : WordTrace (prefixWord ++ tailWord_1392142) baseStart_1392142 baseEnd_1392142 := by
    simpa [prefixWord, tailWord_1392142, baseEnd_1392142] using wordTrace_append hprefix tailTrace_1392142
  have hstable : (prefixWord ++ tailWord_1392142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392142).length < 2 ^ (prefixWord ++ tailWord_1392142).sum := by decide
  have hdescent : baseEnd_1392142 < baseStart_1392142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392229 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 4]
def baseStart_1392229 : Nat := 118140960795 + 1392229 * 2 ^ 59
def prefixEnd_1392229 : Nat := 4983230072969 + 3 ^ 40 * 1392229 * 2
def baseEnd_1392229 : Nat := 317725625834906058371005

theorem tailTrace_1392229 : CollatzResearch.WordTrace tailWord_1392229 prefixEnd_1392229 317725625834906058371005 := by
  unfold tailWord_1392229
  simp only [CollatzResearch.WordTrace]
  refine ⟨50778763273199581628171741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33852508848799721085447827 50778763273199581628171741)
  ·
    refine ⟨19042036227449843110564403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50778763273199581628171741 19042036227449843110564403)
    ·
      refine ⟨28563054341174764665846605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19042036227449843110564403 28563054341174764665846605)
      ·
        refine ⟨10711145377940536749692477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28563054341174764665846605 10711145377940536749692477)
        ·
          refine ⟨4016679516727701281134679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10711145377940536749692477 4016679516727701281134679)
          ·
            refine ⟨6025019275091551921702019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016679516727701281134679 6025019275091551921702019)
            ·
              refine ⟨9037528912637327882553029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6025019275091551921702019 9037528912637327882553029)
              ·
                refine ⟨1694536671119498977978693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9037528912637327882553029 1694536671119498977978693)
                ·
                  refine ⟨317725625834906058371005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1694536671119498977978693 317725625834906058371005)
                  ·
                    rfl

theorem cell21_1392229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_1392229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392229 prefixEnd_1392229 := by exact prefixLift 1392229
  have htrace : WordTrace (prefixWord ++ tailWord_1392229) baseStart_1392229 baseEnd_1392229 := by
    simpa [prefixWord, tailWord_1392229, baseEnd_1392229] using wordTrace_append hprefix tailTrace_1392229
  have hstable : (prefixWord ++ tailWord_1392229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392229).length < 2 ^ (prefixWord ++ tailWord_1392229).sum := by decide
  have hdescent : baseEnd_1392229 < baseStart_1392229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392232 : List Nat := [2, 1, 4, 3, 1, 2, 1, 4, 3]
def baseStart_1392232 : Nat := 118140960795 + 1392232 * 2 ^ 59
def prefixEnd_1392232 : Nat := 4983230072969 + 3 ^ 40 * 1392232 * 2
def baseEnd_1392232 : Nat := 317726310475778719820999

theorem tailTrace_1392232 : CollatzResearch.WordTrace tailWord_1392232 prefixEnd_1392232 317726310475778719820999 := by
  unfold tailWord_1392232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25389436346094356570265475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33852581794792475427020633 25389436346094356570265475)
  ·
    refine ⟨38084154519141534855398213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25389436346094356570265475 38084154519141534855398213)
    ·
      refine ⟨7140778972339037785387165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38084154519141534855398213 7140778972339037785387165)
      ·
        refine ⟨2677792114627139169520187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7140778972339037785387165 2677792114627139169520187)
        ·
          refine ⟨4016688171940708754280281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677792114627139169520187 4016688171940708754280281)
          ·
            refine ⟨3012516128955531565710211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4016688171940708754280281 3012516128955531565710211)
            ·
              refine ⟨4518774193433297348565317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012516128955531565710211 4518774193433297348565317)
              ·
                refine ⟨847270161268743252855997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4518774193433297348565317 847270161268743252855997)
                ·
                  refine ⟨317726310475778719820999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 847270161268743252855997 317726310475778719820999)
                  ·
                    rfl

theorem cell21_1392232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 3].length) (baseStart_1392232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392232 prefixEnd_1392232 := by exact prefixLift 1392232
  have htrace : WordTrace (prefixWord ++ tailWord_1392232) baseStart_1392232 baseEnd_1392232 := by
    simpa [prefixWord, tailWord_1392232, baseEnd_1392232] using wordTrace_append hprefix tailTrace_1392232
  have hstable : (prefixWord ++ tailWord_1392232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392232).length < 2 ^ (prefixWord ++ tailWord_1392232).sum := by decide
  have hdescent : baseEnd_1392232 < baseStart_1392232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392246 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1392246 : Nat := 118140960795 + 1392246 * 2 ^ 59
def prefixEnd_1392246 : Nat := 4983230072969 + 3 ^ 40 * 1392246 * 2
def baseEnd_1392246 : Nat := 317729505466517806587637

theorem tailTrace_1392246 : CollatzResearch.WordTrace tailWord_1392246 prefixEnd_1392246 317729505466517806587637 := by
  unfold tailWord_1392246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173711457133624595721287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33852922209425329021027061 3173711457133624595721287)
  ·
    refine ⟨4760567185700436893581931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3173711457133624595721287 4760567185700436893581931)
    ·
      refine ⟨7140850778550655340372897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4760567185700436893581931 7140850778550655340372897)
      ·
        refine ⟨5355638083912991505279673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7140850778550655340372897 5355638083912991505279673)
        ·
          refine ⟨4016728562934743628959755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5355638083912991505279673 4016728562934743628959755)
          ·
            refine ⟨6025092844402115443439633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016728562934743628959755 6025092844402115443439633)
            ·
              refine ⟨4518819633301586582579725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6025092844402115443439633 4518819633301586582579725)
              ·
                refine ⟨1694557362488094968467397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4518819633301586582579725 1694557362488094968467397)
                ·
                  refine ⟨317729505466517806587637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1694557362488094968467397 317729505466517806587637)
                  ·
                    rfl

theorem cell21_1392246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1392246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392246 prefixEnd_1392246 := by exact prefixLift 1392246
  have htrace : WordTrace (prefixWord ++ tailWord_1392246) baseStart_1392246 baseEnd_1392246 := by
    simpa [prefixWord, tailWord_1392246, baseEnd_1392246] using wordTrace_append hprefix tailTrace_1392246
  have hstable : (prefixWord ++ tailWord_1392246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392246).length < 2 ^ (prefixWord ++ tailWord_1392246).sum := by decide
  have hdescent : baseEnd_1392246 < baseStart_1392246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392342 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1392342 : Nat := 118140960795 + 1392342 * 2 ^ 59
def prefixEnd_1392342 : Nat := 4983230072969 + 3 ^ 40 * 1392342 * 2
def baseEnd_1392342 : Nat := 317751413974442972987441

theorem tailTrace_1392342 : CollatzResearch.WordTrace tailWord_1392342 prefixEnd_1392342 317751413974442972987441 := by
  unfold tailWord_1392342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173930295111887620439705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33855256481193467951356853 3173930295111887620439705)
  ·
    refine ⟨2380447721333915715329779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3173930295111887620439705 2380447721333915715329779)
    ·
      refine ⟨3570671582000873572994669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2380447721333915715329779 3570671582000873572994669)
      ·
        refine ⟨1339001843250327589873001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3570671582000873572994669 1339001843250327589873001)
        ·
          refine ⟨1004251382437745692404751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1339001843250327589873001 1004251382437745692404751)
          ·
            refine ⟨1506377073656618538607127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004251382437745692404751 1506377073656618538607127)
            ·
              refine ⟨2259565610484927807910691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506377073656618538607127 2259565610484927807910691)
              ·
                refine ⟨3389348415727391711866037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259565610484927807910691 3389348415727391711866037)
                ·
                  refine ⟨317751413974442972987441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3389348415727391711866037 317751413974442972987441)
                  ·
                    rfl

theorem cell21_1392342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1392342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392342 prefixEnd_1392342 := by exact prefixLift 1392342
  have htrace : WordTrace (prefixWord ++ tailWord_1392342) baseStart_1392342 baseEnd_1392342 := by
    simpa [prefixWord, tailWord_1392342, baseEnd_1392342] using wordTrace_append hprefix tailTrace_1392342
  have hstable : (prefixWord ++ tailWord_1392342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392342).length < 2 ^ (prefixWord ++ tailWord_1392342).sum := by decide
  have hdescent : baseEnd_1392342 < baseStart_1392342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392390 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1392390 : Nat := 118140960795 + 1392390 * 2 ^ 59
def prefixEnd_1392390 : Nat := 4983230072969 + 3 ^ 40 * 1392390 * 2
def baseEnd_1392390 : Nat := 317762368228405556187343

theorem tailTrace_1392390 : CollatzResearch.WordTrace tailWord_1392390 prefixEnd_1392390 317762368228405556187343 := by
  unfold tailWord_1392390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587019857050509566399457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33856423617077537416521749 1587019857050509566399457)
  ·
    refine ⟨1190264892787882174799593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1587019857050509566399457 1190264892787882174799593)
    ·
      refine ⟨892698669590911631099695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1190264892787882174799593 892698669590911631099695)
      ·
        refine ⟨1339048004386367446649543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892698669590911631099695 1339048004386367446649543)
        ·
          refine ⟨2008572006579551169974315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339048004386367446649543 2008572006579551169974315)
          ·
            refine ⟨3012858009869326754961473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008572006579551169974315 3012858009869326754961473)
            ·
              refine ⟨2259643507401995066221105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3012858009869326754961473 2259643507401995066221105)
              ·
                refine ⟨1694732630551496299665829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259643507401995066221105 1694732630551496299665829)
                ·
                  refine ⟨317762368228405556187343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1694732630551496299665829 317762368228405556187343)
                  ·
                    rfl

theorem cell21_1392390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1392390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392390 prefixEnd_1392390 := by exact prefixLift 1392390
  have htrace : WordTrace (prefixWord ++ tailWord_1392390) baseStart_1392390 baseEnd_1392390 := by
    simpa [prefixWord, tailWord_1392390, baseEnd_1392390] using wordTrace_append hprefix tailTrace_1392390
  have hstable : (prefixWord ++ tailWord_1392390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392390).length < 2 ^ (prefixWord ++ tailWord_1392390).sum := by decide
  have hdescent : baseEnd_1392390 < baseStart_1392390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392516 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1392516 : Nat := 118140960795 + 1392516 * 2 ^ 59
def prefixEnd_1392516 : Nat := 4983230072969 + 3 ^ 40 * 1392516 * 2
def baseEnd_1392516 : Nat := 317791123145057337087085

theorem tailTrace_1392516 : CollatzResearch.WordTrace tailWord_1392516 prefixEnd_1392516 317791123145057337087085 := by
  unfold tailWord_1392516
  simp only [CollatzResearch.WordTrace]
  refine ⟨25394615511579914821934701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33859487348773219762579601 25394615511579914821934701)
  ·
    refine ⟨9522980816842468058225513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25394615511579914821934701 9522980816842468058225513)
    ·
      refine ⟨7142235612631851043669135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9522980816842468058225513 7142235612631851043669135)
      ·
        refine ⟨10713353418947776565503703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7142235612631851043669135 10713353418947776565503703)
        ·
          refine ⟨16070030128421664848255555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10713353418947776565503703 16070030128421664848255555)
          ·
            refine ⟨24105045192632497272383333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16070030128421664848255555 24105045192632497272383333)
            ·
              refine ⟨4519695973618593238571875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24105045192632497272383333 4519695973618593238571875)
              ·
                refine ⟨6779543960427889857857813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4519695973618593238571875 6779543960427889857857813)
                ·
                  refine ⟨317791123145057337087085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6779543960427889857857813 317791123145057337087085)
                  ·
                    rfl

theorem cell21_1392516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1392516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392516 prefixEnd_1392516 := by exact prefixLift 1392516
  have htrace : WordTrace (prefixWord ++ tailWord_1392516) baseStart_1392516 baseEnd_1392516 := by
    simpa [prefixWord, tailWord_1392516, baseEnd_1392516] using wordTrace_append hprefix tailTrace_1392516
  have hstable : (prefixWord ++ tailWord_1392516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392516).length < 2 ^ (prefixWord ++ tailWord_1392516).sum := by decide
  have hdescent : baseEnd_1392516 < baseStart_1392516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392519 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 5]
def baseStart_1392519 : Nat := 118140960795 + 1392519 * 2 ^ 59
def prefixEnd_1392519 : Nat := 4983230072969 + 3 ^ 40 * 1392519 * 2
def baseEnd_1392519 : Nat := 317791807785929998537079

theorem tailTrace_1392519 : CollatzResearch.WordTrace tailWord_1392519 prefixEnd_1392519 317791807785929998537079 := by
  unfold tailWord_1392519
  simp only [CollatzResearch.WordTrace]
  refine ⟨50789340442148961156228611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33859560294765974104152407 50789340442148961156228611)
  ·
    refine ⟨76184010663223441734342917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50789340442148961156228611 76184010663223441734342917)
    ·
      refine ⟨14284501999354395325189297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76184010663223441734342917 14284501999354395325189297)
      ·
        refine ⟨10713376499515796493891973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14284501999354395325189297 10713376499515796493891973)
        ·
          refine ⟨2008758093659211842604745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10713376499515796493891973 2008758093659211842604745)
          ·
            refine ⟨1506568570244408881953559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2008758093659211842604745 1506568570244408881953559)
            ·
              refine ⟨2259852855366613322930339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506568570244408881953559 2259852855366613322930339)
              ·
                refine ⟨3389779283049919984395509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259852855366613322930339 3389779283049919984395509)
                ·
                  refine ⟨317791807785929998537079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3389779283049919984395509 317791807785929998537079)
                  ·
                    rfl

theorem cell21_1392519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 5].length) (baseStart_1392519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392519 prefixEnd_1392519 := by exact prefixLift 1392519
  have htrace : WordTrace (prefixWord ++ tailWord_1392519) baseStart_1392519 baseEnd_1392519 := by
    simpa [prefixWord, tailWord_1392519, baseEnd_1392519] using wordTrace_append hprefix tailTrace_1392519
  have hstable : (prefixWord ++ tailWord_1392519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392519).length < 2 ^ (prefixWord ++ tailWord_1392519).sum := by decide
  have hdescent : baseEnd_1392519 < baseStart_1392519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392564 : List Nat := [2, 5, 2, 1, 2, 9]
def baseStart_1392564 : Nat := 118140960795 + 1392564 * 2 ^ 59
def prefixEnd_1392564 : Nat := 4983230072969 + 3 ^ 40 * 1392564 * 2
def baseEnd_1392564 : Nat := 11770447311074811862481

theorem tailTrace_1392564 : CollatzResearch.WordTrace tailWord_1392564 prefixEnd_1392564 11770447311074811862481 := by
  unfold tailWord_1392564
  simp only [CollatzResearch.WordTrace]
  refine ⟨25395490863492966920808373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33860654484657289227744497 25395490863492966920808373)
  ·
    refine ⟨2380827268452465648825785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25395490863492966920808373 2380827268452465648825785)
    ·
      refine ⟨1785620451339349236619339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2380827268452465648825785 1785620451339349236619339)
      ·
        refine ⟨2678430677009023854929009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785620451339349236619339 2678430677009023854929009)
        ·
          refine ⟨2008823007756767891196757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2678430677009023854929009 2008823007756767891196757)
          ·
            refine ⟨11770447311074811862481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2008823007756767891196757 11770447311074811862481)
            ·
              rfl

theorem cell21_1392564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 9].length) (baseStart_1392564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392564 prefixEnd_1392564 := by exact prefixLift 1392564
  have htrace : WordTrace (prefixWord ++ tailWord_1392564) baseStart_1392564 baseEnd_1392564 := by
    simpa [prefixWord, tailWord_1392564, baseEnd_1392564] using wordTrace_append hprefix tailTrace_1392564
  have hstable : (prefixWord ++ tailWord_1392564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392564).length < 2 ^ (prefixWord ++ tailWord_1392564).sum := by decide
  have hdescent : baseEnd_1392564 < baseStart_1392564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392592 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_1392592 : Nat := 118140960795 + 1392592 * 2 ^ 59
def prefixEnd_1392592 : Nat := 4983230072969 + 3 ^ 40 * 1392592 * 2
def baseEnd_1392592 : Nat := 317808467380498093820263

theorem tailTrace_1392592 : CollatzResearch.WordTrace tailWord_1392592 prefixEnd_1392592 317808467380498093820263 := by
  unfold tailWord_1392592
  simp only [CollatzResearch.WordTrace]
  refine ⟨25396001485442247311818015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33861335313922996415757353 25396001485442247311818015)
  ·
    refine ⟨38094002228163370967727023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25396001485442247311818015 38094002228163370967727023)
    ·
      refine ⟨57141003342245056451590535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38094002228163370967727023 57141003342245056451590535)
      ·
        refine ⟨85711505013367584677385803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57141003342245056451590535 85711505013367584677385803)
        ·
          refine ⟨128567257520051377016078705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85711505013367584677385803 128567257520051377016078705)
          ·
            refine ⟨96425443140038532762059029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128567257520051377016078705 96425443140038532762059029)
            ·
              refine ⟨4519942647189306223221517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96425443140038532762059029 4519942647189306223221517)
              ·
                refine ⟨1694978492695989833708069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4519942647189306223221517 1694978492695989833708069)
                ·
                  refine ⟨317808467380498093820263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1694978492695989833708069 317808467380498093820263)
                  ·
                    rfl

theorem cell21_1392592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_1392592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392592 prefixEnd_1392592 := by exact prefixLift 1392592
  have htrace : WordTrace (prefixWord ++ tailWord_1392592) baseStart_1392592 baseEnd_1392592 := by
    simpa [prefixWord, tailWord_1392592, baseEnd_1392592] using wordTrace_append hprefix tailTrace_1392592
  have hstable : (prefixWord ++ tailWord_1392592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392592).length < 2 ^ (prefixWord ++ tailWord_1392592).sum := by decide
  have hdescent : baseEnd_1392592 < baseStart_1392592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392637 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 5]
def baseStart_1392637 : Nat := 118140960795 + 1392637 * 2 ^ 59
def prefixEnd_1392637 : Nat := 4983230072969 + 3 ^ 40 * 1392637 * 2
def baseEnd_1392637 : Nat := 317818736993588015570171

theorem tailTrace_1392637 : CollatzResearch.WordTrace tailWord_1392637 prefixEnd_1392637 317818736993588015570171 := by
  unfold tailWord_1392637
  simp only [CollatzResearch.WordTrace]
  refine ⟨50793644255721467309024165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33862429503814311539349443 50793644255721467309024165)
  ·
    refine ⟨9523808297947775120442031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50793644255721467309024165 9523808297947775120442031)
    ·
      refine ⟨14285712446921662680663047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9523808297947775120442031 14285712446921662680663047)
      ·
        refine ⟨21428568670382494020994571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14285712446921662680663047 21428568670382494020994571)
        ·
          refine ⟨32142853005573741031491857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21428568670382494020994571 32142853005573741031491857)
          ·
            refine ⟨24107139754180305773618893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32142853005573741031491857 24107139754180305773618893)
            ·
              refine ⟨9040177407817614665107085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24107139754180305773618893 9040177407817614665107085)
              ·
                refine ⟨3390066527931605499415157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9040177407817614665107085 3390066527931605499415157)
                ·
                  refine ⟨317818736993588015570171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3390066527931605499415157 317818736993588015570171)
                  ·
                    rfl

theorem cell21_1392637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_1392637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392637 prefixEnd_1392637 := by exact prefixLift 1392637
  have htrace : WordTrace (prefixWord ++ tailWord_1392637) baseStart_1392637 baseEnd_1392637 := by
    simpa [prefixWord, tailWord_1392637, baseEnd_1392637] using wordTrace_append hprefix tailTrace_1392637
  have hstable : (prefixWord ++ tailWord_1392637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392637).length < 2 ^ (prefixWord ++ tailWord_1392637).sum := by decide
  have hdescent : baseEnd_1392637 < baseStart_1392637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392668 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_1392668 : Nat := 118140960795 + 1392668 * 2 ^ 59
def prefixEnd_1392668 : Nat := 4983230072969 + 3 ^ 40 * 1392668 * 2
def baseEnd_1392668 : Nat := 317825811615938850553441

theorem tailTrace_1392668 : CollatzResearch.WordTrace tailWord_1392668 prefixEnd_1392668 317825811615938850553441 := by
  unfold tailWord_1392668
  simp only [CollatzResearch.WordTrace]
  refine ⟨25397387459304579801701329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33863183279072773068935105 25397387459304579801701329)
  ·
    refine ⟨19048040594478434851275997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25397387459304579801701329 19048040594478434851275997)
    ·
      refine ⟨7143015222929413069228499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19048040594478434851275997 7143015222929413069228499)
      ·
        refine ⟨10714522834394119603842749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7143015222929413069228499 10714522834394119603842749)
        ·
          refine ⟨4017946062897794851441031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10714522834394119603842749 4017946062897794851441031)
          ·
            refine ⟨6026919094346692277161547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4017946062897794851441031 6026919094346692277161547)
            ·
              refine ⟨9040378641520038415742321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6026919094346692277161547 9040378641520038415742321)
              ·
                refine ⟨6780283981140028811806741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9040378641520038415742321 6780283981140028811806741)
                ·
                  refine ⟨317825811615938850553441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6780283981140028811806741 317825811615938850553441)
                  ·
                    rfl

theorem cell21_1392668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_1392668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392668 prefixEnd_1392668 := by exact prefixLift 1392668
  have htrace : WordTrace (prefixWord ++ tailWord_1392668) baseStart_1392668 baseEnd_1392668 := by
    simpa [prefixWord, tailWord_1392668, baseEnd_1392668] using wordTrace_append hprefix tailTrace_1392668
  have hstable : (prefixWord ++ tailWord_1392668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392668).length < 2 ^ (prefixWord ++ tailWord_1392668).sum := by decide
  have hdescent : baseEnd_1392668 < baseStart_1392668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392702 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1392702 : Nat := 118140960795 + 1392702 * 2 ^ 59
def prefixEnd_1392702 : Nat := 4983230072969 + 3 ^ 40 * 1392702 * 2
def baseEnd_1392702 : Nat := 317833570879162346986705

theorem tailTrace_1392702 : CollatzResearch.WordTrace tailWord_1392702 prefixEnd_1392702 317833570879162346986705 := by
  unfold tailWord_1392702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349501875060747926267545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33864010000323988940093573 6349501875060747926267545)
  ·
    refine ⟨4762126406295560944700659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6349501875060747926267545 4762126406295560944700659)
    ·
      refine ⟨7143189609443341417050989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4762126406295560944700659 7143189609443341417050989)
      ·
        refine ⟨2678696103541253031394121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7143189609443341417050989 2678696103541253031394121)
        ·
          refine ⟨2009022077655939773545591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2678696103541253031394121 2009022077655939773545591)
          ·
            refine ⟨3013533116483909660318387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009022077655939773545591 3013533116483909660318387)
            ·
              refine ⟨4520299674725864490477581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013533116483909660318387 4520299674725864490477581)
              ·
                refine ⟨1695112378022199183929093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4520299674725864490477581 1695112378022199183929093)
                ·
                  refine ⟨317833570879162346986705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1695112378022199183929093 317833570879162346986705)
                  ·
                    rfl

theorem cell21_1392702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1392702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392702 prefixEnd_1392702 := by exact prefixLift 1392702
  have htrace : WordTrace (prefixWord ++ tailWord_1392702) baseStart_1392702 baseEnd_1392702 := by
    simpa [prefixWord, tailWord_1392702, baseEnd_1392702] using wordTrace_append hprefix tailTrace_1392702
  have hstable : (prefixWord ++ tailWord_1392702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392702).length < 2 ^ (prefixWord ++ tailWord_1392702).sum := by decide
  have hdescent : baseEnd_1392702 < baseStart_1392702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392727 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 8]
def baseStart_1392727 : Nat := 118140960795 + 1392727 * 2 ^ 59
def prefixEnd_1392727 : Nat := 4983230072969 + 3 ^ 40 * 1392727 * 2
def baseEnd_1392727 : Nat := 317839276219767859069987

theorem tailTrace_1392727 : CollatzResearch.WordTrace tailWord_1392727 prefixEnd_1392727 317839276219767859069987 := by
  unfold tailWord_1392727
  simp only [CollatzResearch.WordTrace]
  refine ⟨50796926825395412679800435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33864617883596941786533623 50796926825395412679800435)
  ·
    refine ⟨76195390238093119019700653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50796926825395412679800435 76195390238093119019700653)
    ·
      refine ⟨28573271339284919632387745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76195390238093119019700653 28573271339284919632387745)
      ·
        refine ⟨21429953504463689724290809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28573271339284919632387745 21429953504463689724290809)
        ·
          refine ⟨16072465128347767293218107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21429953504463689724290809 16072465128347767293218107)
          ·
            refine ⟨24108697692521650939827161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16072465128347767293218107 24108697692521650939827161)
            ·
              refine ⟨18081523269391238204870371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24108697692521650939827161 18081523269391238204870371)
              ·
                refine ⟨27122284904086857307305557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18081523269391238204870371 27122284904086857307305557)
                ·
                  refine ⟨317839276219767859069987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27122284904086857307305557 317839276219767859069987)
                  ·
                    rfl

theorem cell21_1392727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_1392727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392727 prefixEnd_1392727 := by exact prefixLift 1392727
  have htrace : WordTrace (prefixWord ++ tailWord_1392727) baseStart_1392727 baseEnd_1392727 := by
    simpa [prefixWord, tailWord_1392727, baseEnd_1392727] using wordTrace_append hprefix tailTrace_1392727
  have hstable : (prefixWord ++ tailWord_1392727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392727).length < 2 ^ (prefixWord ++ tailWord_1392727).sum := by decide
  have hdescent : baseEnd_1392727 < baseStart_1392727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392730 : List Nat := [3, 1, 1, 2, 1, 1, 4, 5, 3]
def baseStart_1392730 : Nat := 118140960795 + 1392730 * 2 ^ 59
def prefixEnd_1392730 : Nat := 4983230072969 + 3 ^ 40 * 1392730 * 2
def baseEnd_1392730 : Nat := 317839960860640520519981

theorem tailTrace_1392730 : CollatzResearch.WordTrace tailWord_1392730 prefixEnd_1392730 317839960860640520519981 := by
  unfold tailWord_1392730
  simp only [CollatzResearch.WordTrace]
  refine ⟨12699259061096136048039911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33864690829589696128106429 12699259061096136048039911)
  ·
    refine ⟨19048888591644204072059867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12699259061096136048039911 19048888591644204072059867)
    ·
      refine ⟨28573332887466306108089801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19048888591644204072059867 28573332887466306108089801)
      ·
        refine ⟨21429999665599729581067351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28573332887466306108089801 21429999665599729581067351)
        ·
          refine ⟨32144999498399594371601027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21429999665599729581067351 32144999498399594371601027)
          ·
            refine ⟨48217499247599391557401541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32144999498399594371601027 48217499247599391557401541)
            ·
              refine ⟨9040781108924885917012789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48217499247599391557401541 9040781108924885917012789)
              ·
                refine ⟨847573228961708054719949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9040781108924885917012789 847573228961708054719949)
                ·
                  refine ⟨317839960860640520519981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 847573228961708054719949 317839960860640520519981)
                  ·
                    rfl

theorem cell21_1392730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_1392730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392730 prefixEnd_1392730 := by exact prefixLift 1392730
  have htrace : WordTrace (prefixWord ++ tailWord_1392730) baseStart_1392730 baseEnd_1392730 := by
    simpa [prefixWord, tailWord_1392730, baseEnd_1392730] using wordTrace_append hprefix tailTrace_1392730
  have hstable : (prefixWord ++ tailWord_1392730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392730).length < 2 ^ (prefixWord ++ tailWord_1392730).sum := by decide
  have hdescent : baseEnd_1392730 < baseStart_1392730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392927 : List Nat := [1, 1, 2, 4, 3, 3, 1, 6]
def baseStart_1392927 : Nat := 118140960795 + 1392927 * 2 ^ 59
def prefixEnd_1392927 : Nat := 4983230072969 + 3 ^ 40 * 1392927 * 2
def baseEnd_1392927 : Nat := 105961639648203985245415

theorem tailTrace_1392927 : CollatzResearch.WordTrace tailWord_1392927 prefixEnd_1392927 105961639648203985245415 := by
  unfold tailWord_1392927
  simp only [CollatzResearch.WordTrace]
  refine ⟨50804221424670846837081035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33869480949780564558054023 50804221424670846837081035)
  ·
    refine ⟨76206332137006270255621553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50804221424670846837081035 76206332137006270255621553)
    ·
      refine ⟨57154749102754702691716165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76206332137006270255621553 57154749102754702691716165)
      ·
        refine ⟨10716515456766506754696781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57154749102754702691716165 10716515456766506754696781)
        ·
          refine ⟨4018693296287440033011293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10716515456766506754696781 4018693296287440033011293)
          ·
            refine ⟨1507009986107790012379235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4018693296287440033011293 1507009986107790012379235)
            ·
              refine ⟨2260514979161685018568853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507009986107790012379235 2260514979161685018568853)
              ·
                refine ⟨105961639648203985245415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2260514979161685018568853 105961639648203985245415)
                ·
                  rfl

theorem cell21_1392927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 6].length) (baseStart_1392927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1392927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1392927 prefixEnd_1392927 := by exact prefixLift 1392927
  have htrace : WordTrace (prefixWord ++ tailWord_1392927) baseStart_1392927 baseEnd_1392927 := by
    simpa [prefixWord, tailWord_1392927, baseEnd_1392927] using wordTrace_append hprefix tailTrace_1392927
  have hstable : (prefixWord ++ tailWord_1392927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392927).length < 2 ^ (prefixWord ++ tailWord_1392927).sum := by decide
  have hdescent : baseEnd_1392927 < baseStart_1392927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393031 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 6]
def baseStart_1393031 : Nat := 118140960795 + 1393031 * 2 ^ 59
def prefixEnd_1393031 : Nat := 4983230072969 + 3 ^ 40 * 1393031 * 2
def baseEnd_1393031 : Nat := 317908653161530886002699

theorem tailTrace_1393031 : CollatzResearch.WordTrace tailWord_1393031 prefixEnd_1393031 317908653161530886002699 := by
  unfold tailWord_1393031
  simp only [CollatzResearch.WordTrace]
  refine ⟨50808014616294072598866947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33872009744196048399244631 50808014616294072598866947)
  ·
    refine ⟨76212021924441108898300421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50808014616294072598866947 76212021924441108898300421)
    ·
      refine ⟨14289754110832707918431329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76212021924441108898300421 14289754110832707918431329)
      ·
        refine ⟨10717315583124530938823497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14289754110832707918431329 10717315583124530938823497)
        ·
          refine ⟨8037986687343398204117623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10717315583124530938823497 8037986687343398204117623)
          ·
            refine ⟨12056980031015097306176435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8037986687343398204117623 12056980031015097306176435)
            ·
              refine ⟨18085470046522645959264653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12056980031015097306176435 18085470046522645959264653)
              ·
                refine ⟨6782051267445992234724245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18085470046522645959264653 6782051267445992234724245)
                ·
                  refine ⟨317908653161530886002699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6782051267445992234724245 317908653161530886002699)
                  ·
                    rfl

theorem cell21_1393031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_1393031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393031 prefixEnd_1393031 := by exact prefixLift 1393031
  have htrace : WordTrace (prefixWord ++ tailWord_1393031) baseStart_1393031 baseEnd_1393031 := by
    simpa [prefixWord, tailWord_1393031, baseEnd_1393031] using wordTrace_append hprefix tailTrace_1393031
  have hstable : (prefixWord ++ tailWord_1393031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393031).length < 2 ^ (prefixWord ++ tailWord_1393031).sum := by decide
  have hdescent : baseEnd_1393031 < baseStart_1393031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393110 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1393110 : Nat := 118140960795 + 1393110 * 2 ^ 59
def prefixEnd_1393110 : Nat := 4983230072969 + 3 ^ 40 * 1393110 * 2
def baseEnd_1393110 : Nat := 317926682037844304185871

theorem tailTrace_1393110 : CollatzResearch.WordTrace tailWord_1393110 prefixEnd_1393110 317926682037844304185871 := by
  unfold tailWord_1393110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175680998937991818187049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33873930655338579393995189 3175680998937991818187049)
  ·
    refine ⟨2381760749203493863640287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3175680998937991818187049 2381760749203493863640287)
    ·
      refine ⟨3572641123805240795460431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381760749203493863640287 3572641123805240795460431)
      ·
        refine ⟨5358961685707861193190647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572641123805240795460431 5358961685707861193190647)
        ·
          refine ⟨8038442528561791789785971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5358961685707861193190647 8038442528561791789785971)
          ·
            refine ⟨12057663792842687684678957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8038442528561791789785971 12057663792842687684678957)
            ·
              refine ⟨4521623922316007881754609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12057663792842687684678957 4521623922316007881754609)
              ·
                refine ⟨3391217941737005911315957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4521623922316007881754609 3391217941737005911315957)
                ·
                  refine ⟨317926682037844304185871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3391217941737005911315957 317926682037844304185871)
                  ·
                    rfl

theorem cell21_1393110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1393110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393110 prefixEnd_1393110 := by exact prefixLift 1393110
  have htrace : WordTrace (prefixWord ++ tailWord_1393110) baseStart_1393110 baseEnd_1393110 := by
    simpa [prefixWord, tailWord_1393110, baseEnd_1393110] using wordTrace_append hprefix tailTrace_1393110
  have hstable : (prefixWord ++ tailWord_1393110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393110).length < 2 ^ (prefixWord ++ tailWord_1393110).sum := by decide
  have hdescent : baseEnd_1393110 < baseStart_1393110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393141 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 6]
def baseStart_1393141 : Nat := 118140960795 + 1393141 * 2 ^ 59
def prefixEnd_1393141 : Nat := 4983230072969 + 3 ^ 40 * 1393141 * 2
def baseEnd_1393141 : Nat := 317933756660195139169141

theorem tailTrace_1393141 : CollatzResearch.WordTrace tailWord_1393141 prefixEnd_1393141 317933756660195139169141 := by
  unfold tailWord_1393141
  simp only [CollatzResearch.WordTrace]
  refine ⟨50812026645895561385371277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33874684430597040923580851 50812026645895561385371277)
  ·
    refine ⟨19054509992210835519514229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50812026645895561385371277 19054509992210835519514229)
    ·
      refine ⟨1786360311769765829954459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19054509992210835519514229 1786360311769765829954459)
      ·
        refine ⟨2679540467654648744931689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786360311769765829954459 2679540467654648744931689)
        ·
          refine ⟨2009655350740986558698767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2679540467654648744931689 2009655350740986558698767)
          ·
            refine ⟨3014483026111479838048151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009655350740986558698767 3014483026111479838048151)
            ·
              refine ⟨4521724539167219757072227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014483026111479838048151 4521724539167219757072227)
              ·
                refine ⟨6782586808750829635608341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4521724539167219757072227 6782586808750829635608341)
                ·
                  refine ⟨317933756660195139169141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6782586808750829635608341 317933756660195139169141)
                  ·
                    rfl

theorem cell21_1393141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_1393141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393141 prefixEnd_1393141 := by exact prefixLift 1393141
  have htrace : WordTrace (prefixWord ++ tailWord_1393141) baseStart_1393141 baseEnd_1393141 := by
    simpa [prefixWord, tailWord_1393141, baseEnd_1393141] using wordTrace_append hprefix tailTrace_1393141
  have hstable : (prefixWord ++ tailWord_1393141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393141).length < 2 ^ (prefixWord ++ tailWord_1393141).sum := by decide
  have hdescent : baseEnd_1393141 < baseStart_1393141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393172 : List Nat := [2, 4, 3, 1, 1, 1, 4, 5]
def baseStart_1393172 : Nat := 118140960795 + 1393172 * 2 ^ 59
def prefixEnd_1393172 : Nat := 4983230072969 + 3 ^ 40 * 1393172 * 2
def baseEnd_1393172 : Nat := 105980277094181991384137

theorem tailTrace_1393172 : CollatzResearch.WordTrace tailWord_1393172 prefixEnd_1393172 105980277094181991384137 := by
  unfold tailWord_1393172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25406578654391626839874885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33875438205855502453166513 25406578654391626839874885)
  ·
    refine ⟨4763733497698430032476541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25406578654391626839874885 4763733497698430032476541)
    ·
      refine ⟨1786400061636911262178703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4763733497698430032476541 1786400061636911262178703)
      ·
        refine ⟨2679600092455366893268055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786400061636911262178703 2679600092455366893268055)
        ·
          refine ⟨4019400138683050339902083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2679600092455366893268055 4019400138683050339902083)
          ·
            refine ⟨6029100208024575509853125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019400138683050339902083 6029100208024575509853125)
            ·
              refine ⟨1130456289004607908097461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6029100208024575509853125 1130456289004607908097461)
              ·
                refine ⟨105980277094181991384137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1130456289004607908097461 105980277094181991384137)
                ·
                  rfl

theorem cell21_1393172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_1393172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393172 prefixEnd_1393172 := by exact prefixLift 1393172
  have htrace : WordTrace (prefixWord ++ tailWord_1393172) baseStart_1393172 baseEnd_1393172 := by
    simpa [prefixWord, tailWord_1393172, baseEnd_1393172] using wordTrace_append hprefix tailTrace_1393172
  have hstable : (prefixWord ++ tailWord_1393172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393172).length < 2 ^ (prefixWord ++ tailWord_1393172).sum := by decide
  have hdescent : baseEnd_1393172 < baseStart_1393172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393217 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 4]
def baseStart_1393217 : Nat := 118140960795 + 1393217 * 2 ^ 59
def prefixEnd_1393217 : Nat := 4983230072969 + 3 ^ 40 * 1393217 * 2
def baseEnd_1393217 : Nat := 317951100895635895902319

theorem tailTrace_1393217 : CollatzResearch.WordTrace tailWord_1393217 prefixEnd_1393217 317951100895635895902319 := by
  unfold tailWord_1393217
  simp only [CollatzResearch.WordTrace]
  refine ⟨50814798593620226365137905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33876532395746817576758603 50814798593620226365137905)
  ·
    refine ⟨38111098945215169773853429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50814798593620226365137905 38111098945215169773853429)
    ·
      refine ⟨3572915526113922166298759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38111098945215169773853429 3572915526113922166298759)
      ·
        refine ⟨5359373289170883249448139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572915526113922166298759 5359373289170883249448139)
        ·
          refine ⟨8039059933756324874172209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359373289170883249448139 8039059933756324874172209)
          ·
            refine ⟨6029294950317243655629157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8039059933756324874172209 6029294950317243655629157)
            ·
              refine ⟨1130492803184483185430467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6029294950317243655629157 1130492803184483185430467)
              ·
                refine ⟨1695739204776724778145701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130492803184483185430467 1695739204776724778145701)
                ·
                  refine ⟨317951100895635895902319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1695739204776724778145701 317951100895635895902319)
                  ·
                    rfl

theorem cell21_1393217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_1393217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393217 prefixEnd_1393217 := by exact prefixLift 1393217
  have htrace : WordTrace (prefixWord ++ tailWord_1393217) baseStart_1393217 baseEnd_1393217 := by
    simpa [prefixWord, tailWord_1393217, baseEnd_1393217] using wordTrace_append hprefix tailTrace_1393217
  have hstable : (prefixWord ++ tailWord_1393217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393217).length < 2 ^ (prefixWord ++ tailWord_1393217).sum := by decide
  have hdescent : baseEnd_1393217 < baseStart_1393217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393228 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_1393228 : Nat := 118140960795 + 1393228 * 2 ^ 59
def prefixEnd_1393228 : Nat := 4983230072969 + 3 ^ 40 * 1393228 * 2
def baseEnd_1393228 : Nat := 317953611245502321218963

theorem tailTrace_1393228 : CollatzResearch.WordTrace tailWord_1393228 prefixEnd_1393228 317953611245502321218963 := by
  unfold tailWord_1393228
  simp only [CollatzResearch.WordTrace]
  refine ⟨25407599898290187621894169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33876799864386916829192225 25407599898290187621894169)
  ·
    refine ⟨19055699923717640716420627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25407599898290187621894169 19055699923717640716420627)
    ·
      refine ⟨28583549885576461074630941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19055699923717640716420627 28583549885576461074630941)
      ·
        refine ⟨10718831207091172902986603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28583549885576461074630941 10718831207091172902986603)
        ·
          refine ⟨16078246810636759354479905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10718831207091172902986603 16078246810636759354479905)
          ·
            refine ⟨12058685107977569515859929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16078246810636759354479905 12058685107977569515859929)
            ·
              refine ⟨9044013830983177136894947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12058685107977569515859929 9044013830983177136894947)
              ·
                refine ⟨13566020746474765705342421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9044013830983177136894947 13566020746474765705342421)
                ·
                  refine ⟨317953611245502321218963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13566020746474765705342421 317953611245502321218963)
                  ·
                    rfl

theorem cell21_1393228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_1393228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393228 prefixEnd_1393228 := by exact prefixLift 1393228
  have htrace : WordTrace (prefixWord ++ tailWord_1393228) baseStart_1393228 baseEnd_1393228 := by
    simpa [prefixWord, tailWord_1393228, baseEnd_1393228] using wordTrace_append hprefix tailTrace_1393228
  have hstable : (prefixWord ++ tailWord_1393228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393228).length < 2 ^ (prefixWord ++ tailWord_1393228).sum := by decide
  have hdescent : baseEnd_1393228 < baseStart_1393228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393282 : List Nat := [3, 4, 3, 1, 1, 1, 3, 5]
def baseStart_1393282 : Nat := 118140960795 + 1393282 * 2 ^ 59
def prefixEnd_1393282 : Nat := 4983230072969 + 3 ^ 40 * 1393282 * 2
def baseEnd_1393282 : Nat := 105988644927070075772951

theorem tailTrace_1393282 : CollatzResearch.WordTrace tailWord_1393282 prefixEnd_1393282 105988644927070075772951 := by
  unfold tailWord_1393282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12704292334596185616563525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33878112892256494977502733 12704292334596185616563525)
  ·
    refine ⟨2382054812736784803105661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12704292334596185616563525 2382054812736784803105661)
    ·
      refine ⟨893270554776294301164623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2382054812736784803105661 893270554776294301164623)
      ·
        refine ⟨1339905832164441451746935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893270554776294301164623 1339905832164441451746935)
        ·
          refine ⟨2009858748246662177620403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339905832164441451746935 2009858748246662177620403)
          ·
            refine ⟨3014788122369993266430605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009858748246662177620403 3014788122369993266430605)
            ·
              refine ⟨1130545545888747474911477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3014788122369993266430605 1130545545888747474911477)
              ·
                refine ⟨105988644927070075772951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1130545545888747474911477 105988644927070075772951)
                ·
                  rfl

theorem cell21_1393282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_1393282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393282 prefixEnd_1393282 := by exact prefixLift 1393282
  have htrace : WordTrace (prefixWord ++ tailWord_1393282) baseStart_1393282 baseEnd_1393282 := by
    simpa [prefixWord, tailWord_1393282, baseEnd_1393282] using wordTrace_append hprefix tailTrace_1393282
  have hstable : (prefixWord ++ tailWord_1393282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393282).length < 2 ^ (prefixWord ++ tailWord_1393282).sum := by decide
  have hdescent : baseEnd_1393282 < baseStart_1393282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393304 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_1393304 : Nat := 118140960795 + 1393304 * 2 ^ 59
def prefixEnd_1393304 : Nat := 4983230072969 + 3 ^ 40 * 1393304 * 2
def baseEnd_1393304 : Nat := 317970955480943077952141

theorem tailTrace_1393304 : CollatzResearch.WordTrace tailWord_1393304 prefixEnd_1393304 317970955480943077952141 := by
  unfold tailWord_1393304
  simp only [CollatzResearch.WordTrace]
  refine ⟨25408985872152520111777483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33878647829536693482369977 25408985872152520111777483)
  ·
    refine ⟨38113478808228780167666225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25408985872152520111777483 38113478808228780167666225)
    ·
      refine ⟨28585109106171585125749669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38113478808228780167666225 28585109106171585125749669)
      ·
        refine ⟨5359707957407172211078063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28585109106171585125749669 5359707957407172211078063)
        ·
          refine ⟨8039561936110758316617095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359707957407172211078063 8039561936110758316617095)
          ·
            refine ⟨12059342904166137474925643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8039561936110758316617095 12059342904166137474925643)
            ·
              refine ⟨18089014356249206212388465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12059342904166137474925643 18089014356249206212388465)
              ·
                refine ⟨13566760767186904659291349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18089014356249206212388465 13566760767186904659291349)
                ·
                  refine ⟨317970955480943077952141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13566760767186904659291349 317970955480943077952141)
                  ·
                    rfl

theorem cell21_1393304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_1393304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393304 prefixEnd_1393304 := by exact prefixLift 1393304
  have htrace : WordTrace (prefixWord ++ tailWord_1393304) baseStart_1393304 baseEnd_1393304 := by
    simpa [prefixWord, tailWord_1393304, baseEnd_1393304] using wordTrace_append hprefix tailTrace_1393304
  have hstable : (prefixWord ++ tailWord_1393304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393304).length < 2 ^ (prefixWord ++ tailWord_1393304).sum := by decide
  have hdescent : baseEnd_1393304 < baseStart_1393304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393372 : List Nat := [2, 2, 5, 1, 1, 2, 3, 2, 3]
def baseStart_1393372 : Nat := 118140960795 + 1393372 * 2 ^ 59
def prefixEnd_1393372 : Nat := 4983230072969 + 3 ^ 40 * 1393372 * 2
def baseEnd_1393372 : Nat := 317986474007390070818669

theorem tailTrace_1393372 : CollatzResearch.WordTrace tailWord_1393372 prefixEnd_1393372 317986474007390070818669 := by
  unfold tailWord_1393372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25410225954029343918515185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33880301272039125224686913 25410225954029343918515185)
  ·
    refine ⟨19057669465522007938886389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25410225954029343918515185 19057669465522007938886389)
    ·
      refine ⟨1786656512392688244270599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19057669465522007938886389 1786656512392688244270599)
      ·
        refine ⟨2679984768589032366405899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786656512392688244270599 2679984768589032366405899)
        ·
          refine ⟨4019977152883548549608849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2679984768589032366405899 4019977152883548549608849)
          ·
            refine ⟨3014982864662661412206637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4019977152883548549608849 3014982864662661412206637)
            ·
              refine ⟨1130618574248498029577489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3014982864662661412206637 1130618574248498029577489)
              ·
                refine ⟨847963930686373522183117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1130618574248498029577489 847963930686373522183117)
                ·
                  refine ⟨317986474007390070818669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 847963930686373522183117 317986474007390070818669)
                  ·
                    rfl

theorem cell21_1393372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_1393372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393372 prefixEnd_1393372 := by exact prefixLift 1393372
  have htrace : WordTrace (prefixWord ++ tailWord_1393372) baseStart_1393372 baseEnd_1393372 := by
    simpa [prefixWord, tailWord_1393372, baseEnd_1393372] using wordTrace_append hprefix tailTrace_1393372
  have hstable : (prefixWord ++ tailWord_1393372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393372).length < 2 ^ (prefixWord ++ tailWord_1393372).sum := by decide
  have hdescent : baseEnd_1393372 < baseStart_1393372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393442 : List Nat := [3, 3, 1, 1, 2, 2, 3, 6]
def baseStart_1393442 : Nat := 118140960795 + 1393442 * 2 ^ 59
def prefixEnd_1393442 : Nat := 4983230072969 + 3 ^ 40 * 1393442 * 2
def baseEnd_1393442 : Nat := 106000816320361834883953

theorem tailTrace_1393442 : CollatzResearch.WordTrace tailWord_1393442 prefixEnd_1393442 106000816320361834883953 := by
  unfold tailWord_1393442
  simp only [CollatzResearch.WordTrace]
  refine ⟨12705751254451272448019645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33882003345203393194719053 12705751254451272448019645)
  ·
    refine ⟨4764656720419227168007367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12705751254451272448019645 4764656720419227168007367)
    ·
      refine ⟨7146985080628840752011051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4764656720419227168007367 7146985080628840752011051)
      ·
        refine ⟨10720477620943261128016577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7146985080628840752011051 10720477620943261128016577)
        ·
          refine ⟨8040358215707445846012433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10720477620943261128016577 8040358215707445846012433)
          ·
            refine ⟨6030268661780584384509325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8040358215707445846012433 6030268661780584384509325)
            ·
              refine ⟨2261350748167719144190997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6030268661780584384509325 2261350748167719144190997)
              ·
                refine ⟨106000816320361834883953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2261350748167719144190997 106000816320361834883953)
                ·
                  rfl

theorem cell21_1393442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_1393442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393442 prefixEnd_1393442 := by exact prefixLift 1393442
  have htrace : WordTrace (prefixWord ++ tailWord_1393442) baseStart_1393442 baseEnd_1393442 := by
    simpa [prefixWord, tailWord_1393442, baseEnd_1393442] using wordTrace_append hprefix tailTrace_1393442
  have hstable : (prefixWord ++ tailWord_1393442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393442).length < 2 ^ (prefixWord ++ tailWord_1393442).sum := by decide
  have hdescent : baseEnd_1393442 < baseStart_1393442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393504 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 4]
def baseStart_1393504 : Nat := 118140960795 + 1393504 * 2 ^ 59
def prefixEnd_1393504 : Nat := 4983230072969 + 3 ^ 40 * 1393504 * 2
def baseEnd_1393504 : Nat := 318016598205787174618399

theorem tailTrace_1393504 : CollatzResearch.WordTrace tailWord_1393504 prefixEnd_1393504 318016598205787174618399 := by
  unfold tailWord_1393504
  simp only [CollatzResearch.WordTrace]
  refine ⟨25412633171790237190417783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33883510895720316253890377 25412633171790237190417783)
  ·
    refine ⟨38118949757685355785626675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25412633171790237190417783 38118949757685355785626675)
    ·
      refine ⟨57178424636528033678440013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38118949757685355785626675 57178424636528033678440013)
      ·
        refine ⟨21441909238698012629415005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57178424636528033678440013 21441909238698012629415005)
        ·
          refine ⟨8040715964511754736030627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21441909238698012629415005 8040715964511754736030627)
          ·
            refine ⟨12061073946767632104045941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040715964511754736030627 12061073946767632104045941)
            ·
              refine ⟨1130725682509465509754307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12061073946767632104045941 1130725682509465509754307)
              ·
                refine ⟨1696088523764198264631461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130725682509465509754307 1696088523764198264631461)
                ·
                  refine ⟨318016598205787174618399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696088523764198264631461 318016598205787174618399)
                  ·
                    rfl

theorem cell21_1393504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_1393504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393504 prefixEnd_1393504 := by exact prefixLift 1393504
  have htrace : WordTrace (prefixWord ++ tailWord_1393504) baseStart_1393504 baseEnd_1393504 := by
    simpa [prefixWord, tailWord_1393504, baseEnd_1393504] using wordTrace_append hprefix tailTrace_1393504
  have hstable : (prefixWord ++ tailWord_1393504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393504).length < 2 ^ (prefixWord ++ tailWord_1393504).sum := by decide
  have hdescent : baseEnd_1393504 < baseStart_1393504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393642 : List Nat := [3, 1, 3, 1, 2, 3, 2, 3, 3]
def baseStart_1393642 : Nat := 118140960795 + 1393642 * 2 ^ 59
def prefixEnd_1393642 : Nat := 4983230072969 + 3 ^ 40 * 1393642 * 2
def baseEnd_1393642 : Nat := 318048091685929601318117

theorem tailTrace_1393642 : CollatzResearch.WordTrace tailWord_1393642 prefixEnd_1393642 318048091685929601318117 := by
  unfold tailWord_1393642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707574904270130987339795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33886866411387015966239453 12707574904270130987339795)
  ·
    refine ⟨19061362356405196481009693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12707574904270130987339795 19061362356405196481009693)
    ·
      refine ⟨7148010883651948680378635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19061362356405196481009693 7148010883651948680378635)
      ·
        refine ⟨10722016325477923020567953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7148010883651948680378635 10722016325477923020567953)
        ·
          refine ⟨8041512244108442265425965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10722016325477923020567953 8041512244108442265425965)
          ·
            refine ⟨3015567091540665849534737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8041512244108442265425965 3015567091540665849534737)
            ·
              refine ⟨2261675318655499387151053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3015567091540665849534737 2261675318655499387151053)
              ·
                refine ⟨848128244495812270181645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2261675318655499387151053 848128244495812270181645)
                ·
                  refine ⟨318048091685929601318117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848128244495812270181645 318048091685929601318117)
                  ·
                    rfl

theorem cell21_1393642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_1393642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393642 prefixEnd_1393642 := by exact prefixLift 1393642
  have htrace : WordTrace (prefixWord ++ tailWord_1393642) baseStart_1393642 baseEnd_1393642 := by
    simpa [prefixWord, tailWord_1393642, baseEnd_1393642] using wordTrace_append hprefix tailTrace_1393642
  have hstable : (prefixWord ++ tailWord_1393642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393642).length < 2 ^ (prefixWord ++ tailWord_1393642).sum := by decide
  have hdescent : baseEnd_1393642 < baseStart_1393642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393687 : List Nat := [1, 1, 3, 5, 1, 3, 2, 5]
def baseStart_1393687 : Nat := 118140960795 + 1393687 * 2 ^ 59
def prefixEnd_1393687 : Nat := 4983230072969 + 3 ^ 40 * 1393687 * 2
def baseEnd_1393687 : Nat := 106019453766339841022675

theorem tailTrace_1393687 : CollatzResearch.WordTrace tailWord_1393687 prefixEnd_1393687 106019453766339841022675 := by
  unfold tailWord_1393687
  simp only [CollatzResearch.WordTrace]
  refine ⟨50831940901917496634747315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33887960601278331089831543 50831940901917496634747315)
  ·
    refine ⟨76247911352876244952120973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50831940901917496634747315 76247911352876244952120973)
    ·
      refine ⟨28592966757328591857045365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76247911352876244952120973 28592966757328591857045365)
      ·
        refine ⟨2680590633499555486598003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28592966757328591857045365 2680590633499555486598003)
        ·
          refine ⟨4020885950249333229897005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680590633499555486598003 4020885950249333229897005)
          ·
            refine ⟨1507832231343499961211377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4020885950249333229897005 1507832231343499961211377)
            ·
              refine ⟨1130874173507624970908533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1507832231343499961211377 1130874173507624970908533)
              ·
                refine ⟨106019453766339841022675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1130874173507624970908533 106019453766339841022675)
                ·
                  rfl

theorem cell21_1393687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 5].length) (baseStart_1393687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393687 prefixEnd_1393687 := by exact prefixLift 1393687
  have htrace : WordTrace (prefixWord ++ tailWord_1393687) baseStart_1393687 baseEnd_1393687 := by
    simpa [prefixWord, tailWord_1393687, baseEnd_1393687] using wordTrace_append hprefix tailTrace_1393687
  have hstable : (prefixWord ++ tailWord_1393687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393687).length < 2 ^ (prefixWord ++ tailWord_1393687).sum := by decide
  have hdescent : baseEnd_1393687 < baseStart_1393687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393718 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1393718 : Nat := 118140960795 + 1393718 * 2 ^ 59
def prefixEnd_1393718 : Nat := 4983230072969 + 3 ^ 40 * 1393718 * 2
def baseEnd_1393718 : Nat := 318065435921370358051295

theorem tailTrace_1393718 : CollatzResearch.WordTrace tailWord_1393718 prefixEnd_1393718 318065435921370358051295 := by
  unfold tailWord_1393718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3177066972800324308070363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33888714376536792619417205 3177066972800324308070363)
  ·
    refine ⟨4765600459200486462105545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3177066972800324308070363 4765600459200486462105545)
    ·
      refine ⟨3574200344400364846579159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4765600459200486462105545 3574200344400364846579159)
      ·
        refine ⟨5361300516600547269868739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3574200344400364846579159 5361300516600547269868739)
        ·
          refine ⟨8041950774900820904803109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5361300516600547269868739 8041950774900820904803109)
          ·
            refine ⟨1507865770293903919650583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8041950774900820904803109 1507865770293903919650583)
            ·
              refine ⟨2261798655440855879475875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507865770293903919650583 2261798655440855879475875)
              ·
                refine ⟨3392697983161283819213813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261798655440855879475875 3392697983161283819213813)
                ·
                  refine ⟨318065435921370358051295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3392697983161283819213813 318065435921370358051295)
                  ·
                    rfl

theorem cell21_1393718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1393718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393718 prefixEnd_1393718 := by exact prefixLift 1393718
  have htrace : WordTrace (prefixWord ++ tailWord_1393718) baseStart_1393718 baseEnd_1393718 := by
    simpa [prefixWord, tailWord_1393718, baseEnd_1393718] using wordTrace_append hprefix tailTrace_1393718
  have hstable : (prefixWord ++ tailWord_1393718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393718).length < 2 ^ (prefixWord ++ tailWord_1393718).sum := by decide
  have hdescent : baseEnd_1393718 < baseStart_1393718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393822 : List Nat := [4, 3, 1, 1, 2, 2, 8]
def baseStart_1393822 : Nat := 118140960795 + 1393822 * 2 ^ 59
def prefixEnd_1393822 : Nat := 4983230072969 + 3 ^ 40 * 1393822 * 2
def baseEnd_1393822 : Nat := 35343241126476587590861

theorem tailTrace_1393822 : CollatzResearch.WordTrace tailWord_1393822 prefixEnd_1393822 35343241126476587590861 := by
  unfold tailWord_1393822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6354608094553551836363965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33891243170952276460607813 6354608094553551836363965)
  ·
    refine ⟨2382978035457581938636487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6354608094553551836363965 2382978035457581938636487)
    ·
      refine ⟨3574467053186372907954731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2382978035457581938636487 3574467053186372907954731)
      ·
        refine ⟨5361700579779559361932097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3574467053186372907954731 5361700579779559361932097)
        ·
          refine ⟨4021275434834669521449073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5361700579779559361932097 4021275434834669521449073)
          ·
            refine ⟨3015956576126002141086805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4021275434834669521449073 3015956576126002141086805)
            ·
              refine ⟨35343241126476587590861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3015956576126002141086805 35343241126476587590861)
              ·
                rfl

theorem cell21_1393822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 8].length) (baseStart_1393822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393822 prefixEnd_1393822 := by exact prefixLift 1393822
  have htrace : WordTrace (prefixWord ++ tailWord_1393822) baseStart_1393822 baseEnd_1393822 := by
    simpa [prefixWord, tailWord_1393822, baseEnd_1393822] using wordTrace_append hprefix tailTrace_1393822
  have hstable : (prefixWord ++ tailWord_1393822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393822).length < 2 ^ (prefixWord ++ tailWord_1393822).sum := by decide
  have hdescent : baseEnd_1393822 < baseStart_1393822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393862 : List Nat := [6, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1393862 : Nat := 118140960795 + 1393862 * 2 ^ 59
def prefixEnd_1393862 : Nat := 4983230072969 + 3 ^ 40 * 1393862 * 2
def baseEnd_1393862 : Nat := 318098298683258107651001

theorem tailTrace_1393862 : CollatzResearch.WordTrace tailWord_1393862 prefixEnd_1393862 318098298683258107651001 := by
  unfold tailWord_1393862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588697614883859422573995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33892215784189001014911893 1588697614883859422573995)
  ·
    refine ⟨2383046422325789133860993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1588697614883859422573995 2383046422325789133860993)
    ·
      refine ⟨1787284816744341850395745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2383046422325789133860993 1787284816744341850395745)
      ·
        refine ⟨1340463612558256387796809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1787284816744341850395745 1340463612558256387796809)
        ·
          refine ⟨1005347709418692290847607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1340463612558256387796809 1005347709418692290847607)
          ·
            refine ⟨1508021564128038436271411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005347709418692290847607 1508021564128038436271411)
            ·
              refine ⟨2262032346192057654407117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508021564128038436271411 2262032346192057654407117)
              ·
                refine ⟨848262129822021620402669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2262032346192057654407117 848262129822021620402669)
                ·
                  refine ⟨318098298683258107651001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848262129822021620402669 318098298683258107651001)
                  ·
                    rfl

theorem cell21_1393862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1393862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393862 prefixEnd_1393862 := by exact prefixLift 1393862
  have htrace : WordTrace (prefixWord ++ tailWord_1393862) baseStart_1393862 baseEnd_1393862 := by
    simpa [prefixWord, tailWord_1393862, baseEnd_1393862] using wordTrace_append hprefix tailTrace_1393862
  have hstable : (prefixWord ++ tailWord_1393862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393862).length < 2 ^ (prefixWord ++ tailWord_1393862).sum := by decide
  have hdescent : baseEnd_1393862 < baseStart_1393862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393901 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1393901 : Nat := 118140960795 + 1393901 * 2 ^ 59
def prefixEnd_1393901 : Nat := 4983230072969 + 3 ^ 40 * 1393901 * 2
def baseEnd_1393901 : Nat := 318107199014602706500921

theorem tailTrace_1393901 : CollatzResearch.WordTrace tailWord_1393901 prefixEnd_1393901 318107199014602706500921 := by
  unfold tailWord_1393901
  simp only [CollatzResearch.WordTrace]
  refine ⟨50839746123142211183037557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33893164082094807455358371 50839746123142211183037557)
  ·
    refine ⟨4766226199044582298409771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50839746123142211183037557 4766226199044582298409771)
    ·
      refine ⟨7149339298566873447614657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4766226199044582298409771 7149339298566873447614657)
      ·
        refine ⟨5362004473925155085710993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7149339298566873447614657 5362004473925155085710993)
        ·
          refine ⟨4021503355443866314283245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5362004473925155085710993 4021503355443866314283245)
          ·
            refine ⟨1508063758291449867856217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4021503355443866314283245 1508063758291449867856217)
            ·
              refine ⟨1131047818718587400892163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508063758291449867856217 1131047818718587400892163)
              ·
                refine ⟨1696571728077881101338245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131047818718587400892163 1696571728077881101338245)
                ·
                  refine ⟨318107199014602706500921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696571728077881101338245 318107199014602706500921)
                  ·
                    rfl

theorem cell21_1393901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1393901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393901 prefixEnd_1393901 := by exact prefixLift 1393901
  have htrace : WordTrace (prefixWord ++ tailWord_1393901) baseStart_1393901 baseEnd_1393901 := by
    simpa [prefixWord, tailWord_1393901, baseEnd_1393901] using wordTrace_append hprefix tailTrace_1393901
  have hstable : (prefixWord ++ tailWord_1393901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393901).length < 2 ^ (prefixWord ++ tailWord_1393901).sum := by decide
  have hdescent : baseEnd_1393901 < baseStart_1393901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393940 : List Nat := [2, 4, 15]
def baseStart_1393940 : Nat := 118140960795 + 1393940 * 2 ^ 59
def prefixEnd_1393940 : Nat := 4983230072969 + 3 ^ 40 * 1393940 * 2
def baseEnd_1393940 : Nat := 436373250131614959329

theorem tailTrace_1393940 : CollatzResearch.WordTrace tailWord_1393940 prefixEnd_1393940 436373250131614959329 := by
  unfold tailWord_1393940
  simp only [CollatzResearch.WordTrace]
  refine ⟨25420584285000460421853637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33894112380000613895804849 25420584285000460421853637)
  ·
    refine ⟨4766359553437586329097557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25420584285000460421853637 4766359553437586329097557)
    ·
      refine ⟨436373250131614959329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 4766359553437586329097557 436373250131614959329)
      ·
        rfl

theorem cell21_1393940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 15].length) (baseStart_1393940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393940 prefixEnd_1393940 := by exact prefixLift 1393940
  have htrace : WordTrace (prefixWord ++ tailWord_1393940) baseStart_1393940 baseEnd_1393940 := by
    simpa [prefixWord, tailWord_1393940, baseEnd_1393940] using wordTrace_append hprefix tailTrace_1393940
  have hstable : (prefixWord ++ tailWord_1393940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393940).length < 2 ^ (prefixWord ++ tailWord_1393940).sum := by decide
  have hdescent : baseEnd_1393940 < baseStart_1393940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393943 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 4]
def baseStart_1393943 : Nat := 118140960795 + 1393943 * 2 ^ 59
def prefixEnd_1393943 : Nat := 4983230072969 + 3 ^ 40 * 1393943 * 2
def baseEnd_1393943 : Nat := 318116783986819966800835

theorem tailTrace_1393943 : CollatzResearch.WordTrace tailWord_1393943 prefixEnd_1393943 318116783986819966800835 := by
  unfold tailWord_1393943
  simp only [CollatzResearch.WordTrace]
  refine ⟨50841277988990052356066483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33894185325993368237377655 50841277988990052356066483)
  ·
    refine ⟨76261916983485078534099725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50841277988990052356066483 76261916983485078534099725)
    ·
      refine ⟨28598218868806904450287397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76261916983485078534099725 28598218868806904450287397)
      ·
        refine ⟨5362166037901294584428887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28598218868806904450287397 5362166037901294584428887)
        ·
          refine ⟨8043249056851941876643331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362166037901294584428887 8043249056851941876643331)
          ·
            refine ⟨12064873585277912814964997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8043249056851941876643331 12064873585277912814964997)
            ·
              refine ⟨2262163797239608652805937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12064873585277912814964997 2262163797239608652805937)
              ·
                refine ⟨1696622847929706489604453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2262163797239608652805937 1696622847929706489604453)
                ·
                  refine ⟨318116783986819966800835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696622847929706489604453 318116783986819966800835)
                  ·
                    rfl

theorem cell21_1393943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 4].length) (baseStart_1393943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393943 prefixEnd_1393943 := by exact prefixLift 1393943
  have htrace : WordTrace (prefixWord ++ tailWord_1393943) baseStart_1393943 baseEnd_1393943 := by
    simpa [prefixWord, tailWord_1393943, baseEnd_1393943] using wordTrace_append hprefix tailTrace_1393943
  have hstable : (prefixWord ++ tailWord_1393943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393943).length < 2 ^ (prefixWord ++ tailWord_1393943).sum := by decide
  have hdescent : baseEnd_1393943 < baseStart_1393943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393946 : List Nat := [3, 1, 1, 3, 3, 1, 4, 2, 3]
def baseStart_1393946 : Nat := 118140960795 + 1393946 * 2 ^ 59
def prefixEnd_1393946 : Nat := 4983230072969 + 3 ^ 40 * 1393946 * 2
def baseEnd_1393946 : Nat := 318117468627692628250829

theorem tailTrace_1393946 : CollatzResearch.WordTrace tailWord_1393946 prefixEnd_1393946 318117468627692628250829 := by
  unfold tailWord_1393946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12710346851994795967106423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33894258271986122578950461 12710346851994795967106423)
  ·
    refine ⟨19065520277992193950659635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12710346851994795967106423 19065520277992193950659635)
    ·
      refine ⟨28598280416988290925989453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19065520277992193950659635 28598280416988290925989453)
      ·
        refine ⟨10724355156370609097246045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28598280416988290925989453 10724355156370609097246045)
        ·
          refine ⟨4021633183638978411467267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10724355156370609097246045 4021633183638978411467267)
          ·
            refine ⟨6032449775458467617200901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021633183638978411467267 6032449775458467617200901)
            ·
              refine ⟨1131084332898462678225169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6032449775458467617200901 1131084332898462678225169)
              ·
                refine ⟨848313249673847008668877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131084332898462678225169 848313249673847008668877)
                ·
                  refine ⟨318117468627692628250829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848313249673847008668877 318117468627692628250829)
                  ·
                    rfl

theorem cell21_1393946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_1393946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393946 prefixEnd_1393946 := by exact prefixLift 1393946
  have htrace : WordTrace (prefixWord ++ tailWord_1393946) baseStart_1393946 baseEnd_1393946 := by
    simpa [prefixWord, tailWord_1393946, baseEnd_1393946] using wordTrace_append hprefix tailTrace_1393946
  have hstable : (prefixWord ++ tailWord_1393946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393946).length < 2 ^ (prefixWord ++ tailWord_1393946).sum := by decide
  have hdescent : baseEnd_1393946 < baseStart_1393946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393957 : List Nat := [1, 3, 1, 2, 4, 1, 3, 6]
def baseStart_1393957 : Nat := 118140960795 + 1393957 * 2 ^ 59
def prefixEnd_1393957 : Nat := 4983230072969 + 3 ^ 40 * 1393957 * 2
def baseEnd_1393957 : Nat := 106039992992519684522491

theorem tailTrace_1393957 : CollatzResearch.WordTrace tailWord_1393957 prefixEnd_1393957 106039992992519684522491 := by
  unfold tailWord_1393957
  simp only [CollatzResearch.WordTrace]
  refine ⟨50841788610939332747076125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33894525740626221831384083 50841788610939332747076125)
  ·
    refine ⟨19065670729102249780153547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50841788610939332747076125 19065670729102249780153547)
    ·
      refine ⟨28598506093653374670230321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19065670729102249780153547 28598506093653374670230321)
      ·
        refine ⟨21448879570240031002672741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28598506093653374670230321 21448879570240031002672741)
        ·
          refine ⟨4021664919420005813001139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21448879570240031002672741 4021664919420005813001139)
          ·
            refine ⟨6032497379130008719501709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021664919420005813001139 6032497379130008719501709)
            ·
              refine ⟨2262186517173753269813141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6032497379130008719501709 2262186517173753269813141)
              ·
                refine ⟨106039992992519684522491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2262186517173753269813141 106039992992519684522491)
                ·
                  rfl

theorem cell21_1393957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 6].length) (baseStart_1393957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393957 prefixEnd_1393957 := by exact prefixLift 1393957
  have htrace : WordTrace (prefixWord ++ tailWord_1393957) baseStart_1393957 baseEnd_1393957 := by
    simpa [prefixWord, tailWord_1393957, baseEnd_1393957] using wordTrace_append hprefix tailTrace_1393957
  have hstable : (prefixWord ++ tailWord_1393957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393957).length < 2 ^ (prefixWord ++ tailWord_1393957).sum := by decide
  have hdescent : baseEnd_1393957 < baseStart_1393957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393971 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 7]
def baseStart_1393971 : Nat := 118140960795 + 1393971 * 2 ^ 59
def prefixEnd_1393971 : Nat := 4983230072969 + 3 ^ 40 * 1393971 * 2
def baseEnd_1393971 : Nat := 318123173968298140334111

theorem tailTrace_1393971 : CollatzResearch.WordTrace tailWord_1393971 prefixEnd_1393971 318123173968298140334111 := by
  unfold tailWord_1393971
  simp only [CollatzResearch.WordTrace]
  refine ⟨50842299232888613138085767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33894866155259075425390511 50842299232888613138085767)
  ·
    refine ⟨76263448849332919707128651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50842299232888613138085767 76263448849332919707128651)
    ·
      refine ⟨114395173273999379560692977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76263448849332919707128651 114395173273999379560692977)
      ·
        refine ⟨85796379955499534670519733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114395173273999379560692977 85796379955499534670519733)
        ·
          refine ⟨8043410620828081375361225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85796379955499534670519733 8043410620828081375361225)
          ·
            refine ⟨6032557965621061031520919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8043410620828081375361225 6032557965621061031520919)
            ·
              refine ⟨9048836948431591547281379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032557965621061031520919 9048836948431591547281379)
              ·
                refine ⟨13573255422647387320922069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9048836948431591547281379 13573255422647387320922069)
                ·
                  refine ⟨318123173968298140334111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13573255422647387320922069 318123173968298140334111)
                  ·
                    rfl

theorem cell21_1393971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_1393971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1393971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1393971 prefixEnd_1393971 := by exact prefixLift 1393971
  have htrace : WordTrace (prefixWord ++ tailWord_1393971) baseStart_1393971 baseEnd_1393971 := by
    simpa [prefixWord, tailWord_1393971, baseEnd_1393971] using wordTrace_append hprefix tailTrace_1393971
  have hstable : (prefixWord ++ tailWord_1393971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393971).length < 2 ^ (prefixWord ++ tailWord_1393971).sum := by decide
  have hdescent : baseEnd_1393971 < baseStart_1393971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394005 : List Nat := [1, 3, 2, 2, 3, 1, 2, 4, 3]
def baseStart_1394005 : Nat := 118140960795 + 1394005 * 2 ^ 59
def prefixEnd_1394005 : Nat := 4983230072969 + 3 ^ 40 * 1394005 * 2
def baseEnd_1394005 : Nat := 318130933231521636767375

theorem tailTrace_1394005 : CollatzResearch.WordTrace tailWord_1394005 prefixEnd_1394005 318130933231521636767375 := by
  unfold tailWord_1394005
  simp only [CollatzResearch.WordTrace]
  refine ⟨50843539314765436944823469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33895692876510291296548979 50843539314765436944823469)
  ·
    refine ⟨19066327243037038854308801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50843539314765436944823469 19066327243037038854308801)
    ·
      refine ⟨14299745432277779140731601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19066327243037038854308801 14299745432277779140731601)
      ·
        refine ⟨10724809074208334355548701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14299745432277779140731601 10724809074208334355548701)
        ·
          refine ⟨4021803402828125383330763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10724809074208334355548701 4021803402828125383330763)
          ·
            refine ⟨6032705104242188074996145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021803402828125383330763 6032705104242188074996145)
            ·
              refine ⟨4524528828181641056247109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6032705104242188074996145 4524528828181641056247109)
              ·
                refine ⟨848349155284057698046333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4524528828181641056247109 848349155284057698046333)
                ·
                  refine ⟨318130933231521636767375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848349155284057698046333 318130933231521636767375)
                  ·
                    rfl

theorem cell21_1394005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_1394005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394005 prefixEnd_1394005 := by exact prefixLift 1394005
  have htrace : WordTrace (prefixWord ++ tailWord_1394005) baseStart_1394005 baseEnd_1394005 := by
    simpa [prefixWord, tailWord_1394005, baseEnd_1394005] using wordTrace_append hprefix tailTrace_1394005
  have hstable : (prefixWord ++ tailWord_1394005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394005).length < 2 ^ (prefixWord ++ tailWord_1394005).sum := by decide
  have hdescent : baseEnd_1394005 < baseStart_1394005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394033 : List Nat := [1, 2, 2, 2, 1, 2, 6, 5]
def baseStart_1394033 : Nat := 118140960795 + 1394033 * 2 ^ 59
def prefixEnd_1394033 : Nat := 4983230072969 + 3 ^ 40 * 1394033 * 2
def baseEnd_1394033 : Nat := 106045774404333270100217

theorem tailTrace_1394033 : CollatzResearch.WordTrace tailWord_1394033 prefixEnd_1394033 106045774404333270100217 := by
  unfold tailWord_1394033
  simp only [CollatzResearch.WordTrace]
  refine ⟨50844560558663997726842753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33896373705775998484561835 50844560558663997726842753)
  ·
    refine ⟨38133420418997998295132065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50844560558663997726842753 38133420418997998295132065)
    ·
      refine ⟨28600065314248498721349049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38133420418997998295132065 28600065314248498721349049)
      ·
        refine ⟨21450048985686374041011787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28600065314248498721349049 21450048985686374041011787)
        ·
          refine ⟨32175073478529561061517681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21450048985686374041011787 32175073478529561061517681)
          ·
            refine ⟨24131305108897170796138261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32175073478529561061517681 24131305108897170796138261)
            ·
              refine ⟨1131154926979554881068981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24131305108897170796138261 1131154926979554881068981)
              ·
                refine ⟨106045774404333270100217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1131154926979554881068981 106045774404333270100217)
                ·
                  rfl

theorem cell21_1394033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 5].length) (baseStart_1394033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394033 prefixEnd_1394033 := by exact prefixLift 1394033
  have htrace : WordTrace (prefixWord ++ tailWord_1394033) baseStart_1394033 baseEnd_1394033 := by
    simpa [prefixWord, tailWord_1394033, baseEnd_1394033] using wordTrace_append hprefix tailTrace_1394033
  have hstable : (prefixWord ++ tailWord_1394033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394033).length < 2 ^ (prefixWord ++ tailWord_1394033).sum := by decide
  have hdescent : baseEnd_1394033 < baseStart_1394033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394050 : List Nat := [3, 4, 2, 1, 1, 1, 9]
def baseStart_1394050 : Nat := 118140960795 + 1394050 * 2 ^ 59
def prefixEnd_1394050 : Nat := 4983230072969 + 3 ^ 40 * 1394050 * 2
def baseEnd_1394050 : Nat := 35349022538290173168587

theorem tailTrace_1394050 : CollatzResearch.WordTrace tailWord_1394050 prefixEnd_1394050 35349022538290173168587 := by
  unfold tailWord_1394050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12711295149900602407552901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33896787066401606420141069 12711295149900602407552901)
  ·
    refine ⟨2383367840606362951416169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12711295149900602407552901 2383367840606362951416169)
    ·
      refine ⟨1787525880454772213562127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2383367840606362951416169 1787525880454772213562127)
      ·
        refine ⟨2681288820682158320343191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787525880454772213562127 2681288820682158320343191)
        ·
          refine ⟨4021933231023237480514787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2681288820682158320343191 4021933231023237480514787)
          ·
            refine ⟨6032899846534856220772181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021933231023237480514787 6032899846534856220772181)
            ·
              refine ⟨35349022538290173168587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6032899846534856220772181 35349022538290173168587)
              ·
                rfl

theorem cell21_1394050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 9].length) (baseStart_1394050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394050 prefixEnd_1394050 := by exact prefixLift 1394050
  have htrace : WordTrace (prefixWord ++ tailWord_1394050) baseStart_1394050 baseEnd_1394050 := by
    simpa [prefixWord, tailWord_1394050, baseEnd_1394050] using wordTrace_append hprefix tailTrace_1394050
  have hstable : (prefixWord ++ tailWord_1394050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394050).length < 2 ^ (prefixWord ++ tailWord_1394050).sum := by decide
  have hdescent : baseEnd_1394050 < baseStart_1394050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394092 : List Nat := [2, 2, 1, 1, 1, 1, 6, 7]
def baseStart_1394092 : Nat := 118140960795 + 1394092 * 2 ^ 59
def prefixEnd_1394092 : Nat := 4983230072969 + 3 ^ 40 * 1394092 * 2
def baseEnd_1394092 : Nat := 106050262605609606272399

theorem tailTrace_1394092 : CollatzResearch.WordTrace tailWord_1394092 prefixEnd_1394092 106050262605609606272399 := by
  unfold tailWord_1394092
  simp only [CollatzResearch.WordTrace]
  refine ⟨25423356232725125401620265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33897808310300167202160353 25423356232725125401620265)
  ·
    refine ⟨19067517174543844051215199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25423356232725125401620265 19067517174543844051215199)
    ·
      refine ⟨28601275761815766076822799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19067517174543844051215199 28601275761815766076822799)
      ·
        refine ⟨42901913642723649115234199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28601275761815766076822799 42901913642723649115234199)
        ·
          refine ⟨64352870464085473672851299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42901913642723649115234199 64352870464085473672851299)
          ·
            refine ⟨96529305696128210509276949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64352870464085473672851299 96529305696128210509276949)
            ·
              refine ⟨4524811204506009867622357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96529305696128210509276949 4524811204506009867622357)
              ·
                refine ⟨106050262605609606272399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4524811204506009867622357 106050262605609606272399)
                ·
                  rfl

theorem cell21_1394092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_1394092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394092 prefixEnd_1394092 := by exact prefixLift 1394092
  have htrace : WordTrace (prefixWord ++ tailWord_1394092) baseStart_1394092 baseEnd_1394092 := by
    simpa [prefixWord, tailWord_1394092, baseEnd_1394092] using wordTrace_append hprefix tailTrace_1394092
  have hstable : (prefixWord ++ tailWord_1394092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394092).length < 2 ^ (prefixWord ++ tailWord_1394092).sum := by decide
  have hdescent : baseEnd_1394092 < baseStart_1394092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394168 : List Nat := [2, 1, 2, 1, 1, 6, 8]
def baseStart_1394168 : Nat := 118140960795 + 1394168 * 2 ^ 59
def prefixEnd_1394168 : Nat := 4983230072969 + 3 ^ 40 * 1394168 * 2
def baseEnd_1394168 : Nat := 35352014672474397283375

theorem tailTrace_1394168 : CollatzResearch.WordTrace tailWord_1394168 prefixEnd_1394168 35352014672474397283375 := by
  unfold tailWord_1394168
  simp only [CollatzResearch.WordTrace]
  refine ⟨25424742206587457891503579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33899656275449943855338105 25424742206587457891503579)
  ·
    refine ⟨38137113309881186837255369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25424742206587457891503579 38137113309881186837255369)
    ·
      refine ⟨28602834982410890127941527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38137113309881186837255369 28602834982410890127941527)
      ·
        refine ⟨42904252473616335191912291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28602834982410890127941527 42904252473616335191912291)
        ·
          refine ⟨64356378710424502787868437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42904252473616335191912291 64356378710424502787868437)
          ·
            refine ⟨3016705252051148568181333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64356378710424502787868437 3016705252051148568181333)
            ·
              refine ⟨35352014672474397283375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3016705252051148568181333 35352014672474397283375)
              ·
                rfl

theorem cell21_1394168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 8].length) (baseStart_1394168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394168 prefixEnd_1394168 := by exact prefixLift 1394168
  have htrace : WordTrace (prefixWord ++ tailWord_1394168) baseStart_1394168 baseEnd_1394168 := by
    simpa [prefixWord, tailWord_1394168, baseEnd_1394168] using wordTrace_append hprefix tailTrace_1394168
  have hstable : (prefixWord ++ tailWord_1394168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394168).length < 2 ^ (prefixWord ++ tailWord_1394168).sum := by decide
  have hdescent : baseEnd_1394168 < baseStart_1394168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394174 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_1394174 : Nat := 118140960795 + 1394174 * 2 ^ 59
def prefixEnd_1394174 : Nat := 4983230072969 + 3 ^ 40 * 1394174 * 2
def baseEnd_1394174 : Nat := 318169501334014898450363

theorem tailTrace_1394174 : CollatzResearch.WordTrace tailWord_1394174 prefixEnd_1394174 318169501334014898450363 := by
  unfold tailWord_1394174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6356212906394147350965697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33899802167435452538483717 6356212906394147350965697)
  ·
    refine ⟨4767159679795610513224273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6356212906394147350965697 4767159679795610513224273)
    ·
      refine ⟨3575369759846707884918205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4767159679795610513224273 3575369759846707884918205)
      ·
        refine ⟨1340763659942515456844327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3575369759846707884918205 1340763659942515456844327)
        ·
          refine ⟨2011145489913773185266491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340763659942515456844327 2011145489913773185266491)
          ·
            refine ⟨3016718234870659777899737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011145489913773185266491 3016718234870659777899737)
            ·
              refine ⟨2262538676152994833424803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3016718234870659777899737 2262538676152994833424803)
              ·
                refine ⟨3393808014229492250137205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262538676152994833424803 3393808014229492250137205)
                ·
                  refine ⟨318169501334014898450363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3393808014229492250137205 318169501334014898450363)
                  ·
                    rfl

theorem cell21_1394174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_1394174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394174 prefixEnd_1394174 := by exact prefixLift 1394174
  have htrace : WordTrace (prefixWord ++ tailWord_1394174) baseStart_1394174 baseEnd_1394174 := by
    simpa [prefixWord, tailWord_1394174, baseEnd_1394174] using wordTrace_append hprefix tailTrace_1394174
  have hstable : (prefixWord ++ tailWord_1394174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394174).length < 2 ^ (prefixWord ++ tailWord_1394174).sum := by decide
  have hdescent : baseEnd_1394174 < baseStart_1394174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394188 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 4]
def baseStart_1394188 : Nat := 118140960795 + 1394188 * 2 ^ 59
def prefixEnd_1394188 : Nat := 4983230072969 + 3 ^ 40 * 1394188 * 2
def baseEnd_1394188 : Nat := 318172696324753985217001

theorem tailTrace_1394188 : CollatzResearch.WordTrace tailWord_1394188 prefixEnd_1394188 318172696324753985217001 := by
  unfold tailWord_1394188
  simp only [CollatzResearch.WordTrace]
  refine ⟨25425106936551229599367609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33900142582068306132490145 25425106936551229599367609)
  ·
    refine ⟨19068830202413422199525707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25425106936551229599367609 19068830202413422199525707)
    ·
      refine ⟨28603245303620133299288561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19068830202413422199525707 28603245303620133299288561)
      ·
        refine ⟨21452433977715099974466421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28603245303620133299288561 21452433977715099974466421)
        ·
          refine ⟨2011165685410790622606227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21452433977715099974466421 2011165685410790622606227)
          ·
            refine ⟨3016748528116185933909341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011165685410790622606227 3016748528116185933909341)
            ·
              refine ⟨1131280698043569725216003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3016748528116185933909341 1131280698043569725216003)
              ·
                refine ⟨1696921047065354587824005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131280698043569725216003 1696921047065354587824005)
                ·
                  refine ⟨318172696324753985217001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696921047065354587824005 318172696324753985217001)
                  ·
                    rfl

theorem cell21_1394188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_1394188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394188 prefixEnd_1394188 := by exact prefixLift 1394188
  have htrace : WordTrace (prefixWord ++ tailWord_1394188) baseStart_1394188 baseEnd_1394188 := by
    simpa [prefixWord, tailWord_1394188, baseEnd_1394188] using wordTrace_append hprefix tailTrace_1394188
  have hstable : (prefixWord ++ tailWord_1394188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394188).length < 2 ^ (prefixWord ++ tailWord_1394188).sum := by decide
  have hdescent : baseEnd_1394188 < baseStart_1394188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394247 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 4]
def baseStart_1394247 : Nat := 118140960795 + 1394247 * 2 ^ 59
def prefixEnd_1394247 : Nat := 4983230072969 + 3 ^ 40 * 1394247 * 2
def baseEnd_1394247 : Nat := 318186160928582993733547

theorem tailTrace_1394247 : CollatzResearch.WordTrace tailWord_1394247 prefixEnd_1394247 318186160928582993733547 := by
  unfold tailWord_1394247
  simp only [CollatzResearch.WordTrace]
  refine ⟨50852365779888712275132995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33901577186592474850088663 50852365779888712275132995)
  ·
    refine ⟨76278548669833068412699493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50852365779888712275132995 76278548669833068412699493)
    ·
      refine ⟨14302227875593700327381155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76278548669833068412699493 14302227875593700327381155)
      ·
        refine ⟨21453341813390550491071733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14302227875593700327381155 21453341813390550491071733)
        ·
          refine ⟨2011250795005364108537975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21453341813390550491071733 2011250795005364108537975)
          ·
            refine ⟨3016876192508046162806963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011250795005364108537975 3016876192508046162806963)
            ·
              refine ⟨4525314288762069244210445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016876192508046162806963 4525314288762069244210445)
              ·
                refine ⟨1696992858285775966578917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4525314288762069244210445 1696992858285775966578917)
                ·
                  refine ⟨318186160928582993733547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696992858285775966578917 318186160928582993733547)
                  ·
                    rfl

theorem cell21_1394247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 4].length) (baseStart_1394247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394247 prefixEnd_1394247 := by exact prefixLift 1394247
  have htrace : WordTrace (prefixWord ++ tailWord_1394247) baseStart_1394247 baseEnd_1394247 := by
    simpa [prefixWord, tailWord_1394247, baseEnd_1394247] using wordTrace_append hprefix tailTrace_1394247
  have hstable : (prefixWord ++ tailWord_1394247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394247).length < 2 ^ (prefixWord ++ tailWord_1394247).sum := by decide
  have hdescent : baseEnd_1394247 < baseStart_1394247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394289 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 6]
def baseStart_1394289 : Nat := 118140960795 + 1394289 * 2 ^ 59
def prefixEnd_1394289 : Nat := 4983230072969 + 3 ^ 40 * 1394289 * 2
def baseEnd_1394289 : Nat := 318195745900800254033461

theorem tailTrace_1394289 : CollatzResearch.WordTrace tailWord_1394289 prefixEnd_1394289 318195745900800254033461 := by
  unfold tailWord_1394289
  simp only [CollatzResearch.WordTrace]
  refine ⟨50853897645736553448161921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33902598430491035632107947 50853897645736553448161921)
  ·
    refine ⟨38140423234302415086121441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50853897645736553448161921 38140423234302415086121441)
    ·
      refine ⟨28605317425726811314591081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38140423234302415086121441 28605317425726811314591081)
      ·
        refine ⟨21453988069295108485943311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28605317425726811314591081 21453988069295108485943311)
        ·
          refine ⟨32180982103942662728914967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21453988069295108485943311 32180982103942662728914967)
          ·
            refine ⟨48271473155913994093372451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32180982103942662728914967 48271473155913994093372451)
            ·
              refine ⟨72407209733870991140058677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48271473155913994093372451 72407209733870991140058677)
              ·
                refine ⟨6788175912550405419380501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72407209733870991140058677 6788175912550405419380501)
                ·
                  refine ⟨318195745900800254033461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6788175912550405419380501 318195745900800254033461)
                  ·
                    rfl

theorem cell21_1394289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_1394289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394289 prefixEnd_1394289 := by exact prefixLift 1394289
  have htrace : WordTrace (prefixWord ++ tailWord_1394289) baseStart_1394289 baseEnd_1394289 := by
    simpa [prefixWord, tailWord_1394289, baseEnd_1394289] using wordTrace_append hprefix tailTrace_1394289
  have hstable : (prefixWord ++ tailWord_1394289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394289).length < 2 ^ (prefixWord ++ tailWord_1394289).sum := by decide
  have hdescent : baseEnd_1394289 < baseStart_1394289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394351 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 5]
def baseStart_1394351 : Nat := 118140960795 + 1394351 * 2 ^ 59
def prefixEnd_1394351 : Nat := 4983230072969 + 3 ^ 40 * 1394351 * 2
def baseEnd_1394351 : Nat := 318209895145501924000001

theorem tailTrace_1394351 : CollatzResearch.WordTrace tailWord_1394351 prefixEnd_1394351 318209895145501924000001 := by
  unfold tailWord_1394351
  simp only [CollatzResearch.WordTrace]
  refine ⟨50856158971511938036918907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33904105981007958691279271 50856158971511938036918907)
  ·
    refine ⟨76284238457267907055378361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50856158971511938036918907 76284238457267907055378361)
    ·
      refine ⟨57213178842950930291533771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76284238457267907055378361 57213178842950930291533771)
      ·
        refine ⟨85819768264426395437300657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57213178842950930291533771 85819768264426395437300657)
        ·
          refine ⟨64364826198319796577975493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85819768264426395437300657 64364826198319796577975493)
          ·
            refine ⟨12068404912184961858370405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64364826198319796577975493 12068404912184961858370405)
            ·
              refine ⟨2262825921034680348444451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12068404912184961858370405 2262825921034680348444451)
              ·
                refine ⟨3394238881552020522666677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262825921034680348444451 3394238881552020522666677)
                ·
                  refine ⟨318209895145501924000001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394238881552020522666677 318209895145501924000001)
                  ·
                    rfl

theorem cell21_1394351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 5].length) (baseStart_1394351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394351 prefixEnd_1394351 := by exact prefixLift 1394351
  have htrace : WordTrace (prefixWord ++ tailWord_1394351) baseStart_1394351 baseEnd_1394351 := by
    simpa [prefixWord, tailWord_1394351, baseEnd_1394351] using wordTrace_append hprefix tailTrace_1394351
  have hstable : (prefixWord ++ tailWord_1394351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394351).length < 2 ^ (prefixWord ++ tailWord_1394351).sum := by decide
  have hdescent : baseEnd_1394351 < baseStart_1394351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394385 : List Nat := [1, 2, 2, 1, 2, 6, 1, 3, 3]
def baseStart_1394385 : Nat := 118140960795 + 1394385 * 2 ^ 59
def prefixEnd_1394385 : Nat := 4983230072969 + 3 ^ 40 * 1394385 * 2
def baseEnd_1394385 : Nat := 318217654408725420433265

theorem tailTrace_1394385 : CollatzResearch.WordTrace tailWord_1394385 prefixEnd_1394385 318217654408725420433265 := by
  unfold tailWord_1394385
  simp only [CollatzResearch.WordTrace]
  refine ⟨50857399053388761843656609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33904932702259174562437739 50857399053388761843656609)
  ·
    refine ⟨38143049290041571382742457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50857399053388761843656609 38143049290041571382742457)
    ·
      refine ⟨28607286967531178537056843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38143049290041571382742457 28607286967531178537056843)
      ·
        refine ⟨42910930451296767805585265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28607286967531178537056843 42910930451296767805585265)
        ·
          refine ⟨32183197838472575854188949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42910930451296767805585265 32183197838472575854188949)
          ·
            refine ⟨1508587398678401993165107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32183197838472575854188949 1508587398678401993165107)
            ·
              refine ⟨2262881098017602989747661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508587398678401993165107 2262881098017602989747661)
              ·
                refine ⟨848580411756601121155373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2262881098017602989747661 848580411756601121155373)
                ·
                  refine ⟨318217654408725420433265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848580411756601121155373 318217654408725420433265)
                  ·
                    rfl

theorem cell21_1394385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 3].length) (baseStart_1394385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394385 prefixEnd_1394385 := by exact prefixLift 1394385
  have htrace : WordTrace (prefixWord ++ tailWord_1394385) baseStart_1394385 baseEnd_1394385 := by
    simpa [prefixWord, tailWord_1394385, baseEnd_1394385] using wordTrace_append hprefix tailTrace_1394385
  have hstable : (prefixWord ++ tailWord_1394385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394385).length < 2 ^ (prefixWord ++ tailWord_1394385).sum := by decide
  have hdescent : baseEnd_1394385 < baseStart_1394385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394413 : List Nat := [1, 5, 1, 2, 1, 3, 2, 6]
def baseStart_1394413 : Nat := 118140960795 + 1394413 * 2 ^ 59
def prefixEnd_1394413 : Nat := 4983230072969 + 3 ^ 40 * 1394413 * 2
def baseEnd_1394413 : Nat := 106074681463401197988847

theorem tailTrace_1394413 : CollatzResearch.WordTrace tailWord_1394413 prefixEnd_1394413 106074681463401197988847 := by
  unfold tailWord_1394413
  simp only [CollatzResearch.WordTrace]
  refine ⟨50858420297287322625675893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33905613531524881750450595 50858420297287322625675893)
  ·
    refine ⟨4767976902870686496157115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50858420297287322625675893 4767976902870686496157115)
    ·
      refine ⟨7151965354306029744235673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4767976902870686496157115 7151965354306029744235673)
      ·
        refine ⟨5363974015729522308176755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7151965354306029744235673 5363974015729522308176755)
        ·
          refine ⟨8045961023594283462265133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363974015729522308176755 8045961023594283462265133)
          ·
            refine ⟨3017235383847856298349425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8045961023594283462265133 3017235383847856298349425)
            ·
              refine ⟨2262926537885892223762069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3017235383847856298349425 2262926537885892223762069)
              ·
                refine ⟨106074681463401197988847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2262926537885892223762069 106074681463401197988847)
                ·
                  rfl

theorem cell21_1394413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 6].length) (baseStart_1394413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394413 prefixEnd_1394413 := by exact prefixLift 1394413
  have htrace : WordTrace (prefixWord ++ tailWord_1394413) baseStart_1394413 baseEnd_1394413 := by
    simpa [prefixWord, tailWord_1394413, baseEnd_1394413] using wordTrace_append hprefix tailTrace_1394413
  have hstable : (prefixWord ++ tailWord_1394413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394413).length < 2 ^ (prefixWord ++ tailWord_1394413).sum := by decide
  have hdescent : baseEnd_1394413 < baseStart_1394413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394458 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_1394458 : Nat := 118140960795 + 1394458 * 2 ^ 59
def prefixEnd_1394458 : Nat := 4983230072969 + 3 ^ 40 * 1394458 * 2
def baseEnd_1394458 : Nat := 318234314003293515716449

theorem tailTrace_1394458 : CollatzResearch.WordTrace tailWord_1394458 prefixEnd_1394458 318234314003293515716449 := by
  unfold tailWord_1394458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12715015395531073827766007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33906707721416196874042685 12715015395531073827766007)
  ·
    refine ⟨19072523093296610741649011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12715015395531073827766007 19072523093296610741649011)
    ·
      refine ⟨28608784639944916112473517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19072523093296610741649011 28608784639944916112473517)
      ·
        refine ⟨10728294239979343542177569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28608784639944916112473517 10728294239979343542177569)
        ·
          refine ⟨8046220679984507656633177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10728294239979343542177569 8046220679984507656633177)
          ·
            refine ⟨6034665509988380742474883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8046220679984507656633177 6034665509988380742474883)
            ·
              refine ⟨9051998264982571113712325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034665509988380742474883 9051998264982571113712325)
              ·
                refine ⟨1697249674684232083821061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9051998264982571113712325 1697249674684232083821061)
                ·
                  refine ⟨318234314003293515716449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1697249674684232083821061 318234314003293515716449)
                  ·
                    rfl

theorem cell21_1394458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_1394458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394458 prefixEnd_1394458 := by exact prefixLift 1394458
  have htrace : WordTrace (prefixWord ++ tailWord_1394458) baseStart_1394458 baseEnd_1394458 := by
    simpa [prefixWord, tailWord_1394458, baseEnd_1394458] using wordTrace_append hprefix tailTrace_1394458
  have hstable : (prefixWord ++ tailWord_1394458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394458).length < 2 ^ (prefixWord ++ tailWord_1394458).sum := by decide
  have hdescent : baseEnd_1394458 < baseStart_1394458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394607 : List Nat := [1, 1, 2, 1, 2, 2, 3, 9]
def baseStart_1394607 : Nat := 118140960795 + 1394607 * 2 ^ 59
def prefixEnd_1394607 : Nat := 4983230072969 + 3 ^ 40 * 1394607 * 2
def baseEnd_1394607 : Nat := 106089439277767455910937

theorem tailTrace_1394607 : CollatzResearch.WordTrace tailWord_1394607 prefixEnd_1394607 106089439277767455910937 := by
  unfold tailWord_1394607
  simp only [CollatzResearch.WordTrace]
  refine ⟨50865496058584493758238075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33910330705722995838825383 50865496058584493758238075)
  ·
    refine ⟨76298244087876740637357113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50865496058584493758238075 76298244087876740637357113)
    ·
      refine ⟨57223683065907555478017835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76298244087876740637357113 57223683065907555478017835)
      ·
        refine ⟨85835524598861333217026753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57223683065907555478017835 85835524598861333217026753)
        ·
          refine ⟨64376643449145999912770065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85835524598861333217026753 64376643449145999912770065)
          ·
            refine ⟨48282482586859499934577549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64376643449145999912770065 48282482586859499934577549)
            ·
              refine ⟨18105930970072312475466581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48282482586859499934577549 18105930970072312475466581)
              ·
                refine ⟨106089439277767455910937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18105930970072312475466581 106089439277767455910937)
                ·
                  rfl

theorem cell21_1394607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 9].length) (baseStart_1394607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394607 prefixEnd_1394607 := by exact prefixLift 1394607
  have htrace : WordTrace (prefixWord ++ tailWord_1394607) baseStart_1394607 baseEnd_1394607 := by
    simpa [prefixWord, tailWord_1394607, baseEnd_1394607] using wordTrace_append hprefix tailTrace_1394607
  have hstable : (prefixWord ++ tailWord_1394607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394607).length < 2 ^ (prefixWord ++ tailWord_1394607).sum := by decide
  have hdescent : baseEnd_1394607 < baseStart_1394607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394655 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 5]
def baseStart_1394655 : Nat := 118140960795 + 1394655 * 2 ^ 59
def prefixEnd_1394655 : Nat := 4983230072969 + 3 ^ 40 * 1394655 * 2
def baseEnd_1394655 : Nat := 318279272087264950932713

theorem tailTrace_1394655 : CollatzResearch.WordTrace tailWord_1394655 prefixEnd_1394655 318279272087264950932713 := by
  unfold tailWord_1394655
  simp only [CollatzResearch.WordTrace]
  refine ⟨50867246762410597955985419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33911497841607065303990279 50867246762410597955985419)
  ·
    refine ⟨76300870143615896933978129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50867246762410597955985419 76300870143615896933978129)
    ·
      refine ⟨57225652607711922700483597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76300870143615896933978129 57225652607711922700483597)
      ·
        refine ⟨21459619727891971012681349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57225652607711922700483597 21459619727891971012681349)
        ·
          refine ⟨4023678698979744564877753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21459619727891971012681349 4023678698979744564877753)
          ·
            refine ⟨3017759024234808423658315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4023678698979744564877753 3017759024234808423658315)
            ·
              refine ⟨4526638536352212635487473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017759024234808423658315 4526638536352212635487473)
              ·
                refine ⟨3394978902264159476615605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4526638536352212635487473 3394978902264159476615605)
                ·
                  refine ⟨318279272087264950932713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394978902264159476615605 318279272087264950932713)
                  ·
                    rfl

theorem cell21_1394655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 5].length) (baseStart_1394655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394655 prefixEnd_1394655 := by exact prefixLift 1394655
  have htrace : WordTrace (prefixWord ++ tailWord_1394655) baseStart_1394655 baseEnd_1394655 := by
    simpa [prefixWord, tailWord_1394655, baseEnd_1394655] using wordTrace_append hprefix tailTrace_1394655
  have hstable : (prefixWord ++ tailWord_1394655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394655).length < 2 ^ (prefixWord ++ tailWord_1394655).sum := by decide
  have hdescent : baseEnd_1394655 < baseStart_1394655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394717 : List Nat := [1, 4, 2, 2, 2, 1, 4, 5]
def baseStart_1394717 : Nat := 118140960795 + 1394717 * 2 ^ 59
def prefixEnd_1394717 : Nat := 4983230072969 + 3 ^ 40 * 1394717 * 2
def baseEnd_1394717 : Nat := 106097807110655540299751

theorem tailTrace_1394717 : CollatzResearch.WordTrace tailWord_1394717 prefixEnd_1394717 106097807110655540299751 := by
  unfold tailWord_1394717
  simp only [CollatzResearch.WordTrace]
  refine ⟨50869508088185982544742405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33913005392123988363161603 50869508088185982544742405)
  ·
    refine ⟨9538032766534871727139201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50869508088185982544742405 9538032766534871727139201)
    ·
      refine ⟨7153524574901153795354401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9538032766534871727139201 7153524574901153795354401)
      ·
        refine ⟨5365143431175865346515801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7153524574901153795354401 5365143431175865346515801)
        ·
          refine ⟨4023857573381899009886851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5365143431175865346515801 4023857573381899009886851)
          ·
            refine ⟨6035786360072848514830277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023857573381899009886851 6035786360072848514830277)
            ·
              refine ⟨1131709942513659096530677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6035786360072848514830277 1131709942513659096530677)
              ·
                refine ⟨106097807110655540299751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1131709942513659096530677 106097807110655540299751)
                ·
                  rfl

theorem cell21_1394717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 5].length) (baseStart_1394717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394717 prefixEnd_1394717 := by exact prefixLift 1394717
  have htrace : WordTrace (prefixWord ++ tailWord_1394717) baseStart_1394717 baseEnd_1394717 := by
    simpa [prefixWord, tailWord_1394717, baseEnd_1394717] using wordTrace_append hprefix tailTrace_1394717
  have hstable : (prefixWord ++ tailWord_1394717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394717).length < 2 ^ (prefixWord ++ tailWord_1394717).sum := by decide
  have hdescent : baseEnd_1394717 < baseStart_1394717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394731 : List Nat := [1, 1, 1, 1, 2, 1, 4, 7, 3]
def baseStart_1394731 : Nat := 118140960795 + 1394731 * 2 ^ 59
def prefixEnd_1394731 : Nat := 4983230072969 + 3 ^ 40 * 1394731 * 2
def baseEnd_1394731 : Nat := 318296616322705707665891

theorem tailTrace_1394731 : CollatzResearch.WordTrace tailWord_1394731 prefixEnd_1394731 318296616322705707665891 := by
  unfold tailWord_1394731
  simp only [CollatzResearch.WordTrace]
  refine ⟨50870018710135262935752047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33913345806756841957168031 50870018710135262935752047)
  ·
    refine ⟨76305028065202894403628071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50870018710135262935752047 76305028065202894403628071)
    ·
      refine ⟨114457542097804341605442107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76305028065202894403628071 114457542097804341605442107)
      ·
        refine ⟨171686313146706512408163161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114457542097804341605442107 171686313146706512408163161)
        ·
          refine ⟨128764734860029884306122371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171686313146706512408163161 128764734860029884306122371)
          ·
            refine ⟨193147102290044826459183557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128764734860029884306122371 193147102290044826459183557)
            ·
              refine ⟨36215081679383404961096917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193147102290044826459183557 36215081679383404961096917)
              ·
                refine ⟨848790976860548553775709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36215081679383404961096917 848790976860548553775709)
                ·
                  refine ⟨318296616322705707665891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848790976860548553775709 318296616322705707665891)
                  ·
                    rfl

theorem cell21_1394731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 3].length) (baseStart_1394731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394731 prefixEnd_1394731 := by exact prefixLift 1394731
  have htrace : WordTrace (prefixWord ++ tailWord_1394731) baseStart_1394731 baseEnd_1394731 := by
    simpa [prefixWord, tailWord_1394731, baseEnd_1394731] using wordTrace_append hprefix tailTrace_1394731
  have hstable : (prefixWord ++ tailWord_1394731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394731).length < 2 ^ (prefixWord ++ tailWord_1394731).sum := by decide
  have hdescent : baseEnd_1394731 < baseStart_1394731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394852 : List Nat := [2, 3, 1, 2, 4, 1, 8]
def baseStart_1394852 : Nat := 118140960795 + 1394852 * 2 ^ 59
def prefixEnd_1394852 : Nat := 4983230072969 + 3 ^ 40 * 1394852 * 2
def baseEnd_1394852 : Nat := 35369358907915154016553

theorem tailTrace_1394852 : CollatzResearch.WordTrace tailWord_1394852 prefixEnd_1394852 35369358907915154016553 := by
  unfold tailWord_1394852
  simp only [CollatzResearch.WordTrace]
  refine ⟨25437215971348450300453405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33916287961797933733937873 25437215971348450300453405)
  ·
    refine ⟨9538955989255668862670027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25437215971348450300453405 9538955989255668862670027)
    ·
      refine ⟨14308433983883503294005041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9538955989255668862670027 14308433983883503294005041)
      ·
        refine ⟨10731325487912627470503781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14308433983883503294005041 10731325487912627470503781)
        ·
          refine ⟨2012123528983617650719459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10731325487912627470503781 2012123528983617650719459)
          ·
            refine ⟨3018185293475426476079189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012123528983617650719459 3018185293475426476079189)
            ·
              refine ⟨35369358907915154016553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3018185293475426476079189 35369358907915154016553)
              ·
                rfl

theorem cell21_1394852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 8].length) (baseStart_1394852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394852 prefixEnd_1394852 := by exact prefixLift 1394852
  have htrace : WordTrace (prefixWord ++ tailWord_1394852) baseStart_1394852 baseEnd_1394852 := by
    simpa [prefixWord, tailWord_1394852, baseEnd_1394852] using wordTrace_append hprefix tailTrace_1394852
  have hstable : (prefixWord ++ tailWord_1394852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394852).length < 2 ^ (prefixWord ++ tailWord_1394852).sum := by decide
  have hdescent : baseEnd_1394852 < baseStart_1394852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394917 : List Nat := [1, 3, 1, 4, 2, 2, 3, 2, 3]
def baseStart_1394917 : Nat := 118140960795 + 1394917 * 2 ^ 59
def prefixEnd_1394917 : Nat := 4983230072969 + 3 ^ 40 * 1394917 * 2
def baseEnd_1394917 : Nat := 318339064056810717565511

theorem tailTrace_1394917 : CollatzResearch.WordTrace tailWord_1394917 prefixEnd_1394917 318339064056810717565511 := by
  unfold tailWord_1394917
  simp only [CollatzResearch.WordTrace]
  refine ⟨50876802687461416702023005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33917868458307611134682003 50876802687461416702023005)
  ·
    refine ⟨19078801007798031263258627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50876802687461416702023005 19078801007798031263258627)
    ·
      refine ⟨28618201511697046894887941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19078801007798031263258627 28618201511697046894887941)
      ·
        refine ⟨5365912783443196292791489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28618201511697046894887941 5365912783443196292791489)
        ·
          refine ⟨4024434587582397219593617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5365912783443196292791489 4024434587582397219593617)
          ·
            refine ⟨3018325940686797914695213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4024434587582397219593617 3018325940686797914695213)
            ·
              refine ⟨1131872227757549218010705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3018325940686797914695213 1131872227757549218010705)
              ·
                refine ⟨848904170818161913508029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131872227757549218010705 848904170818161913508029)
                ·
                  refine ⟨318339064056810717565511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848904170818161913508029 318339064056810717565511)
                  ·
                    rfl

theorem cell21_1394917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_1394917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394917 prefixEnd_1394917 := by exact prefixLift 1394917
  have htrace : WordTrace (prefixWord ++ tailWord_1394917) baseStart_1394917 baseEnd_1394917 := by
    simpa [prefixWord, tailWord_1394917, baseEnd_1394917] using wordTrace_append hprefix tailTrace_1394917
  have hstable : (prefixWord ++ tailWord_1394917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394917).length < 2 ^ (prefixWord ++ tailWord_1394917).sum := by decide
  have hdescent : baseEnd_1394917 < baseStart_1394917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394976 : List Nat := [2, 1, 1, 5, 2, 2, 1, 4, 3]
def baseStart_1394976 : Nat := 118140960795 + 1394976 * 2 ^ 59
def prefixEnd_1394976 : Nat := 4983230072969 + 3 ^ 40 * 1394976 * 2
def baseEnd_1394976 : Nat := 318352528660639726082057

theorem tailTrace_1394976 : CollatzResearch.WordTrace tailWord_1394976 prefixEnd_1394976 318352528660639726082057 := by
  unfold tailWord_1394976
  simp only [CollatzResearch.WordTrace]
  refine ⟨25439477297123834889210391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33919303062831779852280521 25439477297123834889210391)
  ·
    refine ⟨38159215945685752333815587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25439477297123834889210391 38159215945685752333815587)
    ·
      refine ⟨57238823918528628500723381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38159215945685752333815587 57238823918528628500723381)
      ·
        refine ⟨5366139742362058921942817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57238823918528628500723381 5366139742362058921942817)
        ·
          refine ⟨4024604806771544191457113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5366139742362058921942817 4024604806771544191457113)
          ·
            refine ⟨3018453605078658143592835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4024604806771544191457113 3018453605078658143592835)
            ·
              refine ⟨4527680407617987215389253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018453605078658143592835 4527680407617987215389253)
              ·
                refine ⟨848940076428372602885485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4527680407617987215389253 848940076428372602885485)
                ·
                  refine ⟨318352528660639726082057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848940076428372602885485 318352528660639726082057)
                  ·
                    rfl

theorem cell21_1394976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 3].length) (baseStart_1394976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1394976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1394976 prefixEnd_1394976 := by exact prefixLift 1394976
  have htrace : WordTrace (prefixWord ++ tailWord_1394976) baseStart_1394976 baseEnd_1394976 := by
    simpa [prefixWord, tailWord_1394976, baseEnd_1394976] using wordTrace_append hprefix tailTrace_1394976
  have hstable : (prefixWord ++ tailWord_1394976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394976).length < 2 ^ (prefixWord ++ tailWord_1394976).sum := by decide
  have hdescent : baseEnd_1394976 < baseStart_1394976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395004 : List Nat := [2, 2, 2, 2, 1, 2, 5, 5]
def baseStart_1395004 : Nat := 118140960795 + 1395004 * 2 ^ 59
def prefixEnd_1395004 : Nat := 4983230072969 + 3 ^ 40 * 1395004 * 2
def baseEnd_1395004 : Nat := 106119639547372633205111

theorem tailTrace_1395004 : CollatzResearch.WordTrace tailWord_1395004 prefixEnd_1395004 106119639547372633205111 := by
  unfold tailWord_1395004
  simp only [CollatzResearch.WordTrace]
  refine ⟨25439987919073115280220033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33919983892097487040293377 25439987919073115280220033)
  ·
    refine ⟨19079990939304836460165025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25439987919073115280220033 19079990939304836460165025)
    ·
      refine ⟨14309993204478627345123769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19079990939304836460165025 14309993204478627345123769)
      ·
        refine ⟨10732494903358970508842827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14309993204478627345123769 10732494903358970508842827)
        ·
          refine ⟨16098742355038455763264241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10732494903358970508842827 16098742355038455763264241)
          ·
            refine ⟨12074056766278841822448181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16098742355038455763264241 12074056766278841822448181)
            ·
              refine ⟨1131942821838641420854517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12074056766278841822448181 1131942821838641420854517)
              ·
                refine ⟨106119639547372633205111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1131942821838641420854517 106119639547372633205111)
                ·
                  rfl

theorem cell21_1395004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_1395004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395004 prefixEnd_1395004 := by exact prefixLift 1395004
  have htrace : WordTrace (prefixWord ++ tailWord_1395004) baseStart_1395004 baseEnd_1395004 := by
    simpa [prefixWord, tailWord_1395004, baseEnd_1395004] using wordTrace_append hprefix tailTrace_1395004
  have hstable : (prefixWord ++ tailWord_1395004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395004).length < 2 ^ (prefixWord ++ tailWord_1395004).sum := by decide
  have hdescent : baseEnd_1395004 < baseStart_1395004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395153 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 9]
def baseStart_1395153 : Nat := 118140960795 + 1395153 * 2 ^ 59
def prefixEnd_1395153 : Nat := 4983230072969 + 3 ^ 40 * 1395153 * 2
def baseEnd_1395153 : Nat := 318392922472126751631695

theorem tailTrace_1395153 : CollatzResearch.WordTrace tailWord_1395153 prefixEnd_1395153 318392922472126751631695 := by
  unfold tailWord_1395153
  simp only [CollatzResearch.WordTrace]
  refine ⟨50885410314606429007614113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33923606876404286005076075 50885410314606429007614113)
  ·
    refine ⟨38164057735954821755710585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50885410314606429007614113 38164057735954821755710585)
    ·
      refine ⟨28623043301966116316782939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38164057735954821755710585 28623043301966116316782939)
      ·
        refine ⟨42934564952949174475174409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28623043301966116316782939 42934564952949174475174409)
        ·
          refine ⟨32200923714711880856380807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42934564952949174475174409 32200923714711880856380807)
          ·
            refine ⟨48301385572067821284571211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32200923714711880856380807 48301385572067821284571211)
            ·
              refine ⟨72452078358101731926856817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48301385572067821284571211 72452078358101731926856817)
              ·
                refine ⟨54339058768576298945142613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72452078358101731926856817 54339058768576298945142613)
                ·
                  refine ⟨318392922472126751631695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54339058768576298945142613 318392922472126751631695)
                  ·
                    rfl

theorem cell21_1395153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_1395153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395153 prefixEnd_1395153 := by exact prefixLift 1395153
  have htrace : WordTrace (prefixWord ++ tailWord_1395153) baseStart_1395153 baseEnd_1395153 := by
    simpa [prefixWord, tailWord_1395153, baseEnd_1395153] using wordTrace_append hprefix tailTrace_1395153
  have hstable : (prefixWord ++ tailWord_1395153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395153).length < 2 ^ (prefixWord ++ tailWord_1395153).sum := by decide
  have hdescent : baseEnd_1395153 < baseStart_1395153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395156 : List Nat := [2, 4, 1, 2, 2, 1, 3, 6]
def baseStart_1395156 : Nat := 118140960795 + 1395156 * 2 ^ 59
def prefixEnd_1395156 : Nat := 4983230072969 + 3 ^ 40 * 1395156 * 2
def baseEnd_1395156 : Nat := 106131202370999804360563

theorem tailTrace_1395156 : CollatzResearch.WordTrace tailWord_1395156 prefixEnd_1395156 106131202370999804360563 := by
  unfold tailWord_1395156
  simp only [CollatzResearch.WordTrace]
  refine ⟨25442759866797780259986661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33923679822397040346648881 25442759866797780259986661)
  ·
    refine ⟨4770517475024583798747499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25442759866797780259986661 4770517475024583798747499)
    ·
      refine ⟨7155776212536875698121249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4770517475024583798747499 7155776212536875698121249)
      ·
        refine ⟨5366832159402656773590937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7155776212536875698121249 5366832159402656773590937)
        ·
          refine ⟨4025124119551992580193203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5366832159402656773590937 4025124119551992580193203)
          ·
            refine ⟨6037686179327988870289805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025124119551992580193203 6037686179327988870289805)
            ·
              refine ⟨2264132317247995826358677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6037686179327988870289805 2264132317247995826358677)
              ·
                refine ⟨106131202370999804360563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2264132317247995826358677 106131202370999804360563)
                ·
                  rfl

theorem cell21_1395156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_1395156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395156 prefixEnd_1395156 := by exact prefixLift 1395156
  have htrace : WordTrace (prefixWord ++ tailWord_1395156) baseStart_1395156 baseEnd_1395156 := by
    simpa [prefixWord, tailWord_1395156, baseEnd_1395156] using wordTrace_append hprefix tailTrace_1395156
  have hstable : (prefixWord ++ tailWord_1395156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395156).length < 2 ^ (prefixWord ++ tailWord_1395156).sum := by decide
  have hdescent : baseEnd_1395156 < baseStart_1395156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395173 : List Nat := [1, 3, 1, 5, 2, 1, 3, 5]
def baseStart_1395173 : Nat := 118140960795 + 1395173 * 2 ^ 59
def prefixEnd_1395173 : Nat := 4983230072969 + 3 ^ 40 * 1395173 * 2
def baseEnd_1395173 : Nat := 106132495581537053766107

theorem tailTrace_1395173 : CollatzResearch.WordTrace tailWord_1395173 prefixEnd_1395173 106132495581537053766107 := by
  unfold tailWord_1395173
  simp only [CollatzResearch.WordTrace]
  refine ⟨50886139774533972423342173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33924093183022648282228115 50886139774533972423342173)
  ·
    refine ⟨19082302415450239658753315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50886139774533972423342173 19082302415450239658753315)
    ·
      refine ⟨28623453623175359488129973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19082302415450239658753315 28623453623175359488129973)
      ·
        refine ⟨2683448777172689952012185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28623453623175359488129973 2683448777172689952012185)
        ·
          refine ⟨2012586582879517464009139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2683448777172689952012185 2012586582879517464009139)
          ·
            refine ⟨3018879874319276196013709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012586582879517464009139 3018879874319276196013709)
            ·
              refine ⟨1132079952869728573505141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3018879874319276196013709 1132079952869728573505141)
              ·
                refine ⟨106132495581537053766107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1132079952869728573505141 106132495581537053766107)
                ·
                  rfl

theorem cell21_1395173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 5].length) (baseStart_1395173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395173 prefixEnd_1395173 := by exact prefixLift 1395173
  have htrace : WordTrace (prefixWord ++ tailWord_1395173) baseStart_1395173 baseEnd_1395173 := by
    simpa [prefixWord, tailWord_1395173, baseEnd_1395173] using wordTrace_append hprefix tailTrace_1395173
  have hstable : (prefixWord ++ tailWord_1395173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395173).length < 2 ^ (prefixWord ++ tailWord_1395173).sum := by decide
  have hdescent : baseEnd_1395173 < baseStart_1395173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395184 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_1395184 : Nat := 118140960795 + 1395184 * 2 ^ 59
def prefixEnd_1395184 : Nat := 4983230072969 + 3 ^ 40 * 1395184 * 2
def baseEnd_1395184 : Nat := 318399997094477586614965

theorem tailTrace_1395184 : CollatzResearch.WordTrace tailWord_1395184 prefixEnd_1395184 318399997094477586614965 := by
  unfold tailWord_1395184
  simp only [CollatzResearch.WordTrace]
  refine ⟨25443270488747060650996303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33924360651662747534661737 25443270488747060650996303)
  ·
    refine ⟨38164905733120590976494455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25443270488747060650996303 38164905733120590976494455)
    ·
      refine ⟨57247358599680886464741683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38164905733120590976494455 57247358599680886464741683)
      ·
        refine ⟨85871037899521329697112525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57247358599680886464741683 85871037899521329697112525)
        ·
          refine ⟨32201639212320498636417197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85871037899521329697112525 32201639212320498636417197)
          ·
            refine ⟨12075614704620186988656449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32201639212320498636417197 12075614704620186988656449)
            ·
              refine ⟨9056711028465140241492337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12075614704620186988656449 9056711028465140241492337)
              ·
                refine ⟨6792533271348855181119253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9056711028465140241492337 6792533271348855181119253)
                ·
                  refine ⟨318399997094477586614965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6792533271348855181119253 318399997094477586614965)
                  ·
                    rfl

theorem cell21_1395184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_1395184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395184 prefixEnd_1395184 := by exact prefixLift 1395184
  have htrace : WordTrace (prefixWord ++ tailWord_1395184) baseStart_1395184 baseEnd_1395184 := by
    simpa [prefixWord, tailWord_1395184, baseEnd_1395184] using wordTrace_append hprefix tailTrace_1395184
  have hstable : (prefixWord ++ tailWord_1395184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395184).length < 2 ^ (prefixWord ++ tailWord_1395184).sum := by decide
  have hdescent : baseEnd_1395184 < baseStart_1395184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395187 : List Nat := [1, 1, 1, 2, 2, 2, 6, 3, 3]
def baseStart_1395187 : Nat := 118140960795 + 1395187 * 2 ^ 59
def prefixEnd_1395187 : Nat := 4983230072969 + 3 ^ 40 * 1395187 * 2
def baseEnd_1395187 : Nat := 318400681735350248064959

theorem tailTrace_1395187 : CollatzResearch.WordTrace tailWord_1395187 prefixEnd_1395187 318400681735350248064959 := by
  unfold tailWord_1395187
  simp only [CollatzResearch.WordTrace]
  refine ⟨50886650396483252814351815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33924433597655501876234543 50886650396483252814351815)
  ·
    refine ⟨76329975594724879221527723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50886650396483252814351815 76329975594724879221527723)
    ·
      refine ⟨114494963392087318832291585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76329975594724879221527723 114494963392087318832291585)
      ·
        refine ⟨85871222544065489124218689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114494963392087318832291585 85871222544065489124218689)
        ·
          refine ⟨64403416908049116843164017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85871222544065489124218689 64403416908049116843164017)
          ·
            refine ⟨48302562681036837632373013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64403416908049116843164017 48302562681036837632373013)
            ·
              refine ⟨2264182625673601764017485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48302562681036837632373013 2264182625673601764017485)
              ·
                refine ⟨849068484627600661506557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2264182625673601764017485 849068484627600661506557)
                ·
                  refine ⟨318400681735350248064959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849068484627600661506557 318400681735350248064959)
                  ·
                    rfl

theorem cell21_1395187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 3].length) (baseStart_1395187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395187 prefixEnd_1395187 := by exact prefixLift 1395187
  have htrace : WordTrace (prefixWord ++ tailWord_1395187) baseStart_1395187 baseEnd_1395187 := by
    simpa [prefixWord, tailWord_1395187, baseEnd_1395187] using wordTrace_append hprefix tailTrace_1395187
  have hstable : (prefixWord ++ tailWord_1395187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395187).length < 2 ^ (prefixWord ++ tailWord_1395187).sum := by decide
  have hdescent : baseEnd_1395187 < baseStart_1395187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395201 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 6]
def baseStart_1395201 : Nat := 118140960795 + 1395201 * 2 ^ 59
def prefixEnd_1395201 : Nat := 4983230072969 + 3 ^ 40 * 1395201 * 2
def baseEnd_1395201 : Nat := 318403876726089334831597

theorem tailTrace_1395201 : CollatzResearch.WordTrace tailWord_1395201 prefixEnd_1395201 318403876726089334831597 := by
  unfold tailWord_1395201
  simp only [CollatzResearch.WordTrace]
  refine ⟨50887161018432533205361457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33924774012288355470240971 50887161018432533205361457)
  ·
    refine ⟨38165370763824399904021093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50887161018432533205361457 38165370763824399904021093)
    ·
      refine ⟨7156007018217074982003955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38165370763824399904021093 7156007018217074982003955)
      ·
        refine ⟨10734010527325612473005933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7156007018217074982003955 10734010527325612473005933)
        ·
          refine ⟨4025253947747104677377225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10734010527325612473005933 4025253947747104677377225)
          ·
            refine ⟨3018940460810328508032919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4025253947747104677377225 3018940460810328508032919)
            ·
              refine ⟨4528410691215492762049379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018940460810328508032919 4528410691215492762049379)
              ·
                refine ⟨6792616036823239143074069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528410691215492762049379 6792616036823239143074069)
                ·
                  refine ⟨318403876726089334831597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6792616036823239143074069 318403876726089334831597)
                  ·
                    rfl

theorem cell21_1395201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_1395201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395201 prefixEnd_1395201 := by exact prefixLift 1395201
  have htrace : WordTrace (prefixWord ++ tailWord_1395201) baseStart_1395201 baseEnd_1395201 := by
    simpa [prefixWord, tailWord_1395201, baseEnd_1395201] using wordTrace_append hprefix tailTrace_1395201
  have hstable : (prefixWord ++ tailWord_1395201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395201).length < 2 ^ (prefixWord ++ tailWord_1395201).sum := by decide
  have hdescent : baseEnd_1395201 < baseStart_1395201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395204 : List Nat := [2, 3, 2, 3, 1, 1, 2, 4, 3]
def baseStart_1395204 : Nat := 118140960795 + 1395204 * 2 ^ 59
def prefixEnd_1395204 : Nat := 4983230072969 + 3 ^ 40 * 1395204 * 2
def baseEnd_1395204 : Nat := 318404561366961996281591

theorem tailTrace_1395204 : CollatzResearch.WordTrace tailWord_1395204 prefixEnd_1395204 318404561366961996281591 := by
  unfold tailWord_1395204
  simp only [CollatzResearch.WordTrace]
  refine ⟨25443635218710832358860333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33924846958281109811813777 25443635218710832358860333)
  ·
    refine ⟨9541363207016562134572625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25443635218710832358860333 9541363207016562134572625)
    ·
      refine ⟨7156022405262421600929469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9541363207016562134572625 7156022405262421600929469)
      ·
        refine ⟨2683508401973408100348551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7156022405262421600929469 2683508401973408100348551)
        ·
          refine ⟨4025262602960112150522827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683508401973408100348551 4025262602960112150522827)
          ·
            refine ⟨6037893904440168225784241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025262602960112150522827 6037893904440168225784241)
            ·
              refine ⟨4528420428330126169338181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6037893904440168225784241 4528420428330126169338181)
              ·
                refine ⟨849078830311898656750909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4528420428330126169338181 849078830311898656750909)
                ·
                  refine ⟨318404561366961996281591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849078830311898656750909 318404561366961996281591)
                  ·
                    rfl

theorem cell21_1395204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_1395204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395204 prefixEnd_1395204 := by exact prefixLift 1395204
  have htrace : WordTrace (prefixWord ++ tailWord_1395204) baseStart_1395204 baseEnd_1395204 := by
    simpa [prefixWord, tailWord_1395204, baseEnd_1395204] using wordTrace_append hprefix tailTrace_1395204
  have hstable : (prefixWord ++ tailWord_1395204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395204).length < 2 ^ (prefixWord ++ tailWord_1395204).sum := by decide
  have hdescent : baseEnd_1395204 < baseStart_1395204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395232 : List Nat := [2, 1, 1, 6, 2, 1, 1, 7]
def baseStart_1395232 : Nat := 118140960795 + 1395232 * 2 ^ 59
def prefixEnd_1395232 : Nat := 4983230072969 + 3 ^ 40 * 1395232 * 2
def baseEnd_1395232 : Nat := 106136983782813389938289

theorem tailTrace_1395232 : CollatzResearch.WordTrace tailWord_1395232 prefixEnd_1395232 106136983782813389938289 := by
  unfold tailWord_1395232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25444145840660112749869975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33925527787546816999826633 25444145840660112749869975)
  ·
    refine ⟨38166218760990169124804963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25444145840660112749869975 38166218760990169124804963)
    ·
      refine ⟨57249328141485253687207445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38166218760990169124804963 57249328141485253687207445)
      ·
        refine ⟨2683562256632121266587849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57249328141485253687207445 2683562256632121266587849)
        ·
          refine ⟨2012671692474090949940887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2683562256632121266587849 2012671692474090949940887)
          ·
            refine ⟨3019007538711136424911331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012671692474090949940887 3019007538711136424911331)
            ·
              refine ⟨4528511308066704637366997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3019007538711136424911331 4528511308066704637366997)
              ·
                refine ⟨106136983782813389938289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4528511308066704637366997 106136983782813389938289)
                ·
                  rfl

theorem cell21_1395232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_1395232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395232 prefixEnd_1395232 := by exact prefixLift 1395232
  have htrace : WordTrace (prefixWord ++ tailWord_1395232) baseStart_1395232 baseEnd_1395232 := by
    simpa [prefixWord, tailWord_1395232, baseEnd_1395232] using wordTrace_append hprefix tailTrace_1395232
  have hstable : (prefixWord ++ tailWord_1395232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395232).length < 2 ^ (prefixWord ++ tailWord_1395232).sum := by decide
  have hdescent : baseEnd_1395232 < baseStart_1395232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395314 : List Nat := [3, 2, 1, 2, 5, 1, 2, 2, 3]
def baseStart_1395314 : Nat := 118140960795 + 1395314 * 2 ^ 59
def prefixEnd_1395314 : Nat := 4983230072969 + 3 ^ 40 * 1395314 * 2
def baseEnd_1395314 : Nat := 318429664865626249448033

theorem tailTrace_1395314 : CollatzResearch.WordTrace tailWord_1395314 prefixEnd_1395314 318429664865626249448033 := by
  unfold tailWord_1395314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12722820616755788376056249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33927521644682102336149997 12722820616755788376056249)
  ·
    refine ⟨9542115462566841282042187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12722820616755788376056249 9542115462566841282042187)
    ·
      refine ⟨14313173193850261923063281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9542115462566841282042187 14313173193850261923063281)
      ·
        refine ⟨10734879895387696442297461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14313173193850261923063281 10734879895387696442297461)
        ·
          refine ⟨1006394990192596541465387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10734879895387696442297461 1006394990192596541465387)
          ·
            refine ⟨1509592485288894812198081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006394990192596541465387 1509592485288894812198081)
            ·
              refine ⟨1132194363966671109148561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1509592485288894812198081 1132194363966671109148561)
              ·
                refine ⟨849145772975003331861421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1132194363966671109148561 849145772975003331861421)
                ·
                  refine ⟨318429664865626249448033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849145772975003331861421 318429664865626249448033)
                  ·
                    rfl

theorem cell21_1395314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_1395314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395314 prefixEnd_1395314 := by exact prefixLift 1395314
  have htrace : WordTrace (prefixWord ++ tailWord_1395314) baseStart_1395314 baseEnd_1395314 := by
    simpa [prefixWord, tailWord_1395314, baseEnd_1395314] using wordTrace_append hprefix tailTrace_1395314
  have hstable : (prefixWord ++ tailWord_1395314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395314).length < 2 ^ (prefixWord ++ tailWord_1395314).sum := by decide
  have hdescent : baseEnd_1395314 < baseStart_1395314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395325 : List Nat := [1, 4, 1, 1, 6, 1, 1, 6]
def baseStart_1395325 : Nat := 118140960795 + 1395325 * 2 ^ 59
def prefixEnd_1395325 : Nat := 4983230072969 + 3 ^ 40 * 1395325 * 2
def baseEnd_1395325 : Nat := 106144058405164224921559

theorem tailTrace_1395325 : CollatzResearch.WordTrace tailWord_1395325 prefixEnd_1395325 106144058405164224921559 := by
  unfold tailWord_1395325
  simp only [CollatzResearch.WordTrace]
  refine ⟨50891683669983302382875429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33927789113322201588583619 50891683669983302382875429)
  ·
    refine ⟨9542190688121869196789143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50891683669983302382875429 9542190688121869196789143)
    ·
      refine ⟨14313286032182803795183715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9542190688121869196789143 14313286032182803795183715)
      ·
        refine ⟨21469929048274205692775573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14313286032182803795183715 21469929048274205692775573)
        ·
          refine ⟨1006402924137853391848855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21469929048274205692775573 1006402924137853391848855)
          ·
            refine ⟨1509604386206780087773283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006402924137853391848855 1509604386206780087773283)
            ·
              refine ⟨2264406579310170131659925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509604386206780087773283 2264406579310170131659925)
              ·
                refine ⟨106144058405164224921559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2264406579310170131659925 106144058405164224921559)
                ·
                  rfl

theorem cell21_1395325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 6].length) (baseStart_1395325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395325 prefixEnd_1395325 := by exact prefixLift 1395325
  have htrace : WordTrace (prefixWord ++ tailWord_1395325) baseStart_1395325 baseEnd_1395325 := by
    simpa [prefixWord, tailWord_1395325, baseEnd_1395325] using wordTrace_append hprefix tailTrace_1395325
  have hstable : (prefixWord ++ tailWord_1395325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395325).length < 2 ^ (prefixWord ++ tailWord_1395325).sum := by decide
  have hdescent : baseEnd_1395325 < baseStart_1395325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395356 : List Nat := [2, 2, 3, 2, 2, 2, 2, 3, 3]
def baseStart_1395356 : Nat := 118140960795 + 1395356 * 2 ^ 59
def prefixEnd_1395356 : Nat := 4983230072969 + 3 ^ 40 * 1395356 * 2
def baseEnd_1395356 : Nat := 318439249837843509747947

theorem tailTrace_1395356 : CollatzResearch.WordTrace tailWord_1395356 prefixEnd_1395356 318439249837843509747947 := by
  unfold tailWord_1395356
  simp only [CollatzResearch.WordTrace]
  refine ⟨25446407166435497338626961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33928542888580663118169281 25446407166435497338626961)
  ·
    refine ⟨19084805374826623003970221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25446407166435497338626961 19084805374826623003970221)
    ·
      refine ⟨7156802015559983626488833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19084805374826623003970221 7156802015559983626488833)
      ·
        refine ⟨5367601511669987719866625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7156802015559983626488833 5367601511669987719866625)
        ·
          refine ⟨4025701133752490789899969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5367601511669987719866625 4025701133752490789899969)
          ·
            refine ⟨3019275850314368092424977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4025701133752490789899969 3019275850314368092424977)
            ·
              refine ⟨2264456887735776069318733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019275850314368092424977 2264456887735776069318733)
              ·
                refine ⟨849171332900916025994525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2264456887735776069318733 849171332900916025994525)
                ·
                  refine ⟨318439249837843509747947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849171332900916025994525 318439249837843509747947)
                  ·
                    rfl

theorem cell21_1395356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_1395356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395356 prefixEnd_1395356 := by exact prefixLift 1395356
  have htrace : WordTrace (prefixWord ++ tailWord_1395356) baseStart_1395356 baseEnd_1395356 := by
    simpa [prefixWord, tailWord_1395356, baseEnd_1395356] using wordTrace_append hprefix tailTrace_1395356
  have hstable : (prefixWord ++ tailWord_1395356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395356).length < 2 ^ (prefixWord ++ tailWord_1395356).sum := by decide
  have hdescent : baseEnd_1395356 < baseStart_1395356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395415 : List Nat := [1, 1, 3, 2, 1, 4, 3, 3, 3]
def baseStart_1395415 : Nat := 118140960795 + 1395415 * 2 ^ 59
def prefixEnd_1395415 : Nat := 4983230072969 + 3 ^ 40 * 1395415 * 2
def baseEnd_1395415 : Nat := 318452714441672518264493

theorem tailTrace_1395415 : CollatzResearch.WordTrace tailWord_1395415 prefixEnd_1395415 318452714441672518264493 := by
  unfold tailWord_1395415
  simp only [CollatzResearch.WordTrace]
  refine ⟨50894966239657247753651699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33929977493104831835767799 50894966239657247753651699)
  ·
    refine ⟨76342449359485871630477549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50894966239657247753651699 76342449359485871630477549)
    ·
      refine ⟨28628418509807201861429081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76342449359485871630477549 28628418509807201861429081)
      ·
        refine ⟨21471313882355401396071811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28628418509807201861429081 21471313882355401396071811)
        ·
          refine ⟨32206970823533102094107717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21471313882355401396071811 32206970823533102094107717)
          ·
            refine ⟨6038807029412456642645197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32206970823533102094107717 6038807029412456642645197)
            ·
              refine ⟨2264552636029671240991949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6038807029412456642645197 2264552636029671240991949)
              ·
                refine ⟨849207238511126715371981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2264552636029671240991949 849207238511126715371981)
                ·
                  refine ⟨318452714441672518264493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849207238511126715371981 318452714441672518264493)
                  ·
                    rfl

theorem cell21_1395415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 3].length) (baseStart_1395415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395415 prefixEnd_1395415 := by exact prefixLift 1395415
  have htrace : WordTrace (prefixWord ++ tailWord_1395415) baseStart_1395415 baseEnd_1395415 := by
    simpa [prefixWord, tailWord_1395415, baseEnd_1395415] using wordTrace_append hprefix tailTrace_1395415
  have hstable : (prefixWord ++ tailWord_1395415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395415).length < 2 ^ (prefixWord ++ tailWord_1395415).sum := by decide
  have hdescent : baseEnd_1395415 < baseStart_1395415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395432 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 5]
def baseStart_1395432 : Nat := 118140960795 + 1395432 * 2 ^ 59
def prefixEnd_1395432 : Nat := 4983230072969 + 3 ^ 40 * 1395432 * 2
def baseEnd_1395432 : Nat := 318456594073284266481125

theorem tailTrace_1395432 : CollatzResearch.WordTrace tailWord_1395432 prefixEnd_1395432 318456594073284266481125 := by
  unfold tailWord_1395432
  simp only [CollatzResearch.WordTrace]
  refine ⟨25447793140297829828510275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33930390853730439771347033 25447793140297829828510275)
  ·
    refine ⟨38171689710446744742765413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25447793140297829828510275 38171689710446744742765413)
    ·
      refine ⟨7157191820708764639268515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38171689710446744742765413 7157191820708764639268515)
      ·
        refine ⟨10735787731063146958902773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7157191820708764639268515 10735787731063146958902773)
        ·
          refine ⟨1006480099787170027397135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10735787731063146958902773 1006480099787170027397135)
          ·
            refine ⟨1509720149680755041095703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006480099787170027397135 1509720149680755041095703)
            ·
              refine ⟨2264580224521132561643555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509720149680755041095703 2264580224521132561643555)
              ·
                refine ⟨3396870336781698842465333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264580224521132561643555 3396870336781698842465333)
                ·
                  refine ⟨318456594073284266481125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3396870336781698842465333 318456594073284266481125)
                  ·
                    rfl

theorem cell21_1395432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 5].length) (baseStart_1395432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395432 prefixEnd_1395432 := by exact prefixLift 1395432
  have htrace : WordTrace (prefixWord ++ tailWord_1395432) baseStart_1395432 baseEnd_1395432 := by
    simpa [prefixWord, tailWord_1395432, baseEnd_1395432] using wordTrace_append hprefix tailTrace_1395432
  have hstable : (prefixWord ++ tailWord_1395432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395432).length < 2 ^ (prefixWord ++ tailWord_1395432).sum := by decide
  have hdescent : baseEnd_1395432 < baseStart_1395432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395457 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 7]
def baseStart_1395457 : Nat := 118140960795 + 1395457 * 2 ^ 59
def prefixEnd_1395457 : Nat := 4983230072969 + 3 ^ 40 * 1395457 * 2
def baseEnd_1395457 : Nat := 318462299413889778564407

theorem tailTrace_1395457 : CollatzResearch.WordTrace tailWord_1395457 prefixEnd_1395457 318462299413889778564407 := by
  unfold tailWord_1395457
  simp only [CollatzResearch.WordTrace]
  refine ⟨50896498105505088926680625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33930998737003392617787083 50896498105505088926680625)
  ·
    refine ⟨38172373579128816695010469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50896498105505088926680625 38172373579128816695010469)
    ·
      refine ⟨7157320046086653130314463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38172373579128816695010469 7157320046086653130314463)
      ·
        refine ⟨10735980069129979695471695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7157320046086653130314463 10735980069129979695471695)
        ·
          refine ⟨16103970103694969543207543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10735980069129979695471695 16103970103694969543207543)
          ·
            refine ⟨24155955155542454314811315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16103970103694969543207543 24155955155542454314811315)
            ·
              refine ⟨36233932733313681472216973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24155955155542454314811315 36233932733313681472216973)
              ·
                refine ⟨13587724774992630552081365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36233932733313681472216973 13587724774992630552081365)
                ·
                  refine ⟨318462299413889778564407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13587724774992630552081365 318462299413889778564407)
                  ·
                    rfl

theorem cell21_1395457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_1395457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395457 prefixEnd_1395457 := by exact prefixLift 1395457
  have htrace : WordTrace (prefixWord ++ tailWord_1395457) baseStart_1395457 baseEnd_1395457 := by
    simpa [prefixWord, tailWord_1395457, baseEnd_1395457] using wordTrace_append hprefix tailTrace_1395457
  have hstable : (prefixWord ++ tailWord_1395457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395457).length < 2 ^ (prefixWord ++ tailWord_1395457).sum := by decide
  have hdescent : baseEnd_1395457 < baseStart_1395457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395612 : List Nat := [2, 2, 3, 3, 2, 1, 2, 6]
def baseStart_1395612 : Nat := 118140960795 + 1395612 * 2 ^ 59
def prefixEnd_1395612 : Nat := 4983230072969 + 3 ^ 40 * 1395612 * 2
def baseEnd_1395612 : Nat := 106165890841881317826919

theorem tailTrace_1395612 : CollatzResearch.WordTrace tailWord_1395612 prefixEnd_1395612 106165890841881317826919 := by
  unfold tailWord_1395612
  simp only [CollatzResearch.WordTrace]
  refine ⟨25451075709971775199286545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33934767613295700265715393 25451075709971775199286545)
  ·
    refine ⟨19088306782478831399464909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25451075709971775199286545 19088306782478831399464909)
    ·
      refine ⟨7158115043429561774799341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19088306782478831399464909 7158115043429561774799341)
      ·
        refine ⟨2684293141286085665549753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7158115043429561774799341 2684293141286085665549753)
        ·
          refine ⟨2013219855964564249162315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2684293141286085665549753 2013219855964564249162315)
          ·
            refine ⟨3019829783946846373743473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013219855964564249162315 3019829783946846373743473)
            ·
              refine ⟨2264872337960134780307605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019829783946846373743473 2264872337960134780307605)
              ·
                refine ⟨106165890841881317826919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2264872337960134780307605 106165890841881317826919)
                ·
                  rfl

theorem cell21_1395612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_1395612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395612 prefixEnd_1395612 := by exact prefixLift 1395612
  have htrace : WordTrace (prefixWord ++ tailWord_1395612) baseStart_1395612 baseEnd_1395612 := by
    simpa [prefixWord, tailWord_1395612, baseEnd_1395612] using wordTrace_append hprefix tailTrace_1395612
  have hstable : (prefixWord ++ tailWord_1395612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395612).length < 2 ^ (prefixWord ++ tailWord_1395612).sum := by decide
  have hdescent : baseEnd_1395612 < baseStart_1395612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395747 : List Nat := [1, 1, 1, 4, 3, 2, 4, 5]
def baseStart_1395747 : Nat := 118140960795 + 1395747 * 2 ^ 59
def prefixEnd_1395747 : Nat := 4983230072969 + 3 ^ 40 * 1395747 * 2
def baseEnd_1395747 : Nat := 106176160454971239576827

theorem tailTrace_1395747 : CollatzResearch.WordTrace tailWord_1395747 prefixEnd_1395747 106176160454971239576827 := by
  unfold tailWord_1395747
  simp only [CollatzResearch.WordTrace]
  refine ⟨50907075274454468454737495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33938050182969645636491663 50907075274454468454737495)
  ·
    refine ⟨76360612911681702682106243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50907075274454468454737495 76360612911681702682106243)
    ·
      refine ⟨114540919367522554023159365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76360612911681702682106243 114540919367522554023159365)
      ·
        refine ⟨21476422381410478879342381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114540919367522554023159365 21476422381410478879342381)
        ·
          refine ⟨8053658393028929579753393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21476422381410478879342381 8053658393028929579753393)
          ·
            refine ⟨6040243794771697184815045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8053658393028929579753393 6040243794771697184815045)
            ·
              refine ⟨1132545711519693222152821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6040243794771697184815045 1132545711519693222152821)
              ·
                refine ⟨106176160454971239576827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1132545711519693222152821 106176160454971239576827)
                ·
                  rfl

theorem cell21_1395747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 5].length) (baseStart_1395747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395747 prefixEnd_1395747 := by exact prefixLift 1395747
  have htrace : WordTrace (prefixWord ++ tailWord_1395747) baseStart_1395747 baseEnd_1395747 := by
    simpa [prefixWord, tailWord_1395747, baseEnd_1395747] using wordTrace_append hprefix tailTrace_1395747
  have hstable : (prefixWord ++ tailWord_1395747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395747).length < 2 ^ (prefixWord ++ tailWord_1395747).sum := by decide
  have hdescent : baseEnd_1395747 < baseStart_1395747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395764 : List Nat := [2, 5, 1, 2, 1, 3, 7]
def baseStart_1395764 : Nat := 118140960795 + 1395764 * 2 ^ 59
def prefixEnd_1395764 : Nat := 4983230072969 + 3 ^ 40 * 1395764 * 2
def baseEnd_1395764 : Nat := 35392484555169496327457

theorem tailTrace_1395764 : CollatzResearch.WordTrace tailWord_1395764 prefixEnd_1395764 35392484555169496327457 := by
  unfold tailWord_1395764
  simp only [CollatzResearch.WordTrace]
  refine ⟨25453847657696440179053173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33938463543595253572070897 25453847657696440179053173)
  ·
    refine ⟨2386298217909041266786235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25453847657696440179053173 2386298217909041266786235)
    ·
      refine ⟨3579447326863561900179353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2386298217909041266786235 3579447326863561900179353)
      ·
        refine ⟨2684585495147671425134515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3579447326863561900179353 2684585495147671425134515)
        ·
          refine ⟨4026878242721507137701773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684585495147671425134515 4026878242721507137701773)
          ·
            refine ⟨1510079341020565176638165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4026878242721507137701773 1510079341020565176638165)
            ·
              refine ⟨35392484555169496327457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1510079341020565176638165 35392484555169496327457)
              ·
                rfl

theorem cell21_1395764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 7].length) (baseStart_1395764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395764 prefixEnd_1395764 := by exact prefixLift 1395764
  have htrace : WordTrace (prefixWord ++ tailWord_1395764) baseStart_1395764 baseEnd_1395764 := by
    simpa [prefixWord, tailWord_1395764, baseEnd_1395764] using wordTrace_append hprefix tailTrace_1395764
  have hstable : (prefixWord ++ tailWord_1395764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395764).length < 2 ^ (prefixWord ++ tailWord_1395764).sum := by decide
  have hdescent : baseEnd_1395764 < baseStart_1395764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395837 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1395837 : Nat := 118140960795 + 1395837 * 2 ^ 59
def prefixEnd_1395837 : Nat := 4983230072969 + 3 ^ 40 * 1395837 * 2
def baseEnd_1395837 : Nat := 318549020591093562230297

theorem tailTrace_1395837 : CollatzResearch.WordTrace tailWord_1395837 prefixEnd_1395837 318549020591093562230297 := by
  unfold tailWord_1395837
  simp only [CollatzResearch.WordTrace]
  refine ⟨50910357844128413825513765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33940238562752275883675843 50910357844128413825513765)
  ·
    refine ⟨9545692095774077592283831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50910357844128413825513765 9545692095774077592283831)
    ·
      refine ⟨14318538143661116388425747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9545692095774077592283831 14318538143661116388425747)
      ·
        refine ⟨21477807215491674582638621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14318538143661116388425747 21477807215491674582638621)
        ·
          refine ⟨8054177705809377968489483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21477807215491674582638621 8054177705809377968489483)
          ·
            refine ⟨12081266558714066952734225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8054177705809377968489483 12081266558714066952734225)
            ·
              refine ⟨9060949919035550214550669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12081266558714066952734225 9060949919035550214550669)
              ·
                refine ⟨3397856219638331330456501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9060949919035550214550669 3397856219638331330456501)
                ·
                  refine ⟨318549020591093562230297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3397856219638331330456501 318549020591093562230297)
                  ·
                    rfl

theorem cell21_1395837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1395837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395837 prefixEnd_1395837 := by exact prefixLift 1395837
  have htrace : WordTrace (prefixWord ++ tailWord_1395837) baseStart_1395837 baseEnd_1395837 := by
    simpa [prefixWord, tailWord_1395837, baseEnd_1395837] using wordTrace_append hprefix tailTrace_1395837
  have hstable : (prefixWord ++ tailWord_1395837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395837).length < 2 ^ (prefixWord ++ tailWord_1395837).sum := by decide
  have hdescent : baseEnd_1395837 < baseStart_1395837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395854 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_1395854 : Nat := 118140960795 + 1395854 * 2 ^ 59
def prefixEnd_1395854 : Nat := 4983230072969 + 3 ^ 40 * 1395854 * 2
def baseEnd_1395854 : Nat := 318552900222705310446929

theorem tailTrace_1395854 : CollatzResearch.WordTrace tailWord_1395854 prefixEnd_1395854 318552900222705310446929 := by
  unfold tailWord_1395854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6363872235633353216110327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33940651923377883819255077 6363872235633353216110327)
  ·
    refine ⟨9545808353450029824165491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6363872235633353216110327 9545808353450029824165491)
    ·
      refine ⟨14318712530175044736248237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9545808353450029824165491 14318712530175044736248237)
      ·
        refine ⟨5369517198815641776093089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14318712530175044736248237 5369517198815641776093089)
        ·
          refine ⟨4027137899111731332069817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5369517198815641776093089 4027137899111731332069817)
          ·
            refine ⟨3020353424333798499052363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4027137899111731332069817 3020353424333798499052363)
            ·
              refine ⟨4530530136500697748578545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020353424333798499052363 4530530136500697748578545)
              ·
                refine ⟨3397897602375523311433909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4530530136500697748578545 3397897602375523311433909)
                ·
                  refine ⟨318552900222705310446929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3397897602375523311433909 318552900222705310446929)
                  ·
                    rfl

theorem cell21_1395854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_1395854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395854 prefixEnd_1395854 := by exact prefixLift 1395854
  have htrace : WordTrace (prefixWord ++ tailWord_1395854) baseStart_1395854 baseEnd_1395854 := by
    simpa [prefixWord, tailWord_1395854, baseEnd_1395854] using wordTrace_append hprefix tailTrace_1395854
  have hstable : (prefixWord ++ tailWord_1395854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395854).length < 2 ^ (prefixWord ++ tailWord_1395854).sum := by decide
  have hdescent : baseEnd_1395854 < baseStart_1395854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395885 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1395885 : Nat := 118140960795 + 1395885 * 2 ^ 59
def prefixEnd_1395885 : Nat := 4983230072969 + 3 ^ 40 * 1395885 * 2
def baseEnd_1395885 : Nat := 318559974845056145430199

theorem tailTrace_1395885 : CollatzResearch.WordTrace tailWord_1395885 prefixEnd_1395885 318559974845056145430199 := by
  unfold tailWord_1395885
  simp only [CollatzResearch.WordTrace]
  refine ⟨50912108547954518023261109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33941405698636345348840739 50912108547954518023261109)
  ·
    refine ⟨4773010176370736064680729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50912108547954518023261109 4773010176370736064680729)
    ·
      refine ⟨3579757632278052048510547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4773010176370736064680729 3579757632278052048510547)
      ·
        refine ⟨5369636448417078072765821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579757632278052048510547 5369636448417078072765821)
        ·
          refine ⟨2013613668156404277287183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5369636448417078072765821 2013613668156404277287183)
          ·
            refine ⟨3020420502234606415930775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013613668156404277287183 3020420502234606415930775)
            ·
              refine ⟨4530630753351909623896163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020420502234606415930775 4530630753351909623896163)
              ·
                refine ⟨6795946130027864435844245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530630753351909623896163 6795946130027864435844245)
                ·
                  refine ⟨318559974845056145430199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6795946130027864435844245 318559974845056145430199)
                  ·
                    rfl

theorem cell21_1395885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1395885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395885 prefixEnd_1395885 := by exact prefixLift 1395885
  have htrace : WordTrace (prefixWord ++ tailWord_1395885) baseStart_1395885 baseEnd_1395885 := by
    simpa [prefixWord, tailWord_1395885, baseEnd_1395885] using wordTrace_append hprefix tailTrace_1395885
  have hstable : (prefixWord ++ tailWord_1395885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395885).length < 2 ^ (prefixWord ++ tailWord_1395885).sum := by decide
  have hdescent : baseEnd_1395885 < baseStart_1395885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395902 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_1395902 : Nat := 118140960795 + 1395902 * 2 ^ 59
def prefixEnd_1395902 : Nat := 4983230072969 + 3 ^ 40 * 1395902 * 2
def baseEnd_1395902 : Nat := 318563854476667893646831

theorem tailTrace_1395902 : CollatzResearch.WordTrace tailWord_1395902 prefixEnd_1395902 318563854476667893646831 := by
  unfold tailWord_1395902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6364091073611616240828745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33941819059261953284419973 6364091073611616240828745)
  ·
    refine ⟨4773068305208712180621559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6364091073611616240828745 4773068305208712180621559)
    ·
      refine ⟨7159602457813068270932339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4773068305208712180621559 7159602457813068270932339)
      ·
        refine ⟨10739403686719602406398509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7159602457813068270932339 10739403686719602406398509)
        ·
          refine ⟨4027276382519850902399441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10739403686719602406398509 4027276382519850902399441)
          ·
            refine ⟨3020457286889888176799581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4027276382519850902399441 3020457286889888176799581)
            ·
              refine ⟨1132671482583708066299843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3020457286889888176799581 1132671482583708066299843)
              ·
                refine ⟨1699007223875562099449765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132671482583708066299843 1699007223875562099449765)
                ·
                  refine ⟨318563854476667893646831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699007223875562099449765 318563854476667893646831)
                  ·
                    rfl

theorem cell21_1395902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_1395902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395902 prefixEnd_1395902 := by exact prefixLift 1395902
  have htrace : WordTrace (prefixWord ++ tailWord_1395902) baseStart_1395902 baseEnd_1395902 := by
    simpa [prefixWord, tailWord_1395902, baseEnd_1395902] using wordTrace_append hprefix tailTrace_1395902
  have hstable : (prefixWord ++ tailWord_1395902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395902).length < 2 ^ (prefixWord ++ tailWord_1395902).sum := by decide
  have hdescent : baseEnd_1395902 < baseStart_1395902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395927 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 6]
def baseStart_1395927 : Nat := 118140960795 + 1395927 * 2 ^ 59
def prefixEnd_1395927 : Nat := 4983230072969 + 3 ^ 40 * 1395927 * 2
def baseEnd_1395927 : Nat := 318569559817273405730113

theorem tailTrace_1395927 : CollatzResearch.WordTrace tailWord_1395927 prefixEnd_1395927 318569559817273405730113 := by
  unfold tailWord_1395927
  simp only [CollatzResearch.WordTrace]
  refine ⟨50913640413802359196290035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33942426942534906130860023 50913640413802359196290035)
  ·
    refine ⟨76370460620703538794435053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50913640413802359196290035 76370460620703538794435053)
    ·
      refine ⟨28638922732763827047913145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76370460620703538794435053 28638922732763827047913145)
      ·
        refine ⟨21479192049572870285934859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28638922732763827047913145 21479192049572870285934859)
        ·
          refine ⟨32218788074359305428902289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21479192049572870285934859 32218788074359305428902289)
          ·
            refine ⟨24164091055769479071676717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32218788074359305428902289 24164091055769479071676717)
            ·
              refine ⟨9061534145913554651878769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24164091055769479071676717 9061534145913554651878769)
              ·
                refine ⟨6796150609435165988909077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9061534145913554651878769 6796150609435165988909077)
                ·
                  refine ⟨318569559817273405730113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6796150609435165988909077 318569559817273405730113)
                  ·
                    rfl

theorem cell21_1395927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_1395927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395927 prefixEnd_1395927 := by exact prefixLift 1395927
  have htrace : WordTrace (prefixWord ++ tailWord_1395927) baseStart_1395927 baseEnd_1395927 := by
    simpa [prefixWord, tailWord_1395927, baseEnd_1395927] using wordTrace_append hprefix tailTrace_1395927
  have hstable : (prefixWord ++ tailWord_1395927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395927).length < 2 ^ (prefixWord ++ tailWord_1395927).sum := by decide
  have hdescent : baseEnd_1395927 < baseStart_1395927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395944 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_1395944 : Nat := 118140960795 + 1395944 * 2 ^ 59
def prefixEnd_1395944 : Nat := 4983230072969 + 3 ^ 40 * 1395944 * 2
def baseEnd_1395944 : Nat := 318573439448885153946745

theorem tailTrace_1395944 : CollatzResearch.WordTrace tailWord_1395944 prefixEnd_1395944 318573439448885153946745 := by
  unfold tailWord_1395944
  simp only [CollatzResearch.WordTrace]
  refine ⟨25457130227370385549829443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33942840303160514066439257 25457130227370385549829443)
  ·
    refine ⟨38185695341055578324744165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25457130227370385549829443 38185695341055578324744165)
    ·
      refine ⟨7159817876447920935889531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38185695341055578324744165 7159817876447920935889531)
      ·
        refine ⟨10739726814671881403834297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7159817876447920935889531 10739726814671881403834297)
        ·
          refine ⟨8054795111003911052875723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10739726814671881403834297 8054795111003911052875723)
          ·
            refine ⟨12082192666505866579313585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8054795111003911052875723 12082192666505866579313585)
            ·
              refine ⟨9061644499879399934485189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12082192666505866579313585 9061644499879399934485189)
              ·
                refine ⟨1699058343727387487715973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9061644499879399934485189 1699058343727387487715973)
                ·
                  refine ⟨318573439448885153946745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699058343727387487715973 318573439448885153946745)
                  ·
                    rfl

theorem cell21_1395944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_1395944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395944 prefixEnd_1395944 := by exact prefixLift 1395944
  have htrace : WordTrace (prefixWord ++ tailWord_1395944) baseStart_1395944 baseEnd_1395944 := by
    simpa [prefixWord, tailWord_1395944, baseEnd_1395944] using wordTrace_append hprefix tailTrace_1395944
  have hstable : (prefixWord ++ tailWord_1395944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395944).length < 2 ^ (prefixWord ++ tailWord_1395944).sum := by decide
  have hdescent : baseEnd_1395944 < baseStart_1395944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395947 : List Nat := [1, 1, 1, 1, 2, 7, 3, 2, 3]
def baseStart_1395947 : Nat := 118140960795 + 1395947 * 2 ^ 59
def prefixEnd_1395947 : Nat := 4983230072969 + 3 ^ 40 * 1395947 * 2
def baseEnd_1395947 : Nat := 318574124089757815396739

theorem tailTrace_1395947 : CollatzResearch.WordTrace tailWord_1395947 prefixEnd_1395947 318574124089757815396739 := by
  unfold tailWord_1395947
  simp only [CollatzResearch.WordTrace]
  refine ⟨50914369873729902612018095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33942913249153268408012063 50914369873729902612018095)
  ·
    refine ⟨76371554810594853918027143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50914369873729902612018095 76371554810594853918027143)
    ·
      refine ⟨114557332215892280877040715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76371554810594853918027143 114557332215892280877040715)
      ·
        refine ⟨171835998323838421315561073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114557332215892280877040715 171835998323838421315561073)
        ·
          refine ⟨128876998742878815986670805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171835998323838421315561073 128876998742878815986670805)
          ·
            refine ⟨3020554658036222249687597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 128876998742878815986670805 3020554658036222249687597)
            ·
              refine ⟨1132707996763583343632849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3020554658036222249687597 1132707996763583343632849)
              ·
                refine ⟨849530997572687507724637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1132707996763583343632849 849530997572687507724637)
                ·
                  refine ⟨318574124089757815396739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849530997572687507724637 318574124089757815396739)
                  ·
                    rfl

theorem cell21_1395947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 3].length) (baseStart_1395947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395947 prefixEnd_1395947 := by exact prefixLift 1395947
  have htrace : WordTrace (prefixWord ++ tailWord_1395947) baseStart_1395947 baseEnd_1395947 := by
    simpa [prefixWord, tailWord_1395947, baseEnd_1395947] using wordTrace_append hprefix tailTrace_1395947
  have hstable : (prefixWord ++ tailWord_1395947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395947).length < 2 ^ (prefixWord ++ tailWord_1395947).sum := by decide
  have hdescent : baseEnd_1395947 < baseStart_1395947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395998 : List Nat := [4, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1395998 : Nat := 118140960795 + 1395998 * 2 ^ 59
def prefixEnd_1395998 : Nat := 4983230072969 + 3 ^ 40 * 1395998 * 2
def baseEnd_1395998 : Nat := 318585762984593060046635

theorem tailTrace_1395998 : CollatzResearch.WordTrace tailWord_1395998 prefixEnd_1395998 318585762984593060046635 := by
  unfold tailWord_1395998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6364528749568142290265581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33944153331030092214749765 6364528749568142290265581)
  ·
    refine ⟨2386698281088053358849593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6364528749568142290265581 2386698281088053358849593)
    ·
      refine ⟨1790023710816040019137195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2386698281088053358849593 1790023710816040019137195)
      ·
        refine ⟨2685035566224060028705793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1790023710816040019137195 2685035566224060028705793)
        ·
          refine ⟨2013776674668045021529345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2685035566224060028705793 2013776674668045021529345)
          ·
            refine ⟨1510332506001033766147009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2013776674668045021529345 1510332506001033766147009)
            ·
              refine ⟨1132749379500775324610257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510332506001033766147009 1132749379500775324610257)
              ·
                refine ⟨849562034625581493457693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1132749379500775324610257 849562034625581493457693)
                ·
                  refine ⟨318585762984593060046635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849562034625581493457693 318585762984593060046635)
                  ·
                    rfl

theorem cell21_1395998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1395998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1395998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1395998 prefixEnd_1395998 := by exact prefixLift 1395998
  have htrace : WordTrace (prefixWord ++ tailWord_1395998) baseStart_1395998 baseEnd_1395998 := by
    simpa [prefixWord, tailWord_1395998, baseEnd_1395998] using wordTrace_append hprefix tailTrace_1395998
  have hstable : (prefixWord ++ tailWord_1395998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395998).length < 2 ^ (prefixWord ++ tailWord_1395998).sum := by decide
  have hdescent : baseEnd_1395998 < baseStart_1395998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396048 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_1396048 : Nat := 118140960795 + 1396048 * 2 ^ 59
def prefixEnd_1396048 : Nat := 4983230072969 + 3 ^ 40 * 1396048 * 2
def baseEnd_1396048 : Nat := 318597173665804084213199

theorem tailTrace_1396048 : CollatzResearch.WordTrace tailWord_1396048 prefixEnd_1396048 318597173665804084213199 := by
  unfold tailWord_1396048
  simp only [CollatzResearch.WordTrace]
  refine ⟨25459026823181998430722399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33945369097575997907629865 25459026823181998430722399)
  ·
    refine ⟨38188540234772997646083599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25459026823181998430722399 38188540234772997646083599)
    ·
      refine ⟨57282810352159496469125399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38188540234772997646083599 57282810352159496469125399)
      ·
        refine ⟨85924215528239244703688099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57282810352159496469125399 85924215528239244703688099)
        ·
          refine ⟨128886323292358867055532149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85924215528239244703688099 128886323292358867055532149)
          ·
            refine ⟨12083092808658643786456139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128886323292358867055532149 12083092808658643786456139)
            ·
              refine ⟨18124639212987965679684209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12083092808658643786456139 18124639212987965679684209)
              ·
                refine ⟨13593479409740974259763157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18124639212987965679684209 13593479409740974259763157)
                ·
                  refine ⟨318597173665804084213199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13593479409740974259763157 318597173665804084213199)
                  ·
                    rfl

theorem cell21_1396048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_1396048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396048 prefixEnd_1396048 := by exact prefixLift 1396048
  have htrace : WordTrace (prefixWord ++ tailWord_1396048) baseStart_1396048 baseEnd_1396048 := by
    simpa [prefixWord, tailWord_1396048, baseEnd_1396048] using wordTrace_append hprefix tailTrace_1396048
  have hstable : (prefixWord ++ tailWord_1396048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396048).length < 2 ^ (prefixWord ++ tailWord_1396048).sum := by decide
  have hdescent : baseEnd_1396048 < baseStart_1396048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396085 : List Nat := [1, 3, 4, 1, 4, 1, 2, 5]
def baseStart_1396085 : Nat := 118140960795 + 1396085 * 2 ^ 59
def prefixEnd_1396085 : Nat := 4983230072969 + 3 ^ 40 * 1396085 * 2
def baseEnd_1396085 : Nat := 106201872523300080698819

theorem tailTrace_1396085 : CollatzResearch.WordTrace tailWord_1396085 prefixEnd_1396085 106201872523300080698819 := by
  unfold tailWord_1396085
  simp only [CollatzResearch.WordTrace]
  refine ⟨50919403147229952180541709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33946268764819968120361139 50919403147229952180541709)
  ·
    refine ⟨19094776180211232067703141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50919403147229952180541709 19094776180211232067703141)
    ·
      refine ⟨3580270533789606012694339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19094776180211232067703141 3580270533789606012694339)
      ·
        refine ⟨5370405800684409019041509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3580270533789606012694339 5370405800684409019041509)
        ·
          refine ⟨1006951087628326691070283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5370405800684409019041509 1006951087628326691070283)
          ·
            refine ⟨1510426631442490036605425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006951087628326691070283 1510426631442490036605425)
            ·
              refine ⟨1132819973581867527454069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510426631442490036605425 1132819973581867527454069)
              ·
                refine ⟨106201872523300080698819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1132819973581867527454069 106201872523300080698819)
                ·
                  rfl

theorem cell21_1396085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 5].length) (baseStart_1396085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396085 prefixEnd_1396085 := by exact prefixLift 1396085
  have htrace : WordTrace (prefixWord ++ tailWord_1396085) baseStart_1396085 baseEnd_1396085 := by
    simpa [prefixWord, tailWord_1396085, baseEnd_1396085] using wordTrace_append hprefix tailTrace_1396085
  have hstable : (prefixWord ++ tailWord_1396085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396085).length < 2 ^ (prefixWord ++ tailWord_1396085).sum := by decide
  have hdescent : baseEnd_1396085 < baseStart_1396085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396099 : List Nat := [1, 1, 1, 3, 5, 3, 1, 3, 3]
def baseStart_1396099 : Nat := 118140960795 + 1396099 * 2 ^ 59
def prefixEnd_1396099 : Nat := 4983230072969 + 3 ^ 40 * 1396099 * 2
def baseEnd_1396099 : Nat := 318608812560639328863095

theorem tailTrace_1396099 : CollatzResearch.WordTrace tailWord_1396099 prefixEnd_1396099 318608812560639328863095 := by
  unfold tailWord_1396099
  simp only [CollatzResearch.WordTrace]
  refine ⟨50919913769179232571551351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33946609179452821714367567 50919913769179232571551351)
  ·
    refine ⟨76379870653768848857327027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50919913769179232571551351 76379870653768848857327027)
    ·
      refine ⟨114569805980653273285990541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76379870653768848857327027 114569805980653273285990541)
      ·
        refine ⟨42963677242744977482246453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114569805980653273285990541 42963677242744977482246453)
        ·
          refine ⟨4027844741507341638960605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42963677242744977482246453 4027844741507341638960605)
          ·
            refine ⟨1510441778065253114610227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4027844741507341638960605 1510441778065253114610227)
            ·
              refine ⟨2265662667097879671915341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510441778065253114610227 2265662667097879671915341)
              ·
                refine ⟨849623500161704876968253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2265662667097879671915341 849623500161704876968253)
                ·
                  refine ⟨318608812560639328863095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849623500161704876968253 318608812560639328863095)
                  ·
                    rfl

theorem cell21_1396099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 3].length) (baseStart_1396099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396099 prefixEnd_1396099 := by exact prefixLift 1396099
  have htrace : WordTrace (prefixWord ++ tailWord_1396099) baseStart_1396099 baseEnd_1396099 := by
    simpa [prefixWord, tailWord_1396099, baseEnd_1396099] using wordTrace_append hprefix tailTrace_1396099
  have hstable : (prefixWord ++ tailWord_1396099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396099).length < 2 ^ (prefixWord ++ tailWord_1396099).sum := by decide
  have hdescent : baseEnd_1396099 < baseStart_1396099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396116 : List Nat := [2, 4, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1396116 : Nat := 118140960795 + 1396116 * 2 ^ 59
def prefixEnd_1396116 : Nat := 4983230072969 + 3 ^ 40 * 1396116 * 2
def baseEnd_1396116 : Nat := 318612692192251077079727

theorem tailTrace_1396116 : CollatzResearch.WordTrace tailWord_1396116 prefixEnd_1396116 318612692192251077079727 := by
  unfold tailWord_1396116
  simp only [CollatzResearch.WordTrace]
  refine ⟨25460266905058822237460101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33947022540078429649946801 25460266905058822237460101)
  ·
    refine ⟨4773800044698529169523769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25460266905058822237460101 4773800044698529169523769)
    ·
      refine ⟨3580350033523896877142827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4773800044698529169523769 3580350033523896877142827)
      ·
        refine ⟨5370525050285845315714241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3580350033523896877142827 5370525050285845315714241)
        ·
          refine ⟨4027893787714383986785681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5370525050285845315714241 4027893787714383986785681)
          ·
            refine ⟨3020920340785787990089261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4027893787714383986785681 3020920340785787990089261)
            ·
              refine ⟨1132845127794670496283473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3020920340785787990089261 1132845127794670496283473)
              ·
                refine ⟨849633845846002872212605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1132845127794670496283473 849633845846002872212605)
                ·
                  refine ⟨318612692192251077079727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849633845846002872212605 318612692192251077079727)
                  ·
                    rfl

theorem cell21_1396116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1396116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396116 prefixEnd_1396116 := by exact prefixLift 1396116
  have htrace : WordTrace (prefixWord ++ tailWord_1396116) baseStart_1396116 baseEnd_1396116 := by
    simpa [prefixWord, tailWord_1396116, baseEnd_1396116] using wordTrace_append hprefix tailTrace_1396116
  have hstable : (prefixWord ++ tailWord_1396116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396116).length < 2 ^ (prefixWord ++ tailWord_1396116).sum := by decide
  have hdescent : baseEnd_1396116 < baseStart_1396116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396130 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1396130 : Nat := 118140960795 + 1396130 * 2 ^ 59
def prefixEnd_1396130 : Nat := 4983230072969 + 3 ^ 40 * 1396130 * 2
def baseEnd_1396130 : Nat := 318615887182990163846365

theorem tailTrace_1396130 : CollatzResearch.WordTrace tailWord_1396130 prefixEnd_1396130 318615887182990163846365 := by
  unfold tailWord_1396130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12730261108016731216482461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33947362954711283243953229 12730261108016731216482461)
  ·
    refine ⟨4773847915506274206180923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12730261108016731216482461 4773847915506274206180923)
    ·
      refine ⟨7160771873259411309271385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4773847915506274206180923 7160771873259411309271385)
      ·
        refine ⟨5370578904944558481953539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7160771873259411309271385 5370578904944558481953539)
        ·
          refine ⟨8055868357416837722930309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5370578904944558481953539 8055868357416837722930309)
          ·
            refine ⟨1510475317015657073049433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8055868357416837722930309 1510475317015657073049433)
            ·
              refine ⟨1132856487761742804787075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510475317015657073049433 1132856487761742804787075)
              ·
                refine ⟨1699284731642614207180613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132856487761742804787075 1699284731642614207180613)
                ·
                  refine ⟨318615887182990163846365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699284731642614207180613 318615887182990163846365)
                  ·
                    rfl

theorem cell21_1396130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1396130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396130 prefixEnd_1396130 := by exact prefixLift 1396130
  have htrace : WordTrace (prefixWord ++ tailWord_1396130) baseStart_1396130 baseEnd_1396130 := by
    simpa [prefixWord, tailWord_1396130, baseEnd_1396130] using wordTrace_append hprefix tailTrace_1396130
  have hstable : (prefixWord ++ tailWord_1396130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396130).length < 2 ^ (prefixWord ++ tailWord_1396130).sum := by decide
  have hdescent : baseEnd_1396130 < baseStart_1396130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396158 : List Nat := [4, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_1396158 : Nat := 118140960795 + 1396158 * 2 ^ 59
def prefixEnd_1396158 : Nat := 4983230072969 + 3 ^ 40 * 1396158 * 2
def baseEnd_1396158 : Nat := 318622277164468337379641

theorem tailTrace_1396158 : CollatzResearch.WordTrace tailWord_1396158 prefixEnd_1396158 318622277164468337379641 := by
  unfold tailWord_1396158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6365258209495685705993641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33948043783976990431966085 6365258209495685705993641)
  ·
    refine ⟨4773943657121764279495231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6365258209495685705993641 4773943657121764279495231)
    ·
      refine ⟨7160915485682646419242847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4773943657121764279495231 7160915485682646419242847)
      ·
        refine ⟨10741373228523969628864271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7160915485682646419242847 10741373228523969628864271)
        ·
          refine ⟨16112059842785954443296407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10741373228523969628864271 16112059842785954443296407)
          ·
            refine ⟨24168089764178931664944611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16112059842785954443296407 24168089764178931664944611)
            ·
              refine ⟨36252134646268397497416917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24168089764178931664944611 36252134646268397497416917)
              ·
                refine ⟨849659405771915566345709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36252134646268397497416917 849659405771915566345709)
                ·
                  refine ⟨318622277164468337379641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849659405771915566345709 318622277164468337379641)
                  ·
                    rfl

theorem cell21_1396158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_1396158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396158 prefixEnd_1396158 := by exact prefixLift 1396158
  have htrace : WordTrace (prefixWord ++ tailWord_1396158) baseStart_1396158 baseEnd_1396158 := by
    simpa [prefixWord, tailWord_1396158, baseEnd_1396158] using wordTrace_append hprefix tailTrace_1396158
  have hstable : (prefixWord ++ tailWord_1396158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396158).length < 2 ^ (prefixWord ++ tailWord_1396158).sum := by decide
  have hdescent : baseEnd_1396158 < baseStart_1396158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396172 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_1396172 : Nat := 118140960795 + 1396172 * 2 ^ 59
def prefixEnd_1396172 : Nat := 4983230072969 + 3 ^ 40 * 1396172 * 2
def baseEnd_1396172 : Nat := 318625472155207424146279

theorem tailTrace_1396172 : CollatzResearch.WordTrace tailWord_1396172 prefixEnd_1396172 318625472155207424146279 := by
  unfold tailWord_1396172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25461288148957383019479385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33948384198609844025972513 25461288148957383019479385)
  ·
    refine ⟨19095966111718037264609539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25461288148957383019479385 19095966111718037264609539)
    ·
      refine ⟨28643949167577055896914309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19095966111718037264609539 28643949167577055896914309)
      ·
        refine ⟨5370740468920697980671433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28643949167577055896914309 5370740468920697980671433)
        ·
          refine ⟨4028055351690523485503575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5370740468920697980671433 4028055351690523485503575)
          ·
            refine ⟨6042083027535785228255363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028055351690523485503575 6042083027535785228255363)
            ·
              refine ⟨9063124541303677842383045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042083027535785228255363 9063124541303677842383045)
              ·
                refine ⟨1699335851494439595446821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9063124541303677842383045 1699335851494439595446821)
                ·
                  refine ⟨318625472155207424146279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699335851494439595446821 318625472155207424146279)
                  ·
                    rfl

theorem cell21_1396172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_1396172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396172 prefixEnd_1396172 := by exact prefixLift 1396172
  have htrace : WordTrace (prefixWord ++ tailWord_1396172) baseStart_1396172 baseEnd_1396172 := by
    simpa [prefixWord, tailWord_1396172, baseEnd_1396172] using wordTrace_append hprefix tailTrace_1396172
  have hstable : (prefixWord ++ tailWord_1396172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396172).length < 2 ^ (prefixWord ++ tailWord_1396172).sum := by decide
  have hdescent : baseEnd_1396172 < baseStart_1396172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396186 : List Nat := [3, 1, 1, 2, 3, 2, 3, 6]
def baseStart_1396186 : Nat := 118140960795 + 1396186 * 2 ^ 59
def prefixEnd_1396186 : Nat := 4983230072969 + 3 ^ 40 * 1396186 * 2
def baseEnd_1396186 : Nat := 106209555715315503637639

theorem tailTrace_1396186 : CollatzResearch.WordTrace tailWord_1396186 prefixEnd_1396186 106209555715315503637639 := by
  unfold tailWord_1396186
  simp only [CollatzResearch.WordTrace]
  refine ⟨12730771729966011607492103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33948724613242697619978941 12730771729966011607492103)
  ·
    refine ⟨19096157594949017411238155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12730771729966011607492103 19096157594949017411238155)
    ·
      refine ⟨28644236392423526116857233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19096157594949017411238155 28644236392423526116857233)
      ·
        refine ⟨21483177294317644587642925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28644236392423526116857233 21483177294317644587642925)
        ·
          refine ⟨8056191485369116720366097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21483177294317644587642925 8056191485369116720366097)
          ·
            refine ⟨6042143614026837540274573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8056191485369116720366097 6042143614026837540274573)
            ·
              refine ⟨2265803855260064077602965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6042143614026837540274573 2265803855260064077602965)
              ·
                refine ⟨106209555715315503637639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2265803855260064077602965 106209555715315503637639)
                ·
                  rfl

theorem cell21_1396186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_1396186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396186 prefixEnd_1396186 := by exact prefixLift 1396186
  have htrace : WordTrace (prefixWord ++ tailWord_1396186) baseStart_1396186 baseEnd_1396186 := by
    simpa [prefixWord, tailWord_1396186, baseEnd_1396186] using wordTrace_append hprefix tailTrace_1396186
  have hstable : (prefixWord ++ tailWord_1396186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396186).length < 2 ^ (prefixWord ++ tailWord_1396186).sum := by decide
  have hdescent : baseEnd_1396186 < baseStart_1396186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396234 : List Nat := [3, 1, 2, 2, 2, 2, 2, 4, 3]
def baseStart_1396234 : Nat := 118140960795 + 1396234 * 2 ^ 59
def prefixEnd_1396234 : Nat := 4983230072969 + 3 ^ 40 * 1396234 * 2
def baseEnd_1396234 : Nat := 318639621399909094112819

theorem tailTrace_1396234 : CollatzResearch.WordTrace tailWord_1396234 prefixEnd_1396234 318639621399909094112819 := by
  unfold tailWord_1396234
  simp only [CollatzResearch.WordTrace]
  refine ⟨12731209405922537656928939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33949891749126767085143837 12731209405922537656928939)
  ·
    refine ⟨19096814108883806485393409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12731209405922537656928939 19096814108883806485393409)
    ·
      refine ⟨14322610581662854864045057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19096814108883806485393409 14322610581662854864045057)
      ·
        refine ⟨10741957936247141148033793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14322610581662854864045057 10741957936247141148033793)
        ·
          refine ⟨8056468452185355861025345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10741957936247141148033793 8056468452185355861025345)
          ·
            refine ⟨6042351339139016895769009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8056468452185355861025345 6042351339139016895769009)
            ·
              refine ⟨4531763504354262671826757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6042351339139016895769009 4531763504354262671826757)
              ·
                refine ⟨849705657066424250967517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4531763504354262671826757 849705657066424250967517)
                ·
                  refine ⟨318639621399909094112819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849705657066424250967517 318639621399909094112819)
                  ·
                    rfl

theorem cell21_1396234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_1396234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396234 prefixEnd_1396234 := by exact prefixLift 1396234
  have htrace : WordTrace (prefixWord ++ tailWord_1396234) baseStart_1396234 baseEnd_1396234 := by
    simpa [prefixWord, tailWord_1396234, baseEnd_1396234] using wordTrace_append hprefix tailTrace_1396234
  have hstable : (prefixWord ++ tailWord_1396234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396234).length < 2 ^ (prefixWord ++ tailWord_1396234).sum := by decide
  have hdescent : baseEnd_1396234 < baseStart_1396234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396321 : List Nat := [1, 2, 3, 1, 1, 3, 1, 9]
def baseStart_1396321 : Nat := 118140960795 + 1396321 * 2 ^ 59
def prefixEnd_1396321 : Nat := 4983230072969 + 3 ^ 40 * 1396321 * 2
def baseEnd_1396321 : Nat := 106219825328405425387547

theorem tailTrace_1396321 : CollatzResearch.WordTrace tailWord_1396321 prefixEnd_1396321 106219825328405425387547 := by
  unfold tailWord_1396321
  simp only [CollatzResearch.WordTrace]
  refine ⟨50928010774374964486132817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33952007182916642990755211 50928010774374964486132817)
  ·
    refine ⟨38196008080781223364599613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50928010774374964486132817 38196008080781223364599613)
    ·
      refine ⟨14323503030292958761724855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38196008080781223364599613 14323503030292958761724855)
      ·
        refine ⟨21485254545439438142587283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14323503030292958761724855 21485254545439438142587283)
        ·
          refine ⟨32227881818159157213880925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21485254545439438142587283 32227881818159157213880925)
          ·
            refine ⟨12085455681809683955205347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32227881818159157213880925 12085455681809683955205347)
            ·
              refine ⟨18128183522714525932808021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12085455681809683955205347 18128183522714525932808021)
              ·
                refine ⟨106219825328405425387547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18128183522714525932808021 106219825328405425387547)
                ·
                  rfl

theorem cell21_1396321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 9].length) (baseStart_1396321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396321 prefixEnd_1396321 := by exact prefixLift 1396321
  have htrace : WordTrace (prefixWord ++ tailWord_1396321) baseStart_1396321 baseEnd_1396321 := by
    simpa [prefixWord, tailWord_1396321, baseEnd_1396321] using wordTrace_append hprefix tailTrace_1396321
  have hstable : (prefixWord ++ tailWord_1396321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396321).length < 2 ^ (prefixWord ++ tailWord_1396321).sum := by decide
  have hdescent : baseEnd_1396321 < baseStart_1396321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396341 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 4]
def baseStart_1396341 : Nat := 118140960795 + 1396341 * 2 ^ 59
def prefixEnd_1396341 : Nat := 4983230072969 + 3 ^ 40 * 1396341 * 2
def baseEnd_1396341 : Nat := 318664040257700685829267

theorem tailTrace_1396341 : CollatzResearch.WordTrace tailWord_1396341 prefixEnd_1396341 318664040257700685829267 := by
  unfold tailWord_1396341
  simp only [CollatzResearch.WordTrace]
  refine ⟨50928740234302507901860877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33952493489535005267907251 50928740234302507901860877)
  ·
    refine ⟨19098277587863440463197829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50928740234302507901860877 19098277587863440463197829)
    ·
      refine ⟨3580927047724395086849593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19098277587863440463197829 3580927047724395086849593)
      ·
        refine ⟨2685695285793296315137195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3580927047724395086849593 2685695285793296315137195)
        ·
          refine ⟨4028542928689944472705793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685695285793296315137195 4028542928689944472705793)
          ·
            refine ⟨3021407196517458354529345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4028542928689944472705793 3021407196517458354529345)
            ·
              refine ⟨2266055397388093765897009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3021407196517458354529345 2266055397388093765897009)
              ·
                refine ⟨1699541548041070324422757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2266055397388093765897009 1699541548041070324422757)
                ·
                  refine ⟨318664040257700685829267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699541548041070324422757 318664040257700685829267)
                  ·
                    rfl

theorem cell21_1396341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_1396341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396341 prefixEnd_1396341 := by exact prefixLift 1396341
  have htrace : WordTrace (prefixWord ++ tailWord_1396341) baseStart_1396341 baseEnd_1396341 := by
    simpa [prefixWord, tailWord_1396341, baseEnd_1396341] using wordTrace_append hprefix tailTrace_1396341
  have hstable : (prefixWord ++ tailWord_1396341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396341).length < 2 ^ (prefixWord ++ tailWord_1396341).sum := by decide
  have hdescent : baseEnd_1396341 < baseStart_1396341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396352 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_1396352 : Nat := 118140960795 + 1396352 * 2 ^ 59
def prefixEnd_1396352 : Nat := 4983230072969 + 3 ^ 40 * 1396352 * 2
def baseEnd_1396352 : Nat := 318666550607567111145911

theorem tailTrace_1396352 : CollatzResearch.WordTrace tailWord_1396352 prefixEnd_1396352 318666550607567111145911 := by
  unfold tailWord_1396352
  simp only [CollatzResearch.WordTrace]
  refine ⟨25464570718631328390255655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33952760958175104520340873 25464570718631328390255655)
  ·
    refine ⟨38196856077946992585383483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25464570718631328390255655 38196856077946992585383483)
    ·
      refine ⟨57295284116920488878075225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38196856077946992585383483 57295284116920488878075225)
      ·
        refine ⟨42971463087690366658556419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57295284116920488878075225 42971463087690366658556419)
        ·
          refine ⟨64457194631535549987834629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42971463087690366658556419 64457194631535549987834629)
          ·
            refine ⟨12085723993412915622718993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64457194631535549987834629 12085723993412915622718993)
            ·
              refine ⟨9064292995059686717039245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12085723993412915622718993 9064292995059686717039245)
              ·
                refine ⟨3399109873147382518889717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9064292995059686717039245 3399109873147382518889717)
                ·
                  refine ⟨318666550607567111145911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3399109873147382518889717 318666550607567111145911)
                  ·
                    rfl

theorem cell21_1396352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_1396352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396352 prefixEnd_1396352 := by exact prefixLift 1396352
  have htrace : WordTrace (prefixWord ++ tailWord_1396352) baseStart_1396352 baseEnd_1396352 := by
    simpa [prefixWord, tailWord_1396352, baseEnd_1396352] using wordTrace_append hprefix tailTrace_1396352
  have hstable : (prefixWord ++ tailWord_1396352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396352).length < 2 ^ (prefixWord ++ tailWord_1396352).sum := by decide
  have hdescent : baseEnd_1396352 < baseStart_1396352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396372 : List Nat := [2, 4, 2, 2, 2, 1, 3, 5]
def baseStart_1396372 : Nat := 118140960795 + 1396372 * 2 ^ 59
def prefixEnd_1396372 : Nat := 4983230072969 + 3 ^ 40 * 1396372 * 2
def baseEnd_1396372 : Nat := 106223704960017173604179

theorem tailTrace_1396372 : CollatzResearch.WordTrace tailWord_1396372 prefixEnd_1396372 106223704960017173604179 := by
  unfold tailWord_1396372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25464935448595100098119685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33953247264793466797492913 25464935448595100098119685)
  ·
    refine ⟨4774675396611581268397441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25464935448595100098119685 4774675396611581268397441)
    ·
      refine ⟨3581006547458685951298081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4774675396611581268397441 3581006547458685951298081)
      ·
        refine ⟨2685754910594014463473561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3581006547458685951298081 2685754910594014463473561)
        ·
          refine ⟨2014316182945510847605171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2685754910594014463473561 2014316182945510847605171)
          ·
            refine ⟨3021474274418266271407757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014316182945510847605171 3021474274418266271407757)
            ·
              refine ⟨1133052852906849851777909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3021474274418266271407757 1133052852906849851777909)
              ·
                refine ⟨106223704960017173604179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1133052852906849851777909 106223704960017173604179)
                ·
                  rfl

theorem cell21_1396372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_1396372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396372 prefixEnd_1396372 := by exact prefixLift 1396372
  have htrace : WordTrace (prefixWord ++ tailWord_1396372) baseStart_1396372 baseEnd_1396372 := by
    simpa [prefixWord, tailWord_1396372, baseEnd_1396372] using wordTrace_append hprefix tailTrace_1396372
  have hstable : (prefixWord ++ tailWord_1396372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396372).length < 2 ^ (prefixWord ++ tailWord_1396372).sum := by decide
  have hdescent : baseEnd_1396372 < baseStart_1396372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396392 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 4]
def baseStart_1396392 : Nat := 118140960795 + 1396392 * 2 ^ 59
def prefixEnd_1396392 : Nat := 4983230072969 + 3 ^ 40 * 1396392 * 2
def baseEnd_1396392 : Nat := 318675679152535930479163

theorem tailTrace_1396392 : CollatzResearch.WordTrace tailWord_1396392 prefixEnd_1396392 318675679152535930479163 := by
  unfold tailWord_1396392
  simp only [CollatzResearch.WordTrace]
  refine ⟨25465300178558871805983715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33953733571411829074644953 25465300178558871805983715)
  ·
    refine ⟨38197950267838307708975573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25465300178558871805983715 38197950267838307708975573)
    ·
      refine ⟨895264459402460336929115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 38197950267838307708975573 895264459402460336929115)
      ·
        refine ⟨1342896689103690505393673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 895264459402460336929115 1342896689103690505393673)
        ·
          refine ⟨1007172516827767879045255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1342896689103690505393673 1007172516827767879045255)
          ·
            refine ⟨1510758775241651818567883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007172516827767879045255 1510758775241651818567883)
            ·
              refine ⟨2266138162862477727851825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510758775241651818567883 2266138162862477727851825)
              ·
                refine ⟨1699603622146858295888869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2266138162862477727851825 1699603622146858295888869)
                ·
                  refine ⟨318675679152535930479163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699603622146858295888869 318675679152535930479163)
                  ·
                    rfl

theorem cell21_1396392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 4].length) (baseStart_1396392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396392 prefixEnd_1396392 := by exact prefixLift 1396392
  have htrace : WordTrace (prefixWord ++ tailWord_1396392) baseStart_1396392 baseEnd_1396392 := by
    simpa [prefixWord, tailWord_1396392, baseEnd_1396392] using wordTrace_append hprefix tailTrace_1396392
  have hstable : (prefixWord ++ tailWord_1396392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396392).length < 2 ^ (prefixWord ++ tailWord_1396392).sum := by decide
  have hdescent : baseEnd_1396392 < baseStart_1396392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396586 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_1396586 : Nat := 118140960795 + 1396586 * 2 ^ 59
def prefixEnd_1396586 : Nat := 4983230072969 + 3 ^ 40 * 1396586 * 2
def baseEnd_1396586 : Nat := 318719952595634704245433

theorem tailTrace_1396586 : CollatzResearch.WordTrace tailWord_1396586 prefixEnd_1396586 318719952595634704245433 := by
  unfold tailWord_1396586
  simp only [CollatzResearch.WordTrace]
  refine ⟨12734419029603728686132403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33958450745609943163019741 12734419029603728686132403)
  ·
    refine ⟨19101628544405593029198605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12734419029603728686132403 19101628544405593029198605)
    ·
      refine ⟨7163110704152097385949477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19101628544405593029198605 7163110704152097385949477)
      ·
        refine ⟨1343083257028518259865527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7163110704152097385949477 1343083257028518259865527)
        ·
          refine ⟨2014624885542777389798291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343083257028518259865527 2014624885542777389798291)
          ·
            refine ⟨3021937328314166084697437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014624885542777389798291 3021937328314166084697437)
            ·
              refine ⟨1133226498117812281761539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3021937328314166084697437 1133226498117812281761539)
              ·
                refine ⟨1699839747176718422642309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133226498117812281761539 1699839747176718422642309)
                ·
                  refine ⟨318719952595634704245433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699839747176718422642309 318719952595634704245433)
                  ·
                    rfl

theorem cell21_1396586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_1396586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396586 prefixEnd_1396586 := by exact prefixLift 1396586
  have htrace : WordTrace (prefixWord ++ tailWord_1396586) baseStart_1396586 baseEnd_1396586 := by
    simpa [prefixWord, tailWord_1396586, baseEnd_1396586] using wordTrace_append hprefix tailTrace_1396586
  have hstable : (prefixWord ++ tailWord_1396586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396586).length < 2 ^ (prefixWord ++ tailWord_1396586).sum := by decide
  have hdescent : baseEnd_1396586 < baseStart_1396586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396687 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 4]
def baseStart_1396687 : Nat := 118140960795 + 1396687 * 2 ^ 59
def prefixEnd_1396687 : Nat := 4983230072969 + 3 ^ 40 * 1396687 * 2
def baseEnd_1396687 : Nat := 318743002171680973061893

theorem tailTrace_1396687 : CollatzResearch.WordTrace tailWord_1396687 prefixEnd_1396687 318743002171680973061893 := by
  unfold tailWord_1396687
  simp only [CollatzResearch.WordTrace]
  refine ⟨50941359891049008993956315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33960906594032672662637543 50941359891049008993956315)
  ·
    refine ⟨76412039836573513490934473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50941359891049008993956315 76412039836573513490934473)
    ·
      refine ⟨57309029877430135118200855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76412039836573513490934473 57309029877430135118200855)
      ·
        refine ⟨85963544816145202677301283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57309029877430135118200855 85963544816145202677301283)
        ·
          refine ⟨128945317224217804015951925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85963544816145202677301283 128945317224217804015951925)
          ·
            refine ⟨12088623489770419126495493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128945317224217804015951925 12088623489770419126495493)
            ·
              refine ⟨2266616904331953586217905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12088623489770419126495493 2266616904331953586217905)
              ·
                refine ⟨1699962678248965189663429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2266616904331953586217905 1699962678248965189663429)
                ·
                  refine ⟨318743002171680973061893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699962678248965189663429 318743002171680973061893)
                  ·
                    rfl

theorem cell21_1396687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 4].length) (baseStart_1396687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396687 prefixEnd_1396687 := by exact prefixLift 1396687
  have htrace : WordTrace (prefixWord ++ tailWord_1396687) baseStart_1396687 baseEnd_1396687 := by
    simpa [prefixWord, tailWord_1396687, baseEnd_1396687] using wordTrace_append hprefix tailTrace_1396687
  have hstable : (prefixWord ++ tailWord_1396687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396687).length < 2 ^ (prefixWord ++ tailWord_1396687).sum := by decide
  have hdescent : baseEnd_1396687 < baseStart_1396687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396791 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 7]
def baseStart_1396791 : Nat := 118140960795 + 1396791 * 2 ^ 59
def prefixEnd_1396791 : Nat := 4983230072969 + 3 ^ 40 * 1396791 * 2
def baseEnd_1396791 : Nat := 318766736388599903328347

theorem tailTrace_1396791 : CollatzResearch.WordTrace tailWord_1396791 prefixEnd_1396791 318766736388599903328347 := by
  unfold tailWord_1396791
  simp only [CollatzResearch.WordTrace]
  refine ⟨50945153082672234755742227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33963435388448156503828151 50945153082672234755742227)
  ·
    refine ⟨76417729624008352133613341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50945153082672234755742227 76417729624008352133613341)
    ·
      refine ⟨28656648609003132050105003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76417729624008352133613341 28656648609003132050105003)
      ·
        refine ⟨42984972913504698075157505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28656648609003132050105003 42984972913504698075157505)
        ·
          refine ⟨32238729685128523556368129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42984972913504698075157505 32238729685128523556368129)
          ·
            refine ⟨24179047263846392667276097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32238729685128523556368129 24179047263846392667276097)
            ·
              refine ⟨18134285447884794500457073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24179047263846392667276097 18134285447884794500457073)
              ·
                refine ⟨13600714085913595875342805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18134285447884794500457073 13600714085913595875342805)
                ·
                  refine ⟨318766736388599903328347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13600714085913595875342805 318766736388599903328347)
                  ·
                    rfl

theorem cell21_1396791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_1396791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396791 prefixEnd_1396791 := by exact prefixLift 1396791
  have htrace : WordTrace (prefixWord ++ tailWord_1396791) baseStart_1396791 baseEnd_1396791 := by
    simpa [prefixWord, tailWord_1396791, baseEnd_1396791] using wordTrace_append hprefix tailTrace_1396791
  have hstable : (prefixWord ++ tailWord_1396791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396791).length < 2 ^ (prefixWord ++ tailWord_1396791).sum := by decide
  have hdescent : baseEnd_1396791 < baseStart_1396791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396901 : List Nat := [1, 3, 1, 2, 1, 3, 4, 3, 3]
def baseStart_1396901 : Nat := 118140960795 + 1396901 * 2 ^ 59
def prefixEnd_1396901 : Nat := 4983230072969 + 3 ^ 40 * 1396901 * 2
def baseEnd_1396901 : Nat := 318791839887264156494789

theorem tailTrace_1396901 : CollatzResearch.WordTrace tailWord_1396901 prefixEnd_1396901 318791839887264156494789 := by
  unfold tailWord_1396901
  simp only [CollatzResearch.WordTrace]
  refine ⟨50949165112273723542246557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33966110074849149028164371 50949165112273723542246557)
  ·
    refine ⟨19105936917102646328342459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50949165112273723542246557 19105936917102646328342459)
    ·
      refine ⟨28658905375653969492513689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19105936917102646328342459 28658905375653969492513689)
      ·
        refine ⟨21494179031740477119385267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28658905375653969492513689 21494179031740477119385267)
        ·
          refine ⟨32241268547610715679077901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21494179031740477119385267 32241268547610715679077901)
          ·
            refine ⟨12090475705354018379654213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32241268547610715679077901 12090475705354018379654213)
            ·
              refine ⟨2266964194753878446185165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12090475705354018379654213 2266964194753878446185165)
              ·
                refine ⟨850111573032704417319437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2266964194753878446185165 850111573032704417319437)
                ·
                  refine ⟨318791839887264156494789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850111573032704417319437 318791839887264156494789)
                  ·
                    rfl

theorem cell21_1396901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_1396901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396901 prefixEnd_1396901 := by exact prefixLift 1396901
  have htrace : WordTrace (prefixWord ++ tailWord_1396901) baseStart_1396901 baseEnd_1396901 := by
    simpa [prefixWord, tailWord_1396901, baseEnd_1396901] using wordTrace_append hprefix tailTrace_1396901
  have hstable : (prefixWord ++ tailWord_1396901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396901).length < 2 ^ (prefixWord ++ tailWord_1396901).sum := by decide
  have hdescent : baseEnd_1396901 < baseStart_1396901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396943 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 5]
def baseStart_1396943 : Nat := 118140960795 + 1396943 * 2 ^ 59
def prefixEnd_1396943 : Nat := 4983230072969 + 3 ^ 40 * 1396943 * 2
def baseEnd_1396943 : Nat := 318801424859481416794703

theorem tailTrace_1396943 : CollatzResearch.WordTrace tailWord_1396943 prefixEnd_1396943 318801424859481416794703 := by
  unfold tailWord_1396943
  simp only [CollatzResearch.WordTrace]
  refine ⟨50950696978121564715275483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33967131318747709810183655 50950696978121564715275483)
  ·
    refine ⟨76426045467182347072913225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50950696978121564715275483 76426045467182347072913225)
    ·
      refine ⟨57319534100386760304684919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76426045467182347072913225 57319534100386760304684919)
      ·
        refine ⟨85979301150580140457027379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57319534100386760304684919 85979301150580140457027379)
        ·
          refine ⟨128968951725870210685541069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85979301150580140457027379 128968951725870210685541069)
          ·
            refine ⟨48363356897201329007077901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128968951725870210685541069 48363356897201329007077901)
            ·
              refine ⟨18136258836450498377654213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48363356897201329007077901 18136258836450498377654213)
              ·
                refine ⟨3400548531834468445810165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18136258836450498377654213 3400548531834468445810165)
                ·
                  refine ⟨318801424859481416794703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3400548531834468445810165 318801424859481416794703)
                  ·
                    rfl

theorem cell21_1396943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_1396943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396943 prefixEnd_1396943 := by exact prefixLift 1396943
  have htrace : WordTrace (prefixWord ++ tailWord_1396943) baseStart_1396943 baseEnd_1396943 := by
    simpa [prefixWord, tailWord_1396943, baseEnd_1396943] using wordTrace_append hprefix tailTrace_1396943
  have hstable : (prefixWord ++ tailWord_1396943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396943).length < 2 ^ (prefixWord ++ tailWord_1396943).sum := by decide
  have hdescent : baseEnd_1396943 < baseStart_1396943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396946 : List Nat := [3, 2, 2, 2, 1, 2, 4, 5]
def baseStart_1396946 : Nat := 118140960795 + 1396946 * 2 ^ 59
def prefixEnd_1396946 : Nat := 4983230072969 + 3 ^ 40 * 1396946 * 2
def baseEnd_1396946 : Nat := 106267369833451359414899

theorem tailTrace_1396946 : CollatzResearch.WordTrace tailWord_1396946 prefixEnd_1396946 106267369833451359414899 := by
  unfold tailWord_1396946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12737701599277674056908673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33967204264740464151756461 12737701599277674056908673)
  ·
    refine ⟨9553276199458255542681505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12737701599277674056908673 9553276199458255542681505)
    ·
      refine ⟨7164957149593691657011129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9553276199458255542681505 7164957149593691657011129)
      ·
        refine ⟨5373717862195268742758347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7164957149593691657011129 5373717862195268742758347)
        ·
          refine ⟨8060576793292903114137521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5373717862195268742758347 8060576793292903114137521)
          ·
            refine ⟨6045432594969677335603141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8060576793292903114137521 6045432594969677335603141)
            ·
              refine ⟨1133518611556814500425589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6045432594969677335603141 1133518611556814500425589)
              ·
                refine ⟨106267369833451359414899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1133518611556814500425589 106267369833451359414899)
                ·
                  rfl

theorem cell21_1396946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_1396946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396946 prefixEnd_1396946 := by exact prefixLift 1396946
  have htrace : WordTrace (prefixWord ++ tailWord_1396946) baseStart_1396946 baseEnd_1396946 := by
    simpa [prefixWord, tailWord_1396946, baseEnd_1396946] using wordTrace_append hprefix tailTrace_1396946
  have hstable : (prefixWord ++ tailWord_1396946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396946).length < 2 ^ (prefixWord ++ tailWord_1396946).sum := by decide
  have hdescent : baseEnd_1396946 < baseStart_1396946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396963 : List Nat := [1, 1, 1, 8, 2, 1, 7]
def baseStart_1396963 : Nat := 118140960795 + 1396963 * 2 ^ 59
def prefixEnd_1396963 : Nat := 4983230072969 + 3 ^ 40 * 1396963 * 2
def baseEnd_1396963 : Nat := 35422887681329536273481

theorem tailTrace_1396963 : CollatzResearch.WordTrace tailWord_1396963 prefixEnd_1396963 35422887681329536273481 := by
  unfold tailWord_1396963
  simp only [CollatzResearch.WordTrace]
  refine ⟨50951426438049108131003543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33967617625366072087335695 50951426438049108131003543)
  ·
    refine ⟨76427139657073662196505315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50951426438049108131003543 76427139657073662196505315)
    ·
      refine ⟨114640709485610493294757973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76427139657073662196505315 114640709485610493294757973)
      ·
        refine ⟨1343445814284497968297945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 114640709485610493294757973 1343445814284497968297945)
        ·
          refine ⟨1007584360713373476223459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343445814284497968297945 1007584360713373476223459)
          ·
            refine ⟨1511376541070060214335189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007584360713373476223459 1511376541070060214335189)
            ·
              refine ⟨35422887681329536273481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1511376541070060214335189 35422887681329536273481)
              ·
                rfl

theorem cell21_1396963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 7].length) (baseStart_1396963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1396963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1396963 prefixEnd_1396963 := by exact prefixLift 1396963
  have htrace : WordTrace (prefixWord ++ tailWord_1396963) baseStart_1396963 baseEnd_1396963 := by
    simpa [prefixWord, tailWord_1396963, baseEnd_1396963] using wordTrace_append hprefix tailTrace_1396963
  have hstable : (prefixWord ++ tailWord_1396963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396963).length < 2 ^ (prefixWord ++ tailWord_1396963).sum := by decide
  have hdescent : baseEnd_1396963 < baseStart_1396963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397022 : List Nat := [4, 3, 2, 1, 1, 10]
def baseStart_1397022 : Nat := 118140960795 + 1397022 * 2 ^ 59
def prefixEnd_1397022 : Nat := 4983230072969 + 3 ^ 40 * 1397022 * 2
def baseEnd_1397022 : Nat := 11808127916140549443625

theorem tailTrace_1397022 : CollatzResearch.WordTrace tailWord_1397022 prefixEnd_1397022 11808127916140549443625 := by
  unfold tailWord_1397022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6369197293104420150925165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33969052229890240804934213 6369197293104420150925165)
  ·
    refine ⟨2388448984914157556596937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6369197293104420150925165 2388448984914157556596937)
    ·
      refine ⟨1791336738685618167447703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2388448984914157556596937 1791336738685618167447703)
      ·
        refine ⟨2687005108028427251171555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791336738685618167447703 2687005108028427251171555)
        ·
          refine ⟨4030507662042640876757333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687005108028427251171555 4030507662042640876757333)
          ·
            refine ⟨11808127916140549443625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4030507662042640876757333 11808127916140549443625)
            ·
              rfl

theorem cell21_1397022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 10].length) (baseStart_1397022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397022 prefixEnd_1397022 := by exact prefixLift 1397022
  have htrace : WordTrace (prefixWord ++ tailWord_1397022) baseStart_1397022 baseEnd_1397022 := by
    simpa [prefixWord, tailWord_1397022, baseEnd_1397022] using wordTrace_append hprefix tailTrace_1397022
  have hstable : (prefixWord ++ tailWord_1397022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397022).length < 2 ^ (prefixWord ++ tailWord_1397022).sum := by decide
  have hdescent : baseEnd_1397022 < baseStart_1397022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397064 : List Nat := [2, 1, 3, 1, 1, 2, 2, 9]
def baseStart_1397064 : Nat := 118140960795 + 1397064 * 2 ^ 59
def prefixEnd_1397064 : Nat := 4983230072969 + 3 ^ 40 * 1397064 * 2
def baseEnd_1397064 : Nat := 106276346236004031759263

theorem tailTrace_1397064 : CollatzResearch.WordTrace tailWord_1397064 prefixEnd_1397064 106276346236004031759263 := by
  unfold tailWord_1397064
  simp only [CollatzResearch.WordTrace]
  refine ⟨25477555105341601190215123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33970073473788801586953497 25477555105341601190215123)
  ·
    refine ⟨38216332658012401785322685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25477555105341601190215123 38216332658012401785322685)
    ·
      refine ⟨14331124746754650669496007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38216332658012401785322685 14331124746754650669496007)
      ·
        refine ⟨21496687120131976004244011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14331124746754650669496007 21496687120131976004244011)
        ·
          refine ⟨32245030680197964006366017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21496687120131976004244011 32245030680197964006366017)
          ·
            refine ⟨24183773010148473004774513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32245030680197964006366017 24183773010148473004774513)
            ·
              refine ⟨18137829757611354753580885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24183773010148473004774513 18137829757611354753580885)
              ·
                refine ⟨106276346236004031759263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18137829757611354753580885 106276346236004031759263)
                ·
                  rfl

theorem cell21_1397064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_1397064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397064 prefixEnd_1397064 := by exact prefixLift 1397064
  have htrace : WordTrace (prefixWord ++ tailWord_1397064) baseStart_1397064 baseEnd_1397064 := by
    simpa [prefixWord, tailWord_1397064, baseEnd_1397064] using wordTrace_append hprefix tailTrace_1397064
  have hstable : (prefixWord ++ tailWord_1397064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397064).length < 2 ^ (prefixWord ++ tailWord_1397064).sum := by decide
  have hdescent : baseEnd_1397064 < baseStart_1397064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397084 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 6]
def baseStart_1397084 : Nat := 118140960795 + 1397084 * 2 ^ 59
def prefixEnd_1397084 : Nat := 4983230072969 + 3 ^ 40 * 1397084 * 2
def baseEnd_1397084 : Nat := 318833602980496504944415

theorem tailTrace_1397084 : CollatzResearch.WordTrace tailWord_1397084 prefixEnd_1397084 318833602980496504944415 := by
  unfold tailWord_1397084
  simp only [CollatzResearch.WordTrace]
  refine ⟨25477919835305372898079153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33970559780407163864105537 25477919835305372898079153)
  ·
    refine ⟨19108439876479029673559365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25477919835305372898079153 19108439876479029673559365)
    ·
      refine ⟨3582832476839818063792381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19108439876479029673559365 3582832476839818063792381)
      ·
        refine ⟨1343562178814931773922143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3582832476839818063792381 1343562178814931773922143)
        ·
          refine ⟨2015343268222397660883215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343562178814931773922143 2015343268222397660883215)
          ·
            refine ⟨3023014902333596491324823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015343268222397660883215 3023014902333596491324823)
            ·
              refine ⟨4534522353500394736987235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023014902333596491324823 4534522353500394736987235)
              ·
                refine ⟨6801783530250592105480853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4534522353500394736987235 6801783530250592105480853)
                ·
                  refine ⟨318833602980496504944415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6801783530250592105480853 318833602980496504944415)
                  ·
                    rfl

theorem cell21_1397084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_1397084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397084 prefixEnd_1397084 := by exact prefixLift 1397084
  have htrace : WordTrace (prefixWord ++ tailWord_1397084) baseStart_1397084 baseEnd_1397084 := by
    simpa [prefixWord, tailWord_1397084, baseEnd_1397084] using wordTrace_append hprefix tailTrace_1397084
  have hstable : (prefixWord ++ tailWord_1397084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397084).length < 2 ^ (prefixWord ++ tailWord_1397084).sum := by decide
  have hdescent : baseEnd_1397084 < baseStart_1397084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397129 : List Nat := [1, 2, 1, 1, 6, 1, 3, 3, 3]
def baseStart_1397129 : Nat := 118140960795 + 1397129 * 2 ^ 59
def prefixEnd_1397129 : Nat := 4983230072969 + 3 ^ 40 * 1397129 * 2
def baseEnd_1397129 : Nat := 318843872593586426694323

theorem tailTrace_1397129 : CollatzResearch.WordTrace tailWord_1397129 prefixEnd_1397129 318843872593586426694323 := by
  unfold tailWord_1397129
  simp only [CollatzResearch.WordTrace]
  refine ⟨50957480955447718481546441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33971653970298478987697627 50957480955447718481546441)
  ·
    refine ⟨38218110716585788861159831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50957480955447718481546441 38218110716585788861159831)
    ·
      refine ⟨57327166074878683291739747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38218110716585788861159831 57327166074878683291739747)
      ·
        refine ⟨85990749112318024937609621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57327166074878683291739747 85990749112318024937609621)
        ·
          refine ⟨4030816364639907418950451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85990749112318024937609621 4030816364639907418950451)
          ·
            refine ⟨6046224546959861128425677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030816364639907418950451 6046224546959861128425677)
            ·
              refine ⟨2267334205109947923159629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6046224546959861128425677 2267334205109947923159629)
              ·
                refine ⟨850250326916230471184861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2267334205109947923159629 850250326916230471184861)
                ·
                  refine ⟨318843872593586426694323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850250326916230471184861 318843872593586426694323)
                  ·
                    rfl

theorem cell21_1397129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 3].length) (baseStart_1397129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397129 prefixEnd_1397129 := by exact prefixLift 1397129
  have htrace : WordTrace (prefixWord ++ tailWord_1397129) baseStart_1397129 baseEnd_1397129 := by
    simpa [prefixWord, tailWord_1397129, baseEnd_1397129] using wordTrace_append hprefix tailTrace_1397129
  have hstable : (prefixWord ++ tailWord_1397129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397129).length < 2 ^ (prefixWord ++ tailWord_1397129).sum := by decide
  have hdescent : baseEnd_1397129 < baseStart_1397129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397146 : List Nat := [3, 1, 1, 4, 1, 3, 3, 2, 3]
def baseStart_1397146 : Nat := 118140960795 + 1397146 * 2 ^ 59
def prefixEnd_1397146 : Nat := 4983230072969 + 3 ^ 40 * 1397146 * 2
def baseEnd_1397146 : Nat := 318847752225198174910955

theorem tailTrace_1397146 : CollatzResearch.WordTrace tailWord_1397146 prefixEnd_1397146 318847752225198174910955 := by
  unfold tailWord_1397146
  simp only [CollatzResearch.WordTrace]
  refine ⟨12739525249096532596228823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33972067330924086923276861 12739525249096532596228823)
  ·
    refine ⟨19109287873644798894343235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12739525249096532596228823 19109287873644798894343235)
    ·
      refine ⟨28663931810467198341514853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19109287873644798894343235 28663931810467198341514853)
      ·
        refine ⟨5374487214462599689034035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28663931810467198341514853 5374487214462599689034035)
        ·
          refine ⟨8061730821693899533551053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374487214462599689034035 8061730821693899533551053)
          ·
            refine ⟨3023149058135212325081645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8061730821693899533551053 3023149058135212325081645)
            ·
              refine ⟨1133680896800704621905617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3023149058135212325081645 1133680896800704621905617)
              ·
                refine ⟨850260672600528466429213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133680896800704621905617 850260672600528466429213)
                ·
                  refine ⟨318847752225198174910955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850260672600528466429213 318847752225198174910955)
                  ·
                    rfl

theorem cell21_1397146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_1397146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397146 prefixEnd_1397146 := by exact prefixLift 1397146
  have htrace : WordTrace (prefixWord ++ tailWord_1397146) baseStart_1397146 baseEnd_1397146 := by
    simpa [prefixWord, tailWord_1397146, baseEnd_1397146] using wordTrace_append hprefix tailTrace_1397146
  have hstable : (prefixWord ++ tailWord_1397146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397146).length < 2 ^ (prefixWord ++ tailWord_1397146).sum := by decide
  have hdescent : baseEnd_1397146 < baseStart_1397146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397160 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_1397160 : Nat := 118140960795 + 1397160 * 2 ^ 59
def prefixEnd_1397160 : Nat := 4983230072969 + 3 ^ 40 * 1397160 * 2
def baseEnd_1397160 : Nat := 318850947215937261677593

theorem tailTrace_1397160 : CollatzResearch.WordTrace tailWord_1397160 prefixEnd_1397160 318850947215937261677593 := by
  unfold tailWord_1397160
  simp only [CollatzResearch.WordTrace]
  refine ⟨25479305809167705387962467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33972407745556940517283289 25479305809167705387962467)
  ·
    refine ⟨38218958713751558081943701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25479305809167705387962467 38218958713751558081943701)
    ·
      refine ⟨1791513689707104285091111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38218958713751558081943701 1791513689707104285091111)
      ·
        refine ⟨2687270534560656427636667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791513689707104285091111 2687270534560656427636667)
        ·
          refine ⟨4030905801840984641455001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687270534560656427636667 4030905801840984641455001)
          ·
            refine ⟨3023179351380738481091251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4030905801840984641455001 3023179351380738481091251)
            ·
              refine ⟨4534769027071107721636877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023179351380738481091251 4534769027071107721636877)
              ·
                refine ⟨1700538385151665395613829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4534769027071107721636877 1700538385151665395613829)
                ·
                  refine ⟨318850947215937261677593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1700538385151665395613829 318850947215937261677593)
                  ·
                    rfl

theorem cell21_1397160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_1397160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397160 prefixEnd_1397160 := by exact prefixLift 1397160
  have htrace : WordTrace (prefixWord ++ tailWord_1397160) baseStart_1397160 baseEnd_1397160 := by
    simpa [prefixWord, tailWord_1397160, baseEnd_1397160] using wordTrace_append hprefix tailTrace_1397160
  have hstable : (prefixWord ++ tailWord_1397160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397160).length < 2 ^ (prefixWord ++ tailWord_1397160).sum := by decide
  have hdescent : baseEnd_1397160 < baseStart_1397160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397205 : List Nat := [1, 3, 2, 3, 1, 3, 1, 4, 3]
def baseStart_1397205 : Nat := 118140960795 + 1397205 * 2 ^ 59
def prefixEnd_1397205 : Nat := 4983230072969 + 3 ^ 40 * 1397205 * 2
def baseEnd_1397205 : Nat := 318861216829027183427501

theorem tailTrace_1397205 : CollatzResearch.WordTrace tailWord_1397205 prefixEnd_1397205 318861216829027183427501 := by
  unfold tailWord_1397205
  simp only [CollatzResearch.WordTrace]
  refine ⟨50960252903172383461313069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33973501935448255640875379 50960252903172383461313069)
  ·
    refine ⟨19110094838689643797992401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50960252903172383461313069 19110094838689643797992401)
    ·
      refine ⟨14332571129017232848494301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19110094838689643797992401 14332571129017232848494301)
      ·
        refine ⟨5374714173381462318185363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14332571129017232848494301 5374714173381462318185363)
        ·
          refine ⟨8062071260072193477278045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374714173381462318185363 8062071260072193477278045)
          ·
            refine ⟨3023276722527072553979267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8062071260072193477278045 3023276722527072553979267)
            ·
              refine ⟨4534915083790608830968901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023276722527072553979267 4534915083790608830968901)
              ·
                refine ⟨850296578210739155806669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4534915083790608830968901 850296578210739155806669)
                ·
                  refine ⟨318861216829027183427501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850296578210739155806669 318861216829027183427501)
                  ·
                    rfl

theorem cell21_1397205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_1397205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397205 prefixEnd_1397205 := by exact prefixLift 1397205
  have htrace : WordTrace (prefixWord ++ tailWord_1397205) baseStart_1397205 baseEnd_1397205 := by
    simpa [prefixWord, tailWord_1397205, baseEnd_1397205] using wordTrace_append hprefix tailTrace_1397205
  have hstable : (prefixWord ++ tailWord_1397205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397205).length < 2 ^ (prefixWord ++ tailWord_1397205).sum := by decide
  have hdescent : baseEnd_1397205 < baseStart_1397205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397233 : List Nat := [1, 2, 2, 2, 3, 1, 5, 5]
def baseStart_1397233 : Nat := 118140960795 + 1397233 * 2 ^ 59
def prefixEnd_1397233 : Nat := 4983230072969 + 3 ^ 40 * 1397233 * 2
def baseEnd_1397233 : Nat := 106289202270168452320259

theorem tailTrace_1397233 : CollatzResearch.WordTrace tailWord_1397233 prefixEnd_1397233 106289202270168452320259 := by
  unfold tailWord_1397233
  simp only [CollatzResearch.WordTrace]
  refine ⟨50961274147070944243332353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33974182764713962828888235 50961274147070944243332353)
  ·
    refine ⟨38220955610303208182499265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50961274147070944243332353 38220955610303208182499265)
    ·
      refine ⟨28665716707727406136874449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38220955610303208182499265 28665716707727406136874449)
      ·
        refine ⟨21499287530795554602655837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28665716707727406136874449 21499287530795554602655837)
        ·
          refine ⟨8062232824048332975995939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21499287530795554602655837 8062232824048332975995939)
          ·
            refine ⟨12093349236072499463993909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8062232824048332975995939 12093349236072499463993909)
            ·
              refine ⟨1133751490881796824749429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12093349236072499463993909 1133751490881796824749429)
              ·
                refine ⟨106289202270168452320259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1133751490881796824749429 106289202270168452320259)
                ·
                  rfl

theorem cell21_1397233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 5].length) (baseStart_1397233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397233 prefixEnd_1397233 := by exact prefixLift 1397233
  have htrace : WordTrace (prefixWord ++ tailWord_1397233) baseStart_1397233 baseEnd_1397233 := by
    simpa [prefixWord, tailWord_1397233, baseEnd_1397233] using wordTrace_append hprefix tailTrace_1397233
  have hstable : (prefixWord ++ tailWord_1397233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397233).length < 2 ^ (prefixWord ++ tailWord_1397233).sum := by decide
  have hdescent : baseEnd_1397233 < baseStart_1397233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397250 : List Nat := [3, 4, 1, 2, 2, 1, 8]
def baseStart_1397250 : Nat := 118140960795 + 1397250 * 2 ^ 59
def prefixEnd_1397250 : Nat := 4983230072969 + 3 ^ 40 * 1397250 * 2
def baseEnd_1397250 : Nat := 35430165160235233908601

theorem tailTrace_1397250 : CollatzResearch.WordTrace tailWord_1397250 prefixEnd_1397250 35430165160235233908601 := by
  unfold tailWord_1397250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12740473547002339036675301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33974596125339570764467469 12740473547002339036675301)
  ·
    refine ⟨2388838790062938569376619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12740473547002339036675301 2388838790062938569376619)
    ·
      refine ⟨3583258185094407854064929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388838790062938569376619 3583258185094407854064929)
      ·
        refine ⟨2687443638820805890548697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3583258185094407854064929 2687443638820805890548697)
        ·
          refine ⟨2015582729115604417911523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2687443638820805890548697 2015582729115604417911523)
          ·
            refine ⟨3023374093673406626867285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015582729115604417911523 3023374093673406626867285)
            ·
              refine ⟨35430165160235233908601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3023374093673406626867285 35430165160235233908601)
              ·
                rfl

theorem cell21_1397250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 8].length) (baseStart_1397250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397250 prefixEnd_1397250 := by exact prefixLift 1397250
  have htrace : WordTrace (prefixWord ++ tailWord_1397250) baseStart_1397250 baseEnd_1397250 := by
    simpa [prefixWord, tailWord_1397250, baseEnd_1397250] using wordTrace_append hprefix tailTrace_1397250
  have hstable : (prefixWord ++ tailWord_1397250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397250).length < 2 ^ (prefixWord ++ tailWord_1397250).sum := by decide
  have hdescent : baseEnd_1397250 < baseStart_1397250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397284 : List Nat := [2, 3, 1, 5, 2, 1, 2, 5]
def baseStart_1397284 : Nat := 118140960795 + 1397284 * 2 ^ 59
def prefixEnd_1397284 : Nat := 4983230072969 + 3 ^ 40 * 1397284 * 2
def baseEnd_1397284 : Nat := 106293081901780200536891

theorem tailTrace_1397284 : CollatzResearch.WordTrace tailWord_1397284 prefixEnd_1397284 106293081901780200536891 := by
  unfold tailWord_1397284
  simp only [CollatzResearch.WordTrace]
  refine ⟨25481567134943089976719453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33975422846590786635625937 25481567134943089976719453)
  ·
    refine ⟨9555587675603658741269795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25481567134943089976719453 9555587675603658741269795)
    ·
      refine ⟨14333381513405488111904693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9555587675603658741269795 14333381513405488111904693)
      ·
        refine ⟨1343754516881764510491065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14333381513405488111904693 1343754516881764510491065)
        ·
          refine ⟨1007815887661323382868299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343754516881764510491065 1007815887661323382868299)
          ·
            refine ⟨1511723831491985074302449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007815887661323382868299 1511723831491985074302449)
            ·
              refine ⟨1133792873618988805726837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511723831491985074302449 1133792873618988805726837)
              ·
                refine ⟨106293081901780200536891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1133792873618988805726837 106293081901780200536891)
                ·
                  rfl

theorem cell21_1397284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 5].length) (baseStart_1397284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397284 prefixEnd_1397284 := by exact prefixLift 1397284
  have htrace : WordTrace (prefixWord ++ tailWord_1397284) baseStart_1397284 baseEnd_1397284 := by
    simpa [prefixWord, tailWord_1397284, baseEnd_1397284] using wordTrace_append hprefix tailTrace_1397284
  have hstable : (prefixWord ++ tailWord_1397284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397284).length < 2 ^ (prefixWord ++ tailWord_1397284).sum := by decide
  have hdescent : baseEnd_1397284 < baseStart_1397284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397309 : List Nat := [1, 4, 1, 3, 2, 3, 7]
def baseStart_1397309 : Nat := 118140960795 + 1397309 * 2 ^ 59
def prefixEnd_1397309 : Nat := 4983230072969 + 3 ^ 40 * 1397309 * 2
def baseEnd_1397309 : Nat := 35431661227327345965995

theorem tailTrace_1397309 : CollatzResearch.WordTrace tailWord_1397309 prefixEnd_1397309 35431661227327345965995 := by
  unfold tailWord_1397309
  simp only [CollatzResearch.WordTrace]
  refine ⟨50964046094795609223098981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33976030729863739482065987 50964046094795609223098981)
  ·
    refine ⟨9555758642774176729331059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50964046094795609223098981 9555758642774176729331059)
    ·
      refine ⟨14333637964161265093996589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9555758642774176729331059 14333637964161265093996589)
      ·
        refine ⟨5375114236560474410248721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14333637964161265093996589 5375114236560474410248721)
        ·
          refine ⟨4031335677420355807686541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5375114236560474410248721 4031335677420355807686541)
          ·
            refine ⟨1511750879032633427882453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4031335677420355807686541 1511750879032633427882453)
            ·
              refine ⟨35431661227327345965995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1511750879032633427882453 35431661227327345965995)
              ·
                rfl

theorem cell21_1397309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 7].length) (baseStart_1397309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397309 prefixEnd_1397309 := by exact prefixLift 1397309
  have htrace : WordTrace (prefixWord ++ tailWord_1397309) baseStart_1397309 baseEnd_1397309 := by
    simpa [prefixWord, tailWord_1397309, baseEnd_1397309] using wordTrace_append hprefix tailTrace_1397309
  have hstable : (prefixWord ++ tailWord_1397309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397309).length < 2 ^ (prefixWord ++ tailWord_1397309).sum := by decide
  have hdescent : baseEnd_1397309 < baseStart_1397309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397323 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 5]
def baseStart_1397323 : Nat := 118140960795 + 1397323 * 2 ^ 59
def prefixEnd_1397323 : Nat := 4983230072969 + 3 ^ 40 * 1397323 * 2
def baseEnd_1397323 : Nat := 318888146036685200460593

theorem tailTrace_1397323 : CollatzResearch.WordTrace tailWord_1397323 prefixEnd_1397323 318888146036685200460593 := by
  unfold tailWord_1397323
  simp only [CollatzResearch.WordTrace]
  refine ⟨50964556716744889614108623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33976371144496593076072415 50964556716744889614108623)
  ·
    refine ⟨76446835075117334421162935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50964556716744889614108623 76446835075117334421162935)
    ·
      refine ⟨114670252612676001631744403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76446835075117334421162935 114670252612676001631744403)
      ·
        refine ⟨172005378919014002447616605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114670252612676001631744403 172005378919014002447616605)
        ·
          refine ⟨64502017094630250917856227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172005378919014002447616605 64502017094630250917856227)
          ·
            refine ⟨96753025641945376376784341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64502017094630250917856227 96753025641945376376784341)
            ·
              refine ⟨2267649038483094758830883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 96753025641945376376784341 2267649038483094758830883)
              ·
                refine ⟨3401473557724642138246325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267649038483094758830883 3401473557724642138246325)
                ·
                  refine ⟨318888146036685200460593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3401473557724642138246325 318888146036685200460593)
                  ·
                    rfl

theorem cell21_1397323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 5].length) (baseStart_1397323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397323 prefixEnd_1397323 := by exact prefixLift 1397323
  have htrace : WordTrace (prefixWord ++ tailWord_1397323) baseStart_1397323 baseEnd_1397323 := by
    simpa [prefixWord, tailWord_1397323, baseEnd_1397323] using wordTrace_append hprefix tailTrace_1397323
  have hstable : (prefixWord ++ tailWord_1397323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397323).length < 2 ^ (prefixWord ++ tailWord_1397323).sum := by decide
  have hdescent : baseEnd_1397323 < baseStart_1397323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397399 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 5]
def baseStart_1397399 : Nat := 118140960795 + 1397399 * 2 ^ 59
def prefixEnd_1397399 : Nat := 4983230072969 + 3 ^ 40 * 1397399 * 2
def baseEnd_1397399 : Nat := 318905490272125957193771

theorem tailTrace_1397399 : CollatzResearch.WordTrace tailWord_1397399 prefixEnd_1397399 318905490272125957193771 := by
  unfold tailWord_1397399
  simp only [CollatzResearch.WordTrace]
  refine ⟨50967328664469554593875251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33978219109646369729250167 50967328664469554593875251)
  ·
    refine ⟨76450992996704331890812877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50967328664469554593875251 76450992996704331890812877)
    ·
      refine ⟨28669122373764124459054829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76450992996704331890812877 28669122373764124459054829)
      ·
        refine ⟨10750920890161546672145561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28669122373764124459054829 10750920890161546672145561)
        ·
          refine ⟨8063190667621160004109171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10750920890161546672145561 8063190667621160004109171)
          ·
            refine ⟨12094786001431740006163757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8063190667621160004109171 12094786001431740006163757)
            ·
              refine ⟨4535544750536902502311409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12094786001431740006163757 4535544750536902502311409)
              ·
                refine ⟨3401658562902676876733557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4535544750536902502311409 3401658562902676876733557)
                ·
                  refine ⟨318905490272125957193771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3401658562902676876733557 318905490272125957193771)
                  ·
                    rfl

theorem cell21_1397399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_1397399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397399 prefixEnd_1397399 := by exact prefixLift 1397399
  have htrace : WordTrace (prefixWord ++ tailWord_1397399) baseStart_1397399 baseEnd_1397399 := by
    simpa [prefixWord, tailWord_1397399, baseEnd_1397399] using wordTrace_append hprefix tailTrace_1397399
  have hstable : (prefixWord ++ tailWord_1397399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397399).length < 2 ^ (prefixWord ++ tailWord_1397399).sum := by decide
  have hdescent : baseEnd_1397399 < baseStart_1397399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397413 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 6]
def baseStart_1397413 : Nat := 118140960795 + 1397413 * 2 ^ 59
def prefixEnd_1397413 : Nat := 4983230072969 + 3 ^ 40 * 1397413 * 2
def baseEnd_1397413 : Nat := 318908685262865043960409

theorem tailTrace_1397413 : CollatzResearch.WordTrace tailWord_1397413 prefixEnd_1397413 318908685262865043960409 := by
  unfold tailWord_1397413
  simp only [CollatzResearch.WordTrace]
  refine ⟨50967839286418834984884893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33978559524279223323256595 50967839286418834984884893)
  ·
    refine ⟨19112939732407063119331835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50967839286418834984884893 19112939732407063119331835)
    ·
      refine ⟨28669409598610594678997753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19112939732407063119331835 28669409598610594678997753)
      ·
        refine ⟨21502057198957946009248315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28669409598610594678997753 21502057198957946009248315)
        ·
          refine ⟨32253085798436919013872473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21502057198957946009248315 32253085798436919013872473)
          ·
            refine ⟨24189814348827689260404355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32253085798436919013872473 24189814348827689260404355)
            ·
              refine ⟨36284721523241533890606533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24189814348827689260404355 36284721523241533890606533)
              ·
                refine ⟨6803385285607787604488725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36284721523241533890606533 6803385285607787604488725)
                ·
                  refine ⟨318908685262865043960409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6803385285607787604488725 318908685262865043960409)
                  ·
                    rfl

theorem cell21_1397413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_1397413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397413 prefixEnd_1397413 := by exact prefixLift 1397413
  have htrace : WordTrace (prefixWord ++ tailWord_1397413) baseStart_1397413 baseEnd_1397413 := by
    simpa [prefixWord, tailWord_1397413, baseEnd_1397413] using wordTrace_append hprefix tailTrace_1397413
  have hstable : (prefixWord ++ tailWord_1397413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397413).length < 2 ^ (prefixWord ++ tailWord_1397413).sum := by decide
  have hdescent : baseEnd_1397413 < baseStart_1397413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397489 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 6]
def baseStart_1397489 : Nat := 118140960795 + 1397489 * 2 ^ 59
def prefixEnd_1397489 : Nat := 4983230072969 + 3 ^ 40 * 1397489 * 2
def baseEnd_1397489 : Nat := 318926029498305800693587

theorem tailTrace_1397489 : CollatzResearch.WordTrace tailWord_1397489 prefixEnd_1397489 318926029498305800693587 := by
  unfold tailWord_1397489
  simp only [CollatzResearch.WordTrace]
  refine ⟨50970611234143499964651521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33980407489428999976434347 50970611234143499964651521)
  ·
    refine ⟨38227958425607624973488641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50970611234143499964651521 38227958425607624973488641)
    ·
      refine ⟨28670968819205718730116481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38227958425607624973488641 28670968819205718730116481)
      ·
        refine ⟨21503226614404289047587361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28670968819205718730116481 21503226614404289047587361)
        ·
          refine ⟨16127419960803216785690521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21503226614404289047587361 16127419960803216785690521)
          ·
            refine ⟨12095564970602412589267891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16127419960803216785690521 12095564970602412589267891)
            ·
              refine ⟨18143347455903618883901837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12095564970602412589267891 18143347455903618883901837)
              ·
                refine ⟨6803755295963857081463189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18143347455903618883901837 6803755295963857081463189)
                ·
                  refine ⟨318926029498305800693587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6803755295963857081463189 318926029498305800693587)
                  ·
                    rfl

theorem cell21_1397489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_1397489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397489 prefixEnd_1397489 := by exact prefixLift 1397489
  have htrace : WordTrace (prefixWord ++ tailWord_1397489) baseStart_1397489 baseEnd_1397489 := by
    simpa [prefixWord, tailWord_1397489, baseEnd_1397489] using wordTrace_append hprefix tailTrace_1397489
  have hstable : (prefixWord ++ tailWord_1397489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397489).length < 2 ^ (prefixWord ++ tailWord_1397489).sum := by decide
  have hdescent : baseEnd_1397489 < baseStart_1397489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397585 : List Nat := [1, 2, 2, 1, 6, 1, 2, 3, 3]
def baseStart_1397585 : Nat := 118140960795 + 1397585 * 2 ^ 59
def prefixEnd_1397585 : Nat := 4983230072969 + 3 ^ 40 * 1397585 * 2
def baseEnd_1397585 : Nat := 318947938006230967093391

theorem tailTrace_1397585 : CollatzResearch.WordTrace tailWord_1397585 prefixEnd_1397585 318947938006230967093391 := by
  unfold tailWord_1397585
  simp only [CollatzResearch.WordTrace]
  refine ⟨50974112641795708360146209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33982741761197138906764139 50974112641795708360146209)
  ·
    refine ⟨38230584481346781270109657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50974112641795708360146209 38230584481346781270109657)
    ·
      refine ⟨28672938361010085952582243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38230584481346781270109657 28672938361010085952582243)
      ·
        refine ⟨43009407541515128928873365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28672938361010085952582243 43009407541515128928873365)
        ·
          refine ⟨2016065978508521668540939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43009407541515128928873365 2016065978508521668540939)
          ·
            refine ⟨3024098967762782502811409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016065978508521668540939 3024098967762782502811409)
            ·
              refine ⟨2268074225822086877108557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3024098967762782502811409 2268074225822086877108557)
              ·
                refine ⟨850527834683282578915709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2268074225822086877108557 850527834683282578915709)
                ·
                  refine ⟨318947938006230967093391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850527834683282578915709 318947938006230967093391)
                  ·
                    rfl

theorem cell21_1397585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 3].length) (baseStart_1397585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397585 prefixEnd_1397585 := by exact prefixLift 1397585
  have htrace : WordTrace (prefixWord ++ tailWord_1397585) baseStart_1397585 baseEnd_1397585 := by
    simpa [prefixWord, tailWord_1397585, baseEnd_1397585] using wordTrace_append hprefix tailTrace_1397585
  have hstable : (prefixWord ++ tailWord_1397585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397585).length < 2 ^ (prefixWord ++ tailWord_1397585).sum := by decide
  have hdescent : baseEnd_1397585 < baseStart_1397585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397630 : List Nat := [4, 2, 3, 1, 2, 1, 1, 7]
def baseStart_1397630 : Nat := 118140960795 + 1397630 * 2 ^ 59
def prefixEnd_1397630 : Nat := 4983230072969 + 3 ^ 40 * 1397630 * 2
def baseEnd_1397630 : Nat := 106319402539773629614433

theorem tailTrace_1397630 : CollatzResearch.WordTrace tailWord_1397630 prefixEnd_1397630 106319402539773629614433 := by
  unfold tailWord_1397630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6371969240829085130691793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33983835951088454030356229 6371969240829085130691793)
  ·
    refine ⟨4778976930621813848018845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6371969240829085130691793 4778976930621813848018845)
    ·
      refine ⟨1792116348983180193007067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4778976930621813848018845 1792116348983180193007067)
      ·
        refine ⟨2688174523474770289510601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792116348983180193007067 2688174523474770289510601)
        ·
          refine ⟨2016130892606077717132951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2688174523474770289510601 2016130892606077717132951)
          ·
            refine ⟨3024196338909116575699427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016130892606077717132951 3024196338909116575699427)
            ·
              refine ⟨4536294508363674863549141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024196338909116575699427 4536294508363674863549141)
              ·
                refine ⟨106319402539773629614433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4536294508363674863549141 106319402539773629614433)
                ·
                  rfl

theorem cell21_1397630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_1397630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397630 prefixEnd_1397630 := by exact prefixLift 1397630
  have htrace : WordTrace (prefixWord ++ tailWord_1397630) baseStart_1397630 baseEnd_1397630 := by
    simpa [prefixWord, tailWord_1397630, baseEnd_1397630] using wordTrace_append hprefix tailTrace_1397630
  have hstable : (prefixWord ++ tailWord_1397630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397630).length < 2 ^ (prefixWord ++ tailWord_1397630).sum := by decide
  have hdescent : baseEnd_1397630 < baseStart_1397630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397641 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 6]
def baseStart_1397641 : Nat := 118140960795 + 1397641 * 2 ^ 59
def prefixEnd_1397641 : Nat := 4983230072969 + 3 ^ 40 * 1397641 * 2
def baseEnd_1397641 : Nat := 318960717969187314159943

theorem tailTrace_1397641 : CollatzResearch.WordTrace tailWord_1397641 prefixEnd_1397641 318960717969187314159943 := by
  unfold tailWord_1397641
  simp only [CollatzResearch.WordTrace]
  refine ⟨50976155129592829924184777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33984103419728553282789851 50976155129592829924184777)
  ·
    refine ⟨38232116347194622443138583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50976155129592829924184777 38232116347194622443138583)
    ·
      refine ⟨57348174520791933664707875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38232116347194622443138583 57348174520791933664707875)
      ·
        refine ⟨86022261781187900497061813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57348174520791933664707875 86022261781187900497061813)
        ·
          refine ⟨8064587041986365671599545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86022261781187900497061813 8064587041986365671599545)
          ·
            refine ⟨6048440281489774253699659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8064587041986365671599545 6048440281489774253699659)
            ·
              refine ⟨9072660422234661380549489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6048440281489774253699659 9072660422234661380549489)
              ·
                refine ⟨6804495316675996035412117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9072660422234661380549489 6804495316675996035412117)
                ·
                  refine ⟨318960717969187314159943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6804495316675996035412117 318960717969187314159943)
                  ·
                    rfl

theorem cell21_1397641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_1397641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397641 prefixEnd_1397641 := by exact prefixLift 1397641
  have htrace : WordTrace (prefixWord ++ tailWord_1397641) baseStart_1397641 baseEnd_1397641 := by
    simpa [prefixWord, tailWord_1397641, baseEnd_1397641] using wordTrace_append hprefix tailTrace_1397641
  have hstable : (prefixWord ++ tailWord_1397641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397641).length < 2 ^ (prefixWord ++ tailWord_1397641).sum := by decide
  have hdescent : baseEnd_1397641 < baseStart_1397641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397644 : List Nat := [2, 2, 1, 2, 1, 2, 5, 3, 3]
def baseStart_1397644 : Nat := 118140960795 + 1397644 * 2 ^ 59
def prefixEnd_1397644 : Nat := 4983230072969 + 3 ^ 40 * 1397644 * 2
def baseEnd_1397644 : Nat := 318961402610059975609937

theorem tailTrace_1397644 : CollatzResearch.WordTrace tailWord_1397644 prefixEnd_1397644 318961402610059975609937 := by
  unfold tailWord_1397644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25488132274290980718271993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33984176365721307624362657 25488132274290980718271993)
  ·
    refine ⟨19116099205718235538703995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25488132274290980718271993 19116099205718235538703995)
    ·
      refine ⟨28674148808577353308055993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19116099205718235538703995 28674148808577353308055993)
      ·
        refine ⟨21505611606433014981041995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28674148808577353308055993 21505611606433014981041995)
        ·
          refine ⟨32258417409649522471562993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21505611606433014981041995 32258417409649522471562993)
          ·
            refine ⟨24193813057237141853672245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32258417409649522471562993 24193813057237141853672245)
            ·
              refine ⟨2268169974115982048781773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24193813057237141853672245 2268169974115982048781773)
              ·
                refine ⟨850563740293493268293165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2268169974115982048781773 850563740293493268293165)
                ·
                  refine ⟨318961402610059975609937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850563740293493268293165 318961402610059975609937)
                  ·
                    rfl

theorem cell21_1397644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_1397644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397644 prefixEnd_1397644 := by exact prefixLift 1397644
  have htrace : WordTrace (prefixWord ++ tailWord_1397644) baseStart_1397644 baseEnd_1397644 := by
    simpa [prefixWord, tailWord_1397644, baseEnd_1397644] using wordTrace_append hprefix tailTrace_1397644
  have hstable : (prefixWord ++ tailWord_1397644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397644).length < 2 ^ (prefixWord ++ tailWord_1397644).sum := by decide
  have hdescent : baseEnd_1397644 < baseStart_1397644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397661 : List Nat := [1, 4, 2, 1, 2, 1, 5, 2, 3]
def baseStart_1397661 : Nat := 118140960795 + 1397661 * 2 ^ 59
def prefixEnd_1397661 : Nat := 4983230072969 + 3 ^ 40 * 1397661 * 2
def baseEnd_1397661 : Nat := 318965282241671723826569

theorem tailTrace_1397661 : CollatzResearch.WordTrace tailWord_1397661 prefixEnd_1397661 318965282241671723826569 := by
  unfold tailWord_1397661
  simp only [CollatzResearch.WordTrace]
  refine ⟨50976884589520373339912837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33984589726346915559941891 50976884589520373339912837)
  ·
    refine ⟨9558165860535070001233657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50976884589520373339912837 9558165860535070001233657)
    ·
      refine ⟨7168624395401302500925243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9558165860535070001233657 7168624395401302500925243)
      ·
        refine ⟨10752936593101953751387865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7168624395401302500925243 10752936593101953751387865)
        ·
          refine ⟨8064702444826465313540899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10752936593101953751387865 8064702444826465313540899)
          ·
            refine ⟨12097053667239697970311349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8064702444826465313540899 12097053667239697970311349)
            ·
              refine ⟨1134098781303721684716689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12097053667239697970311349 1134098781303721684716689)
              ·
                refine ⟨850574085977791263537517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134098781303721684716689 850574085977791263537517)
                ·
                  refine ⟨318965282241671723826569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850574085977791263537517 318965282241671723826569)
                  ·
                    rfl

theorem cell21_1397661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_1397661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397661 prefixEnd_1397661 := by exact prefixLift 1397661
  have htrace : WordTrace (prefixWord ++ tailWord_1397661) baseStart_1397661 baseEnd_1397661 := by
    simpa [prefixWord, tailWord_1397661, baseEnd_1397661] using wordTrace_append hprefix tailTrace_1397661
  have hstable : (prefixWord ++ tailWord_1397661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397661).length < 2 ^ (prefixWord ++ tailWord_1397661).sum := by decide
  have hdescent : baseEnd_1397661 < baseStart_1397661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397720 : List Nat := [2, 1, 2, 2, 2, 4, 1, 4, 3]
def baseStart_1397720 : Nat := 118140960795 + 1397720 * 2 ^ 59
def prefixEnd_1397720 : Nat := 4983230072969 + 3 ^ 40 * 1397720 * 2
def baseEnd_1397720 : Nat := 318978746845500732343115

theorem tailTrace_1397720 : CollatzResearch.WordTrace tailWord_1397720 prefixEnd_1397720 318978746845500732343115 := by
  unfold tailWord_1397720
  simp only [CollatzResearch.WordTrace]
  refine ⟨25489518248153313208155307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33986024330871084277540409 25489518248153313208155307)
  ·
    refine ⟨38234277372229969812232961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25489518248153313208155307 38234277372229969812232961)
    ·
      refine ⟨28675708029172477359174721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38234277372229969812232961 28675708029172477359174721)
      ·
        refine ⟨21506781021879358019381041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28675708029172477359174721 21506781021879358019381041)
        ·
          refine ⟨16130085766409518514535781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21506781021879358019381041 16130085766409518514535781)
          ·
            refine ⟨3024391081201784721475459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16130085766409518514535781 3024391081201784721475459)
            ·
              refine ⟨4536586621802677082213189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024391081201784721475459 4536586621802677082213189)
              ·
                refine ⟨850609991588001952914973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4536586621802677082213189 850609991588001952914973)
                ·
                  refine ⟨318978746845500732343115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850609991588001952914973 318978746845500732343115)
                  ·
                    rfl

theorem cell21_1397720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 3].length) (baseStart_1397720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397720 prefixEnd_1397720 := by exact prefixLift 1397720
  have htrace : WordTrace (prefixWord ++ tailWord_1397720) baseStart_1397720 baseEnd_1397720 := by
    simpa [prefixWord, tailWord_1397720, baseEnd_1397720] using wordTrace_append hprefix tailTrace_1397720
  have hstable : (prefixWord ++ tailWord_1397720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397720).length < 2 ^ (prefixWord ++ tailWord_1397720).sum := by decide
  have hdescent : baseEnd_1397720 < baseStart_1397720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397889 : List Nat := [1, 2, 4, 2, 2, 1, 4, 2, 3]
def baseStart_1397889 : Nat := 118140960795 + 1397889 * 2 ^ 59
def prefixEnd_1397889 : Nat := 4983230072969 + 3 ^ 40 * 1397889 * 2
def baseEnd_1397889 : Nat := 319017314947993994026103

theorem tailTrace_1397889 : CollatzResearch.WordTrace tailWord_1397889 prefixEnd_1397889 319017314947993994026103 := by
  unfold tailWord_1397889
  simp only [CollatzResearch.WordTrace]
  refine ⟨50985200432694368279212721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33990133621796245519475147 50985200432694368279212721)
  ·
    refine ⟨38238900324520776209409541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50985200432694368279212721 38238900324520776209409541)
    ·
      refine ⟨7169793810847645539264289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38238900324520776209409541 7169793810847645539264289)
      ·
        refine ⟨5377345358135734154448217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7169793810847645539264289 5377345358135734154448217)
        ·
          refine ⟨4033009018601800615836163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5377345358135734154448217 4033009018601800615836163)
          ·
            refine ⟨6049513527902700923754245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033009018601800615836163 6049513527902700923754245)
            ·
              refine ⟨1134283786481756423203921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6049513527902700923754245 1134283786481756423203921)
              ·
                refine ⟨850712839861317317402941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134283786481756423203921 850712839861317317402941)
                ·
                  refine ⟨319017314947993994026103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850712839861317317402941 319017314947993994026103)
                  ·
                    rfl

theorem cell21_1397889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 3].length) (baseStart_1397889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397889 prefixEnd_1397889 := by exact prefixLift 1397889
  have htrace : WordTrace (prefixWord ++ tailWord_1397889) baseStart_1397889 baseEnd_1397889 := by
    simpa [prefixWord, tailWord_1397889, baseEnd_1397889] using wordTrace_append hprefix tailTrace_1397889
  have hstable : (prefixWord ++ tailWord_1397889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397889).length < 2 ^ (prefixWord ++ tailWord_1397889).sum := by decide
  have hdescent : baseEnd_1397889 < baseStart_1397889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397945 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 6]
def baseStart_1397945 : Nat := 118140960795 + 1397945 * 2 ^ 59
def prefixEnd_1397945 : Nat := 4983230072969 + 3 ^ 40 * 1397945 * 2
def baseEnd_1397945 : Nat := 319030094910950341092655

theorem tailTrace_1397945 : CollatzResearch.WordTrace tailWord_1397945 prefixEnd_1397945 319030094910950341092655 := by
  unfold tailWord_1397945
  simp only [CollatzResearch.WordTrace]
  refine ⟨50987242920491489843251289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33991495280327659895500859 50987242920491489843251289)
  ·
    refine ⟨38240432190368617382438467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50987242920491489843251289 38240432190368617382438467)
    ·
      refine ⟨57360648285552926073657701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38240432190368617382438467 57360648285552926073657701)
      ·
        refine ⟨10755121553541173638810819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57360648285552926073657701 10755121553541173638810819)
        ·
          refine ⟨16132682330311760458216229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10755121553541173638810819 16132682330311760458216229)
          ·
            refine ⟨3024877936933455085915543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16132682330311760458216229 3024877936933455085915543)
            ·
              refine ⟨4537316905400182628873315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024877936933455085915543 4537316905400182628873315)
              ·
                refine ⟨6805975358100273943309973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537316905400182628873315 6805975358100273943309973)
                ·
                  refine ⟨319030094910950341092655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6805975358100273943309973 319030094910950341092655)
                  ·
                    rfl

theorem cell21_1397945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_1397945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397945 prefixEnd_1397945 := by exact prefixLift 1397945
  have htrace : WordTrace (prefixWord ++ tailWord_1397945) baseStart_1397945 baseEnd_1397945 := by
    simpa [prefixWord, tailWord_1397945, baseEnd_1397945] using wordTrace_append hprefix tailTrace_1397945
  have hstable : (prefixWord ++ tailWord_1397945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397945).length < 2 ^ (prefixWord ++ tailWord_1397945).sum := by decide
  have hdescent : baseEnd_1397945 < baseStart_1397945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397948 : List Nat := [2, 2, 2, 3, 2, 1, 2, 4, 3]
def baseStart_1397948 : Nat := 118140960795 + 1397948 * 2 ^ 59
def prefixEnd_1397948 : Nat := 4983230072969 + 3 ^ 40 * 1397948 * 2
def baseEnd_1397948 : Nat := 319030779551823002542649

theorem tailTrace_1397948 : CollatzResearch.WordTrace tailWord_1397948 prefixEnd_1397948 319030779551823002542649 := by
  unfold tailWord_1397948
  simp only [CollatzResearch.WordTrace]
  refine ⟨25493676169740310677805249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33991568226320414237073665 25493676169740310677805249)
  ·
    refine ⟨19120257127305233008353937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25493676169740310677805249 19120257127305233008353937)
    ·
      refine ⟨14340192845478924756265453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19120257127305233008353937 14340192845478924756265453)
      ·
        refine ⟨5377572317054596783599545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14340192845478924756265453 5377572317054596783599545)
        ·
          refine ⟨4033179237790947587699659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5377572317054596783599545 4033179237790947587699659)
          ·
            refine ⟨6049768856686421381549489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033179237790947587699659 6049768856686421381549489)
            ·
              refine ⟨4537326642514816036162117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6049768856686421381549489 4537326642514816036162117)
              ·
                refine ⟨850748745471528006780397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4537326642514816036162117 850748745471528006780397)
                ·
                  refine ⟨319030779551823002542649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850748745471528006780397 319030779551823002542649)
                  ·
                    rfl

theorem cell21_1397948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_1397948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397948 prefixEnd_1397948 := by exact prefixLift 1397948
  have htrace : WordTrace (prefixWord ++ tailWord_1397948) baseStart_1397948 baseEnd_1397948 := by
    simpa [prefixWord, tailWord_1397948, baseEnd_1397948] using wordTrace_append hprefix tailTrace_1397948
  have hstable : (prefixWord ++ tailWord_1397948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397948).length < 2 ^ (prefixWord ++ tailWord_1397948).sum := by decide
  have hdescent : baseEnd_1397948 < baseStart_1397948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397976 : List Nat := [2, 1, 2, 2, 5, 1, 1, 7]
def baseStart_1397976 : Nat := 118140960795 + 1397976 * 2 ^ 59
def prefixEnd_1397976 : Nat := 4983230072969 + 3 ^ 40 * 1397976 * 2
def baseEnd_1397976 : Nat := 106345723177767058691975

theorem tailTrace_1397976 : CollatzResearch.WordTrace tailWord_1397976 prefixEnd_1397976 106345723177767058691975 := by
  unfold tailWord_1397976
  simp only [CollatzResearch.WordTrace]
  refine ⟨25494186791689591068814891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33992249055586121425086521 25494186791689591068814891)
  ·
    refine ⟨38241280187534386603222337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25494186791689591068814891 38241280187534386603222337)
    ·
      refine ⟨28680960140650789952416753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38241280187534386603222337 28680960140650789952416753)
      ·
        refine ⟨21510720105488092464312565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28680960140650789952416753 21510720105488092464312565)
        ·
          refine ⟨2016630009889508668529303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21510720105488092464312565 2016630009889508668529303)
          ·
            refine ⟨3024945014834263002793955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016630009889508668529303 3024945014834263002793955)
            ·
              refine ⟨4537417522251394504190933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024945014834263002793955 4537417522251394504190933)
              ·
                refine ⟨106345723177767058691975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4537417522251394504190933 106345723177767058691975)
                ·
                  rfl

theorem cell21_1397976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_1397976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1397976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1397976 prefixEnd_1397976 := by exact prefixLift 1397976
  have htrace : WordTrace (prefixWord ++ tailWord_1397976) baseStart_1397976 baseEnd_1397976 := by
    simpa [prefixWord, tailWord_1397976, baseEnd_1397976] using wordTrace_append hprefix tailTrace_1397976
  have hstable : (prefixWord ++ tailWord_1397976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397976).length < 2 ^ (prefixWord ++ tailWord_1397976).sum := by decide
  have hdescent : baseEnd_1397976 < baseStart_1397976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398021 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 4]
def baseStart_1398021 : Nat := 118140960795 + 1398021 * 2 ^ 59
def prefixEnd_1398021 : Nat := 4983230072969 + 3 ^ 40 * 1398021 * 2
def baseEnd_1398021 : Nat := 319047439146391097825833

theorem tailTrace_1398021 : CollatzResearch.WordTrace tailWord_1398021 prefixEnd_1398021 319047439146391097825833 := by
  unfold tailWord_1398021
  simp only [CollatzResearch.WordTrace]
  refine ⟨50990014868216154823017917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33993343245477436548678611 50990014868216154823017917)
  ·
    refine ⟨19121255575581058058631719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50990014868216154823017917 19121255575581058058631719)
    ·
      refine ⟨28681883363371587087947579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19121255575581058058631719 28681883363371587087947579)
      ·
        refine ⟨43022825045057380631921369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28681883363371587087947579 43022825045057380631921369)
        ·
          refine ⟨32267118783793035473941027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43022825045057380631921369 32267118783793035473941027)
          ·
            refine ⟨48400678175689553210911541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32267118783793035473941027 48400678175689553210911541)
            ·
              refine ⟨4537563578970895613522957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48400678175689553210911541 4537563578970895613522957)
              ·
                refine ⟨1701586342114085855071109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4537563578970895613522957 1701586342114085855071109)
                ·
                  refine ⟨319047439146391097825833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1701586342114085855071109 319047439146391097825833)
                  ·
                    rfl

theorem cell21_1398021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_1398021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398021 prefixEnd_1398021 := by exact prefixLift 1398021
  have htrace : WordTrace (prefixWord ++ tailWord_1398021) baseStart_1398021 baseEnd_1398021 := by
    simpa [prefixWord, tailWord_1398021, baseEnd_1398021] using wordTrace_append hprefix tailTrace_1398021
  have hstable : (prefixWord ++ tailWord_1398021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398021).length < 2 ^ (prefixWord ++ tailWord_1398021).sum := by decide
  have hdescent : baseEnd_1398021 < baseStart_1398021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398058 : List Nat := [3, 1, 4, 2, 1, 3, 2, 2, 3]
def baseStart_1398058 : Nat := 118140960795 + 1398058 * 2 ^ 59
def prefixEnd_1398058 : Nat := 4983230072969 + 3 ^ 40 * 1398058 * 2
def baseEnd_1398058 : Nat := 319055883050487255709091

theorem tailTrace_1398058 : CollatzResearch.WordTrace tailWord_1398058 prefixEnd_1398058 319055883050487255709091 := by
  unfold tailWord_1398058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12747841092270527535528707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33994242912721406761409885 12747841092270527535528707)
  ·
    refine ⟨19121761638405791303293061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12747841092270527535528707 19121761638405791303293061)
    ·
      refine ⟨3585330307201085869367449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19121761638405791303293061 3585330307201085869367449)
      ·
        refine ⟨2688997730400814402025587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3585330307201085869367449 2688997730400814402025587)
        ·
          refine ⟨4033496595601221603038381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688997730400814402025587 4033496595601221603038381)
          ·
            refine ⟨1512561223350458101139393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4033496595601221603038381 1512561223350458101139393)
            ·
              refine ⟨1134420917512843575854545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1512561223350458101139393 1134420917512843575854545)
              ·
                refine ⟨850815688134632681890909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134420917512843575854545 850815688134632681890909)
                ·
                  refine ⟨319055883050487255709091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850815688134632681890909 319055883050487255709091)
                  ·
                    rfl

theorem cell21_1398058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_1398058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398058 prefixEnd_1398058 := by exact prefixLift 1398058
  have htrace : WordTrace (prefixWord ++ tailWord_1398058) baseStart_1398058 baseEnd_1398058 := by
    simpa [prefixWord, tailWord_1398058, baseEnd_1398058] using wordTrace_append hprefix tailTrace_1398058
  have hstable : (prefixWord ++ tailWord_1398058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398058).length < 2 ^ (prefixWord ++ tailWord_1398058).sum := by decide
  have hdescent : baseEnd_1398058 < baseStart_1398058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398100 : List Nat := [2, 4, 1, 1, 2, 1, 4, 3, 3]
def baseStart_1398100 : Nat := 118140960795 + 1398100 * 2 ^ 59
def prefixEnd_1398100 : Nat := 4983230072969 + 3 ^ 40 * 1398100 * 2
def baseEnd_1398100 : Nat := 319065468022704516009005

theorem tailTrace_1398100 : CollatzResearch.WordTrace tailWord_1398100 prefixEnd_1398100 319065468022704516009005 := by
  unfold tailWord_1398100
  simp only [CollatzResearch.WordTrace]
  refine ⟨25496448117464975657571877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33995264156619967543429169 25496448117464975657571877)
  ·
    refine ⟨4780584022024682935794727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25496448117464975657571877 4780584022024682935794727)
    ·
      refine ⟨7170876033037024403692091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4780584022024682935794727 7170876033037024403692091)
      ·
        refine ⟨10756314049555536605538137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7170876033037024403692091 10756314049555536605538137)
        ·
          refine ⟨8067235537166652454153603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10756314049555536605538137 8067235537166652454153603)
          ·
            refine ⟨12100853305749978681230405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8067235537166652454153603 12100853305749978681230405)
            ·
              refine ⟨2268909994828121002730701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12100853305749978681230405 2268909994828121002730701)
              ·
                refine ⟨850841248060545376024013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2268909994828121002730701 850841248060545376024013)
                ·
                  refine ⟨319065468022704516009005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850841248060545376024013 319065468022704516009005)
                  ·
                    rfl

theorem cell21_1398100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_1398100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398100 prefixEnd_1398100 := by exact prefixLift 1398100
  have htrace : WordTrace (prefixWord ++ tailWord_1398100) baseStart_1398100 baseEnd_1398100 := by
    simpa [prefixWord, tailWord_1398100, baseEnd_1398100] using wordTrace_append hprefix tailTrace_1398100
  have hstable : (prefixWord ++ tailWord_1398100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398100).length < 2 ^ (prefixWord ++ tailWord_1398100).sum := by decide
  have hdescent : baseEnd_1398100 < baseStart_1398100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398156 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_1398156 : Nat := 118140960795 + 1398156 * 2 ^ 59
def prefixEnd_1398156 : Nat := 4983230072969 + 3 ^ 40 * 1398156 * 2
def baseEnd_1398156 : Nat := 319078247985660863075557

theorem tailTrace_1398156 : CollatzResearch.WordTrace tailWord_1398156 prefixEnd_1398156 319078247985660863075557 := by
  unfold tailWord_1398156
  simp only [CollatzResearch.WordTrace]
  refine ⟨25497469361363536439591161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33996625815151381919454881 25497469361363536439591161)
  ·
    refine ⟨19123102021022652329693371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25497469361363536439591161 19123102021022652329693371)
    ·
      refine ⟨28684653031533978494540057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19123102021022652329693371 28684653031533978494540057)
      ·
        refine ⟨21513489773650483870905043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28684653031533978494540057 21513489773650483870905043)
        ·
          refine ⟨32270234660475725806357565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21513489773650483870905043 32270234660475725806357565)
          ·
            refine ⟨12101337997678397177384087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32270234660475725806357565 12101337997678397177384087)
            ·
              refine ⟨18152006996517595766076131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12101337997678397177384087 18152006996517595766076131)
              ·
                refine ⟨27228010494776393649114197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18152006996517595766076131 27228010494776393649114197)
                ·
                  refine ⟨319078247985660863075557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27228010494776393649114197 319078247985660863075557)
                  ·
                    rfl

theorem cell21_1398156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_1398156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398156 prefixEnd_1398156 := by exact prefixLift 1398156
  have htrace : WordTrace (prefixWord ++ tailWord_1398156) baseStart_1398156 baseEnd_1398156 := by
    simpa [prefixWord, tailWord_1398156, baseEnd_1398156] using wordTrace_append hprefix tailTrace_1398156
  have hstable : (prefixWord ++ tailWord_1398156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398156).length < 2 ^ (prefixWord ++ tailWord_1398156).sum := by decide
  have hdescent : baseEnd_1398156 < baseStart_1398156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
