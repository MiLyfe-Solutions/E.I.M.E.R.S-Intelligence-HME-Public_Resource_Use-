import V185TrunkScan21Chunk093

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1141806 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_1141806 : Nat := 118140960795 + 1141806 * 2 ^ 59
def prefixEnd_1141806 : Nat := 4983230072969 + 3 ^ 40 * 1141806 * 2
def baseEnd_1141806 : Nat := 260575685416739961099527

theorem tailTrace_1141806 : CollatzResearch.WordTrace tailWord_1141806 prefixEnd_1141806 260575685416739961099527 := by
  unfold tailWord_1141806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5205635762679917723096659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27763390734292894523182181 5205635762679917723096659)
  ·
    refine ⟨7808453644019876584644989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5205635762679917723096659 7808453644019876584644989)
    ·
      refine ⟨2928170116507453719241871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7808453644019876584644989 2928170116507453719241871)
      ·
        refine ⟨4392255174761180578862807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2928170116507453719241871 4392255174761180578862807)
        ·
          refine ⟨6588382762141770868294211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4392255174761180578862807 6588382762141770868294211)
          ·
            refine ⟨9882574143212656302441317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6588382762141770868294211 9882574143212656302441317)
            ·
              refine ⟨1852982651852373056707747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9882574143212656302441317 1852982651852373056707747)
              ·
                refine ⟨2779473977778559585061621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852982651852373056707747 2779473977778559585061621)
                ·
                  refine ⟨260575685416739961099527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2779473977778559585061621 260575685416739961099527)
                  ·
                    rfl

theorem cell21_1141806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_1141806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141806 prefixEnd_1141806 := by exact prefixLift 1141806
  have htrace : WordTrace (prefixWord ++ tailWord_1141806) baseStart_1141806 baseEnd_1141806 := by
    simpa [prefixWord, tailWord_1141806, baseEnd_1141806] using wordTrace_append hprefix tailTrace_1141806
  have hstable : (prefixWord ++ tailWord_1141806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141806).length < 2 ^ (prefixWord ++ tailWord_1141806).sum := by decide
  have hdescent : baseEnd_1141806 < baseStart_1141806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141854 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1141854 : Nat := 118140960795 + 1141854 * 2 ^ 59
def prefixEnd_1141854 : Nat := 4983230072969 + 3 ^ 40 * 1141854 * 2
def baseEnd_1141854 : Nat := 260586639670702544299429

theorem tailTrace_1141854 : CollatzResearch.WordTrace tailWord_1141854 prefixEnd_1141854 260586639670702544299429 := by
  unfold tailWord_1141854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5205854600658180747815077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27764557870176963988347077 5205854600658180747815077)
  ·
    refine ⟨976097737623408890215327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5205854600658180747815077 976097737623408890215327)
    ·
      refine ⟨1464146606435113335322991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 976097737623408890215327 1464146606435113335322991)
      ·
        refine ⟨2196219909652670002984487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464146606435113335322991 2196219909652670002984487)
        ·
          refine ⟨3294329864479005004476731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196219909652670002984487 3294329864479005004476731)
          ·
            refine ⟨4941494796718507506715097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294329864479005004476731 4941494796718507506715097)
            ·
              refine ⟨3706121097538880630036323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4941494796718507506715097 3706121097538880630036323)
              ·
                refine ⟨5559181646308320945054485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3706121097538880630036323 5559181646308320945054485)
                ·
                  refine ⟨260586639670702544299429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5559181646308320945054485 260586639670702544299429)
                  ·
                    rfl

theorem cell21_1141854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1141854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141854 prefixEnd_1141854 := by exact prefixLift 1141854
  have htrace : WordTrace (prefixWord ++ tailWord_1141854) baseStart_1141854 baseEnd_1141854 := by
    simpa [prefixWord, tailWord_1141854, baseEnd_1141854] using wordTrace_append hprefix tailTrace_1141854
  have hstable : (prefixWord ++ tailWord_1141854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141854).length < 2 ^ (prefixWord ++ tailWord_1141854).sum := by decide
  have hdescent : baseEnd_1141854 < baseStart_1141854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141865 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 5]
def baseStart_1141865 : Nat := 118140960795 + 1141865 * 2 ^ 59
def prefixEnd_1141865 : Nat := 4983230072969 + 3 ^ 40 * 1141865 * 2
def baseEnd_1141865 : Nat := 260589150020568969616073

theorem tailTrace_1141865 : CollatzResearch.WordTrace tailWord_1141865 prefixEnd_1141865 260589150020568969616073 := by
  unfold tailWord_1141865
  simp only [CollatzResearch.WordTrace]
  refine ⟨41647238008225594861171049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27764825338817063240780699 41647238008225594861171049)
  ·
    refine ⟨31235428506169196145878287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41647238008225594861171049 31235428506169196145878287)
    ·
      refine ⟨46853142759253794218817431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31235428506169196145878287 46853142759253794218817431)
      ·
        refine ⟨70279714138880691328226147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46853142759253794218817431 70279714138880691328226147)
        ·
          refine ⟨105419571208321036992339221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70279714138880691328226147 105419571208321036992339221)
          ·
            refine ⟨4941542400390048609015901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105419571208321036992339221 4941542400390048609015901)
            ·
              refine ⟨1853078400146268228380963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4941542400390048609015901 1853078400146268228380963)
              ·
                refine ⟨2779617600219402342571445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853078400146268228380963 2779617600219402342571445)
                ·
                  refine ⟨260589150020568969616073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2779617600219402342571445 260589150020568969616073)
                  ·
                    rfl

theorem cell21_1141865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_1141865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141865 prefixEnd_1141865 := by exact prefixLift 1141865
  have htrace : WordTrace (prefixWord ++ tailWord_1141865) baseStart_1141865 baseEnd_1141865 := by
    simpa [prefixWord, tailWord_1141865, baseEnd_1141865] using wordTrace_append hprefix tailTrace_1141865
  have hstable : (prefixWord ++ tailWord_1141865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141865).length < 2 ^ (prefixWord ++ tailWord_1141865).sum := by decide
  have hdescent : baseEnd_1141865 < baseStart_1141865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141916 : List Nat := [2, 2, 3, 2, 1, 4, 2, 2, 3]
def baseStart_1141916 : Nat := 118140960795 + 1141916 * 2 ^ 59
def prefixEnd_1141916 : Nat := 4983230072969 + 3 ^ 40 * 1141916 * 2
def baseEnd_1141916 : Nat := 260600788915404214265969

theorem tailTrace_1141916 : CollatzResearch.WordTrace tailWord_1141916 prefixEnd_1141916 260600788915404214265969 := by
  unfold tailWord_1141916
  simp only [CollatzResearch.WordTrace]
  refine ⟨20824549065520415285638801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27766065420693887047518401 20824549065520415285638801)
  ·
    refine ⟨15618411799140311464229101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20824549065520415285638801 15618411799140311464229101)
    ·
      refine ⟨5856904424677616799085913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15618411799140311464229101 5856904424677616799085913)
      ·
        refine ⟨4392678318508212599314435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5856904424677616799085913 4392678318508212599314435)
        ·
          refine ⟨6589017477762318898971653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4392678318508212599314435 6589017477762318898971653)
          ·
            refine ⟨1235440777080434793557185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6589017477762318898971653 1235440777080434793557185)
            ·
              refine ⟨926580582810326095167889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235440777080434793557185 926580582810326095167889)
              ·
                refine ⟨694935437107744571375917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926580582810326095167889 694935437107744571375917)
                ·
                  refine ⟨260600788915404214265969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694935437107744571375917 260600788915404214265969)
                  ·
                    rfl

theorem cell21_1141916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_1141916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141916 prefixEnd_1141916 := by exact prefixLift 1141916
  have htrace : WordTrace (prefixWord ++ tailWord_1141916) baseStart_1141916 baseEnd_1141916 := by
    simpa [prefixWord, tailWord_1141916, baseEnd_1141916] using wordTrace_append hprefix tailTrace_1141916
  have hstable : (prefixWord ++ tailWord_1141916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141916).length < 2 ^ (prefixWord ++ tailWord_1141916).sum := by decide
  have hdescent : baseEnd_1141916 < baseStart_1141916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141927 : List Nat := [1, 1, 6, 2, 1, 1, 3, 6]
def baseStart_1141927 : Nat := 118140960795 + 1141927 * 2 ^ 59
def prefixEnd_1141927 : Nat := 4983230072969 + 3 ^ 40 * 1141927 * 2
def baseEnd_1141927 : Nat := 86867766421756879860871

theorem tailTrace_1141927 : CollatzResearch.WordTrace tailWord_1141927 prefixEnd_1141927 86867766421756879860871 := by
  unfold tailWord_1141927
  simp only [CollatzResearch.WordTrace]
  refine ⟨41649499334000979449928035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27766332889333986299952023 41649499334000979449928035)
  ·
    refine ⟨62474249001001469174892053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41649499334000979449928035 62474249001001469174892053)
    ·
      refine ⟨2928480421921943867573065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62474249001001469174892053 2928480421921943867573065)
      ·
        refine ⟨2196360316441457900679799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2928480421921943867573065 2196360316441457900679799)
        ·
          refine ⟨3294540474662186851019699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196360316441457900679799 3294540474662186851019699)
          ·
            refine ⟨4941810711993280276529549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294540474662186851019699 4941810711993280276529549)
            ·
              refine ⟨1853179016997480103698581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4941810711993280276529549 1853179016997480103698581)
              ·
                refine ⟨86867766421756879860871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1853179016997480103698581 86867766421756879860871)
                ·
                  rfl

theorem cell21_1141927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 6].length) (baseStart_1141927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141927 prefixEnd_1141927 := by exact prefixLift 1141927
  have htrace : WordTrace (prefixWord ++ tailWord_1141927) baseStart_1141927 baseEnd_1141927 := by
    simpa [prefixWord, tailWord_1141927, baseEnd_1141927] using wordTrace_append hprefix tailTrace_1141927
  have hstable : (prefixWord ++ tailWord_1141927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141927).length < 2 ^ (prefixWord ++ tailWord_1141927).sum := by decide
  have hdescent : baseEnd_1141927 < baseStart_1141927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142003 : List Nat := [1, 1, 1, 2, 2, 7, 2, 5]
def baseStart_1142003 : Nat := 118140960795 + 1142003 * 2 ^ 59
def prefixEnd_1142003 : Nat := 4983230072969 + 3 ^ 40 * 1142003 * 2
def baseEnd_1142003 : Nat := 86873547833570465438597

theorem tailTrace_1142003 : CollatzResearch.WordTrace tailWord_1142003 prefixEnd_1142003 86873547833570465438597 := by
  unfold tailWord_1142003
  simp only [CollatzResearch.WordTrace]
  refine ⟨41652271281725644429694663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27768180854483762953129775 41652271281725644429694663)
  ·
    refine ⟨62478406922588466644541995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41652271281725644429694663 62478406922588466644541995)
    ·
      refine ⟨93717610383882699966812993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62478406922588466644541995 93717610383882699966812993)
      ·
        refine ⟨70288207787912024975109745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93717610383882699966812993 70288207787912024975109745)
        ·
          refine ⟨52716155840934018731332309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70288207787912024975109745 52716155840934018731332309)
          ·
            refine ⟨1235534902521891064015601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 52716155840934018731332309 1235534902521891064015601)
            ·
              refine ⟨926651176891418298011701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235534902521891064015601 926651176891418298011701)
              ·
                refine ⟨86873547833570465438597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 926651176891418298011701 86873547833570465438597)
                ·
                  rfl

theorem cell21_1142003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 5].length) (baseStart_1142003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142003 prefixEnd_1142003 := by exact prefixLift 1142003
  have htrace : WordTrace (prefixWord ++ tailWord_1142003) baseStart_1142003 baseEnd_1142003 := by
    simpa [prefixWord, tailWord_1142003, baseEnd_1142003] using wordTrace_append hprefix tailTrace_1142003
  have hstable : (prefixWord ++ tailWord_1142003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142003).length < 2 ^ (prefixWord ++ tailWord_1142003).sum := by decide
  have hdescent : baseEnd_1142003 < baseStart_1142003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142158 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_1142158 : Nat := 118140960795 + 1142158 * 2 ^ 59
def prefixEnd_1142158 : Nat := 4983230072969 + 3 ^ 40 * 1142158 * 2
def baseEnd_1142158 : Nat := 260656016612465571232141

theorem tailTrace_1142158 : CollatzResearch.WordTrace tailWord_1142158 prefixEnd_1142158 260656016612465571232141 := by
  unfold tailWord_1142158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5207240574520513237698391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27771949730776070601058085 5207240574520513237698391)
  ·
    refine ⟨7810860861780769856547587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5207240574520513237698391 7810860861780769856547587)
    ·
      refine ⟨11716291292671154784821381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7810860861780769856547587 11716291292671154784821381)
      ·
        refine ⟨2196804617375841522154009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11716291292671154784821381 2196804617375841522154009)
        ·
          refine ⟨1647603463031881141615507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2196804617375841522154009 1647603463031881141615507)
          ·
            refine ⟨2471405194547821712423261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647603463031881141615507 2471405194547821712423261)
            ·
              refine ⟨926776947955433142158723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2471405194547821712423261 926776947955433142158723)
              ·
                refine ⟨1390165421933149713238085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926776947955433142158723 1390165421933149713238085)
                ·
                  refine ⟨260656016612465571232141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1390165421933149713238085 260656016612465571232141)
                  ·
                    rfl

theorem cell21_1142158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_1142158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142158 prefixEnd_1142158 := by exact prefixLift 1142158
  have htrace : WordTrace (prefixWord ++ tailWord_1142158) baseStart_1142158 baseEnd_1142158 := by
    simpa [prefixWord, tailWord_1142158, baseEnd_1142158] using wordTrace_append hprefix tailTrace_1142158
  have hstable : (prefixWord ++ tailWord_1142158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142158).length < 2 ^ (prefixWord ++ tailWord_1142158).sum := by decide
  have hdescent : baseEnd_1142158 < baseStart_1142158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142183 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 8]
def baseStart_1142183 : Nat := 118140960795 + 1142183 * 2 ^ 59
def prefixEnd_1142183 : Nat := 4983230072969 + 3 ^ 40 * 1142183 * 2
def baseEnd_1142183 : Nat := 260661721953071083315423

theorem tailTrace_1142183 : CollatzResearch.WordTrace tailWord_1142183 prefixEnd_1142183 260661721953071083315423 := by
  unfold tailWord_1142183
  simp only [CollatzResearch.WordTrace]
  refine ⟨41658836421073535171247203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27772557614049023447498135 41658836421073535171247203)
  ·
    refine ⟨62488254631610302756870805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41658836421073535171247203 62488254631610302756870805)
    ·
      refine ⟨2929136935856732941728319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62488254631610302756870805 2929136935856732941728319)
      ·
        refine ⟨4393705403785099412592479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2929136935856732941728319 4393705403785099412592479)
        ·
          refine ⟨6590558105677649118888719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4393705403785099412592479 6590558105677649118888719)
          ·
            refine ⟨9885837158516473678333079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6590558105677649118888719 9885837158516473678333079)
            ·
              refine ⟨14828755737774710517499619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9885837158516473678333079 14828755737774710517499619)
              ·
                refine ⟨22243133606662065776249429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14828755737774710517499619 22243133606662065776249429)
                ·
                  refine ⟨260661721953071083315423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22243133606662065776249429 260661721953071083315423)
                  ·
                    rfl

theorem cell21_1142183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_1142183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142183 prefixEnd_1142183 := by exact prefixLift 1142183
  have htrace : WordTrace (prefixWord ++ tailWord_1142183) baseStart_1142183 baseEnd_1142183 := by
    simpa [prefixWord, tailWord_1142183, baseEnd_1142183] using wordTrace_append hprefix tailTrace_1142183
  have hstable : (prefixWord ++ tailWord_1142183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142183).length < 2 ^ (prefixWord ++ tailWord_1142183).sum := by decide
  have hdescent : baseEnd_1142183 < baseStart_1142183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142394 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_1142394 : Nat := 118140960795 + 1142394 * 2 ^ 59
def prefixEnd_1142394 : Nat := 4983230072969 + 3 ^ 40 * 1142394 * 2
def baseEnd_1142394 : Nat := 260709875027781605298325

theorem tailTrace_1142394 : CollatzResearch.WordTrace tailWord_1142394 prefixEnd_1142394 260709875027781605298325 := by
  unfold tailWord_1142394
  simp only [CollatzResearch.WordTrace]
  refine ⟨10416633055827279551794559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27777688148872745471452157 10416633055827279551794559)
  ·
    refine ⟨15624949583740919327691839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10416633055827279551794559 15624949583740919327691839)
    ·
      refine ⟨23437424375611378991537759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15624949583740919327691839 23437424375611378991537759)
      ·
        refine ⟨35156136563417068487306639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23437424375611378991537759 35156136563417068487306639)
        ·
          refine ⟨52734204845125602730959959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35156136563417068487306639 52734204845125602730959959)
          ·
            refine ⟨79101307267688404096439939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52734204845125602730959959 79101307267688404096439939)
            ·
              refine ⟨118651960901532606144659909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79101307267688404096439939 118651960901532606144659909)
              ·
                refine ⟨22247242669037363652123733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118651960901532606144659909 22247242669037363652123733)
                ·
                  refine ⟨260709875027781605298325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22247242669037363652123733 260709875027781605298325)
                  ·
                    rfl

theorem cell21_1142394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_1142394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142394 prefixEnd_1142394 := by exact prefixLift 1142394
  have htrace : WordTrace (prefixWord ++ tailWord_1142394) baseStart_1142394 baseEnd_1142394 := by
    simpa [prefixWord, tailWord_1142394, baseEnd_1142394] using wordTrace_append hprefix tailTrace_1142394
  have hstable : (prefixWord ++ tailWord_1142394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142394).length < 2 ^ (prefixWord ++ tailWord_1142394).sum := by decide
  have hdescent : baseEnd_1142394 < baseStart_1142394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142431 : List Nat := [1, 1, 2, 7, 1, 1, 1, 4, 3]
def baseStart_1142431 : Nat := 118140960795 + 1142431 * 2 ^ 59
def prefixEnd_1142431 : Nat := 4983230072969 + 3 ^ 40 * 1142431 * 2
def baseEnd_1142431 : Nat := 260718318931877763181583

theorem tailTrace_1142431 : CollatzResearch.WordTrace tailWord_1142431 prefixEnd_1142431 260718318931877763181583 := by
  unfold tailWord_1142431
  simp only [CollatzResearch.WordTrace]
  refine ⟨41667881724175073526275147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27778587816116715684183431 41667881724175073526275147)
  ·
    refine ⟨62501822586262610289412721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41667881724175073526275147 62501822586262610289412721)
    ·
      refine ⟨46876366939696957717059541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62501822586262610289412721 46876366939696957717059541)
      ·
        refine ⟨1098664850149147446493583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 46876366939696957717059541 1098664850149147446493583)
        ·
          refine ⟨1647997275223721169740375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098664850149147446493583 1647997275223721169740375)
          ·
            refine ⟨2471995912835581754610563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647997275223721169740375 2471995912835581754610563)
            ·
              refine ⟨3707993869253372631915845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471995912835581754610563 3707993869253372631915845)
              ·
                refine ⟨695248850485007368484221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3707993869253372631915845 695248850485007368484221)
                ·
                  refine ⟨260718318931877763181583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695248850485007368484221 260718318931877763181583)
                  ·
                    rfl

theorem cell21_1142431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 3].length) (baseStart_1142431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142431 prefixEnd_1142431 := by exact prefixLift 1142431
  have htrace : WordTrace (prefixWord ++ tailWord_1142431) baseStart_1142431 baseEnd_1142431 := by
    simpa [prefixWord, tailWord_1142431, baseEnd_1142431] using wordTrace_append hprefix tailTrace_1142431
  have hstable : (prefixWord ++ tailWord_1142431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142431).length < 2 ^ (prefixWord ++ tailWord_1142431).sum := by decide
  have hdescent : baseEnd_1142431 < baseStart_1142431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142501 : List Nat := [1, 3, 1, 4, 1, 1, 2, 8]
def baseStart_1142501 : Nat := 118140960795 + 1142501 * 2 ^ 59
def prefixEnd_1142501 : Nat := 4983230072969 + 3 ^ 40 * 1142501 * 2
def baseEnd_1142501 : Nat := 86911431295191065671591

theorem tailTrace_1142501 : CollatzResearch.WordTrace tailWord_1142501 prefixEnd_1142501 86911431295191065671591 := by
  unfold tailWord_1142501
  simp only [CollatzResearch.WordTrace]
  refine ⟨41670434833921475481323357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27780289889280983654215571 41670434833921475481323357)
  ·
    refine ⟨15626413062720553305496259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41670434833921475481323357 15626413062720553305496259)
    ·
      refine ⟨23439619594080829958244389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15626413062720553305496259 23439619594080829958244389)
      ·
        refine ⟨4394928673890155617170823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23439619594080829958244389 4394928673890155617170823)
        ·
          refine ⟨6592393010835233425756235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4394928673890155617170823 6592393010835233425756235)
          ·
            refine ⟨9888589516252850138634353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6592393010835233425756235 9888589516252850138634353)
            ·
              refine ⟨7416442137189637603975765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9888589516252850138634353 7416442137189637603975765)
              ·
                refine ⟨86911431295191065671591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7416442137189637603975765 86911431295191065671591)
                ·
                  rfl

theorem cell21_1142501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 8].length) (baseStart_1142501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142501 prefixEnd_1142501 := by exact prefixLift 1142501
  have htrace : WordTrace (prefixWord ++ tailWord_1142501) baseStart_1142501 baseEnd_1142501 := by
    simpa [prefixWord, tailWord_1142501, baseEnd_1142501] using wordTrace_append hprefix tailTrace_1142501
  have hstable : (prefixWord ++ tailWord_1142501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142501).length < 2 ^ (prefixWord ++ tailWord_1142501).sum := by decide
  have hdescent : baseEnd_1142501 < baseStart_1142501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142518 : List Nat := [5, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1142518 : Nat := 118140960795 + 1142518 * 2 ^ 59
def prefixEnd_1142518 : Nat := 4983230072969 + 3 ^ 40 * 1142518 * 2
def baseEnd_1142518 : Nat := 86912724505728315077135

theorem tailTrace_1142518 : CollatzResearch.WordTrace tailWord_1142518 prefixEnd_1142518 86912724505728315077135 := by
  unfold tailWord_1142518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2604440929678742961543263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27780703249906591589794805 2604440929678742961543263)
  ·
    refine ⟨3906661394518114442314895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2604440929678742961543263 3906661394518114442314895)
    ·
      refine ⟨5859992091777171663472343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3906661394518114442314895 5859992091777171663472343)
      ·
        refine ⟨8789988137665757495208515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5859992091777171663472343 8789988137665757495208515)
        ·
          refine ⟨13184982206498636242812773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8789988137665757495208515 13184982206498636242812773)
          ·
            refine ⟨2472184163718494295527395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13184982206498636242812773 2472184163718494295527395)
            ·
              refine ⟨3708276245577741443291093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472184163718494295527395 3708276245577741443291093)
              ·
                refine ⟨86912724505728315077135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3708276245577741443291093 86912724505728315077135)
                ·
                  rfl

theorem cell21_1142518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1142518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142518 prefixEnd_1142518 := by exact prefixLift 1142518
  have htrace : WordTrace (prefixWord ++ tailWord_1142518) baseStart_1142518 baseEnd_1142518 := by
    simpa [prefixWord, tailWord_1142518, baseEnd_1142518] using wordTrace_append hprefix tailTrace_1142518
  have hstable : (prefixWord ++ tailWord_1142518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142518).length < 2 ^ (prefixWord ++ tailWord_1142518).sum := by decide
  have hdescent : baseEnd_1142518 < baseStart_1142518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142535 : List Nat := [1, 1, 4, 4, 3, 1, 7]
def baseStart_1142535 : Nat := 118140960795 + 1142535 * 2 ^ 59
def prefixEnd_1142535 : Nat := 4983230072969 + 3 ^ 40 * 1142535 * 2
def baseEnd_1142535 : Nat := 28971339238755188160893

theorem tailTrace_1142535 : CollatzResearch.WordTrace tailWord_1142535 prefixEnd_1142535 28971339238755188160893 := by
  unfold tailWord_1142535
  simp only [CollatzResearch.WordTrace]
  refine ⟨41671674915798299288061059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27781116610532199525374039 41671674915798299288061059)
  ·
    refine ⟨62507512373697448932091589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41671674915798299288061059 62507512373697448932091589)
    ·
      refine ⟨11720158570068271674767173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62507512373697448932091589 11720158570068271674767173)
      ·
        refine ⟨2197529731887800939018845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11720158570068271674767173 2197529731887800939018845)
        ·
          refine ⟨824073649457925352132067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2197529731887800939018845 824073649457925352132067)
          ·
            refine ⟨1236110474186888028198101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824073649457925352132067 1236110474186888028198101)
            ·
              refine ⟨28971339238755188160893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1236110474186888028198101 28971339238755188160893)
              ·
                rfl

theorem cell21_1142535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 7].length) (baseStart_1142535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142535 prefixEnd_1142535 := by exact prefixLift 1142535
  have htrace : WordTrace (prefixWord ++ tailWord_1142535) baseStart_1142535 baseEnd_1142535 := by
    simpa [prefixWord, tailWord_1142535, baseEnd_1142535] using wordTrace_append hprefix tailTrace_1142535
  have hstable : (prefixWord ++ tailWord_1142535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142535).length < 2 ^ (prefixWord ++ tailWord_1142535).sum := by decide
  have hdescent : baseEnd_1142535 < baseStart_1142535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142541 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1142541 : Nat := 118140960795 + 1142541 * 2 ^ 59
def prefixEnd_1142541 : Nat := 4983230072969 + 3 ^ 40 * 1142541 * 2
def baseEnd_1142541 : Nat := 260743422430542016348025

theorem tailTrace_1142541 : CollatzResearch.WordTrace tailWord_1142541 prefixEnd_1142541 260743422430542016348025 := by
  unfold tailWord_1142541
  simp only [CollatzResearch.WordTrace]
  refine ⟨41671893753776562312779477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27781262502517708208519651 41671893753776562312779477)
  ·
    refine ⟨976685009854138179205769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 41671893753776562312779477 976685009854138179205769)
    ·
      refine ⟨732513757390603634404327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 976685009854138179205769 732513757390603634404327)
      ·
        refine ⟨1098770636085905451606491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732513757390603634404327 1098770636085905451606491)
        ·
          refine ⟨1648155954128858177409737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098770636085905451606491 1648155954128858177409737)
          ·
            refine ⟨1236116965596643633057303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1648155954128858177409737 1236116965596643633057303)
            ·
              refine ⟨1854175448394965449585955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236116965596643633057303 1854175448394965449585955)
              ·
                refine ⟨2781263172592448174378933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854175448394965449585955 2781263172592448174378933)
                ·
                  refine ⟨260743422430542016348025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2781263172592448174378933 260743422430542016348025)
                  ·
                    rfl

theorem cell21_1142541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1142541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142541 prefixEnd_1142541 := by exact prefixLift 1142541
  have htrace : WordTrace (prefixWord ++ tailWord_1142541) baseStart_1142541 baseEnd_1142541 := by
    simpa [prefixWord, tailWord_1142541, baseEnd_1142541] using wordTrace_append hprefix tailTrace_1142541
  have hstable : (prefixWord ++ tailWord_1142541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142541).length < 2 ^ (prefixWord ++ tailWord_1142541).sum := by decide
  have hdescent : baseEnd_1142541 < baseStart_1142541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142549 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 5]
def baseStart_1142549 : Nat := 118140960795 + 1142549 * 2 ^ 59
def prefixEnd_1142549 : Nat := 4983230072969 + 3 ^ 40 * 1142549 * 2
def baseEnd_1142549 : Nat := 260745248139535780214675

theorem tailTrace_1142549 : CollatzResearch.WordTrace tailWord_1142549 prefixEnd_1142549 260745248139535780214675 := by
  unfold tailWord_1142549
  simp only [CollatzResearch.WordTrace]
  refine ⟨41672185537747579679070701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27781457025165053119380467 41672185537747579679070701)
  ·
    refine ⟨15627069576655342379651513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41672185537747579679070701 15627069576655342379651513)
    ·
      refine ⟨11720302182491506784738635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15627069576655342379651513 11720302182491506784738635)
      ·
        refine ⟨17580453273737260177107953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11720302182491506784738635 17580453273737260177107953)
        ·
          refine ⟨13185339955302945132830965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17580453273737260177107953 13185339955302945132830965)
          ·
            refine ⟨1236125620809651106202903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13185339955302945132830965 1236125620809651106202903)
            ·
              refine ⟨1854188431214476659304355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236125620809651106202903 1854188431214476659304355)
              ·
                refine ⟨2781282646821714988956533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854188431214476659304355 2781282646821714988956533)
                ·
                  refine ⟨260745248139535780214675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2781282646821714988956533 260745248139535780214675)
                  ·
                    rfl

theorem cell21_1142549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_1142549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142549 prefixEnd_1142549 := by exact prefixLift 1142549
  have htrace : WordTrace (prefixWord ++ tailWord_1142549) baseStart_1142549 baseEnd_1142549 := by
    simpa [prefixWord, tailWord_1142549, baseEnd_1142549] using wordTrace_append hprefix tailTrace_1142549
  have hstable : (prefixWord ++ tailWord_1142549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142549).length < 2 ^ (prefixWord ++ tailWord_1142549).sum := by decide
  have hdescent : baseEnd_1142549 < baseStart_1142549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142577 : List Nat := [1, 2, 2, 3, 2, 2, 2, 7]
def baseStart_1142577 : Nat := 118140960795 + 1142577 * 2 ^ 59
def prefixEnd_1142577 : Nat := 4983230072969 + 3 ^ 40 * 1142577 * 2
def baseEnd_1142577 : Nat := 86917212707004651249317

theorem tailTrace_1142577 : CollatzResearch.WordTrace tailWord_1142577 prefixEnd_1142577 86917212707004651249317 := by
  unfold tailWord_1142577
  simp only [CollatzResearch.WordTrace]
  refine ⟨41673206781646140461089985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27782137854430760307393323 41673206781646140461089985)
  ·
    refine ⟨31254905086234605345817489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41673206781646140461089985 31254905086234605345817489)
    ·
      refine ⟨23441178814675954009363117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31254905086234605345817489 23441178814675954009363117)
      ·
        refine ⟨8790442055503482753511169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23441178814675954009363117 8790442055503482753511169)
        ·
          refine ⟨6592831541627612065133377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8790442055503482753511169 6592831541627612065133377)
          ·
            refine ⟨4944623656220709048850033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6592831541627612065133377 4944623656220709048850033)
            ·
              refine ⟨3708467742165531786637525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4944623656220709048850033 3708467742165531786637525)
              ·
                refine ⟨86917212707004651249317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3708467742165531786637525 86917212707004651249317)
                ·
                  rfl

theorem cell21_1142577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 7].length) (baseStart_1142577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142577 prefixEnd_1142577 := by exact prefixLift 1142577
  have htrace : WordTrace (prefixWord ++ tailWord_1142577) baseStart_1142577 baseEnd_1142577 := by
    simpa [prefixWord, tailWord_1142577, baseEnd_1142577] using wordTrace_append hprefix tailTrace_1142577
  have hstable : (prefixWord ++ tailWord_1142577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142577).length < 2 ^ (prefixWord ++ tailWord_1142577).sum := by decide
  have hdescent : baseEnd_1142577 < baseStart_1142577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142687 : List Nat := [1, 1, 2, 5, 3, 2, 2, 5]
def baseStart_1142687 : Nat := 118140960795 + 1142687 * 2 ^ 59
def prefixEnd_1142687 : Nat := 4983230072969 + 3 ^ 40 * 1142687 * 2
def baseEnd_1142687 : Nat := 86925580539892735638131

theorem tailTrace_1142687 : CollatzResearch.WordTrace tailWord_1142687 prefixEnd_1142687 86925580539892735638131 := by
  unfold tailWord_1142687
  simp only [CollatzResearch.WordTrace]
  refine ⟨41677218811247629247594315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27784812540831752831729543 41677218811247629247594315)
  ·
    refine ⟨62515828216871443871391473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41677218811247629247594315 62515828216871443871391473)
    ·
      refine ⟨46886871162653582903543605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62515828216871443871391473 46886871162653582903543605)
      ·
        refine ⟨4395644171498773397207213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46886871162653582903543605 4395644171498773397207213)
        ·
          refine ⟨1648366564312040023952705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4395644171498773397207213 1648366564312040023952705)
          ·
            refine ⟨1236274923234030017964529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1648366564312040023952705 1236274923234030017964529)
            ·
              refine ⟨927206192425522513473397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236274923234030017964529 927206192425522513473397)
              ·
                refine ⟨86925580539892735638131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 927206192425522513473397 86925580539892735638131)
                ·
                  rfl

theorem cell21_1142687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 5].length) (baseStart_1142687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142687 prefixEnd_1142687 := by exact prefixLift 1142687
  have htrace : WordTrace (prefixWord ++ tailWord_1142687) baseStart_1142687 baseEnd_1142687 := by
    simpa [prefixWord, tailWord_1142687, baseEnd_1142687] using wordTrace_append hprefix tailTrace_1142687
  have hstable : (prefixWord ++ tailWord_1142687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142687).length < 2 ^ (prefixWord ++ tailWord_1142687).sum := by decide
  have hdescent : baseEnd_1142687 < baseStart_1142687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142732 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 4]
def baseStart_1142732 : Nat := 118140960795 + 1142732 * 2 ^ 59
def prefixEnd_1142732 : Nat := 4983230072969 + 3 ^ 40 * 1142732 * 2
def baseEnd_1142732 : Nat := 260787011232768128664301

theorem tailTrace_1142732 : CollatzResearch.WordTrace tailWord_1142732 prefixEnd_1142732 260787011232768128664301 := by
  unfold tailWord_1142732
  simp only [CollatzResearch.WordTrace]
  refine ⟨20839430048042300966491225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27785906730723067955321633 20839430048042300966491225)
  ·
    refine ⟨15629572536031725724868419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20839430048042300966491225 15629572536031725724868419)
    ·
      refine ⟨23444358804047588587302629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15629572536031725724868419 23444358804047588587302629)
      ·
        refine ⟨4395817275758922860119243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23444358804047588587302629 4395817275758922860119243)
        ·
          refine ⟨6593725913638384290178865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4395817275758922860119243 6593725913638384290178865)
          ·
            refine ⟨4945294435228788217634149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6593725913638384290178865 4945294435228788217634149)
            ·
              refine ⟨927242706605397790806403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4945294435228788217634149 927242706605397790806403)
              ·
                refine ⟨1390864059908096686209605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927242706605397790806403 1390864059908096686209605)
                ·
                  refine ⟨260787011232768128664301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1390864059908096686209605 260787011232768128664301)
                  ·
                    rfl

theorem cell21_1142732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_1142732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142732 prefixEnd_1142732 := by exact prefixLift 1142732
  have htrace : WordTrace (prefixWord ++ tailWord_1142732) baseStart_1142732 baseEnd_1142732 := by
    simpa [prefixWord, tailWord_1142732, baseEnd_1142732] using wordTrace_append hprefix tailTrace_1142732
  have hstable : (prefixWord ++ tailWord_1142732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142732).length < 2 ^ (prefixWord ++ tailWord_1142732).sum := by decide
  have hdescent : baseEnd_1142732 < baseStart_1142732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142743 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 7]
def baseStart_1142743 : Nat := 118140960795 + 1142743 * 2 ^ 59
def prefixEnd_1142743 : Nat := 4983230072969 + 3 ^ 40 * 1142743 * 2
def baseEnd_1142743 : Nat := 260789521582634553980945

theorem tailTrace_1142743 : CollatzResearch.WordTrace tailWord_1142743 prefixEnd_1142743 260789521582634553980945 := by
  unfold tailWord_1142743
  simp only [CollatzResearch.WordTrace]
  refine ⟨41679261299044750811632883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27786174199363167207755255 41679261299044750811632883)
  ·
    refine ⟨62518891948567126217449325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41679261299044750811632883 62518891948567126217449325)
    ·
      refine ⟨23444584480712672331543497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62518891948567126217449325 23444584480712672331543497)
      ·
        refine ⟨17583438360534504248657623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23444584480712672331543497 17583438360534504248657623)
        ·
          refine ⟨26375157540801756372986435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17583438360534504248657623 26375157540801756372986435)
          ·
            refine ⟨39562736311202634559479653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26375157540801756372986435 39562736311202634559479653)
            ·
              refine ⟨7418013058350493979902435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39562736311202634559479653 7418013058350493979902435)
              ·
                refine ⟨11127019587525740969853653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7418013058350493979902435 11127019587525740969853653)
                ·
                  refine ⟨260789521582634553980945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11127019587525740969853653 260789521582634553980945)
                  ·
                    rfl

theorem cell21_1142743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_1142743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142743 prefixEnd_1142743 := by exact prefixLift 1142743
  have htrace : WordTrace (prefixWord ++ tailWord_1142743) baseStart_1142743 baseEnd_1142743 := by
    simpa [prefixWord, tailWord_1142743, baseEnd_1142743] using wordTrace_append hprefix tailTrace_1142743
  have hstable : (prefixWord ++ tailWord_1142743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142743).length < 2 ^ (prefixWord ++ tailWord_1142743).sum := by decide
  have hdescent : baseEnd_1142743 < baseStart_1142743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142777 : List Nat := [1, 2, 1, 3, 1, 5, 1, 4, 3]
def baseStart_1142777 : Nat := 118140960795 + 1142777 * 2 ^ 59
def prefixEnd_1142777 : Nat := 4983230072969 + 3 ^ 40 * 1142777 * 2
def baseEnd_1142777 : Nat := 260797280845858050414209

theorem tailTrace_1142777 : CollatzResearch.WordTrace tailWord_1142777 prefixEnd_1142777 260797280845858050414209 := by
  unfold tailWord_1142777
  simp only [CollatzResearch.WordTrace]
  refine ⟨41680501380921574618370585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27787000920614383078913723 41680501380921574618370585)
  ·
    refine ⟨31260376035691180963777939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41680501380921574618370585 31260376035691180963777939)
    ·
      refine ⟨46890564053536771445666909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31260376035691180963777939 46890564053536771445666909)
      ·
        refine ⟨17583961520076289292125091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46890564053536771445666909 17583961520076289292125091)
        ·
          refine ⟨26375942280114433938187637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17583961520076289292125091 26375942280114433938187637)
          ·
            refine ⟨2472744588760728181705091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26375942280114433938187637 2472744588760728181705091)
            ·
              refine ⟨3709116883141092272557637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472744588760728181705091 3709116883141092272557637)
              ·
                refine ⟨695459415588954801104557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3709116883141092272557637 695459415588954801104557)
                ·
                  refine ⟨260797280845858050414209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695459415588954801104557 260797280845858050414209)
                  ·
                    rfl

theorem cell21_1142777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 3].length) (baseStart_1142777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142777 prefixEnd_1142777 := by exact prefixLift 1142777
  have htrace : WordTrace (prefixWord ++ tailWord_1142777) baseStart_1142777 baseEnd_1142777 := by
    simpa [prefixWord, tailWord_1142777, baseEnd_1142777] using wordTrace_append hprefix tailTrace_1142777
  have hstable : (prefixWord ++ tailWord_1142777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142777).length < 2 ^ (prefixWord ++ tailWord_1142777).sum := by decide
  have hdescent : baseEnd_1142777 < baseStart_1142777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142791 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 4]
def baseStart_1142791 : Nat := 118140960795 + 1142791 * 2 ^ 59
def prefixEnd_1142791 : Nat := 4983230072969 + 3 ^ 40 * 1142791 * 2
def baseEnd_1142791 : Nat := 260800475836597137180847

theorem tailTrace_1142791 : CollatzResearch.WordTrace tailWord_1142791 prefixEnd_1142791 260800475836597137180847 := by
  unfold tailWord_1142791
  simp only [CollatzResearch.WordTrace]
  refine ⟨41681012002870855009380227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27787341335247236672920151 41681012002870855009380227)
  ·
    refine ⟨62521518004306282514070341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41681012002870855009380227 62521518004306282514070341)
    ·
      refine ⟨11722784625807427971388189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62521518004306282514070341 11722784625807427971388189)
      ·
        refine ⟨4396044234677785489270571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11722784625807427971388189 4396044234677785489270571)
        ·
          refine ⟨6594066352016678233905857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4396044234677785489270571 6594066352016678233905857)
          ·
            refine ⟨4945549764012508675429393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6594066352016678233905857 4945549764012508675429393)
            ·
              refine ⟨3709162323009381506572045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4945549764012508675429393 3709162323009381506572045)
              ·
                refine ⟨1390935871128518064964517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3709162323009381506572045 1390935871128518064964517)
                ·
                  refine ⟨260800475836597137180847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1390935871128518064964517 260800475836597137180847)
                  ·
                    rfl

theorem cell21_1142791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 4].length) (baseStart_1142791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142791 prefixEnd_1142791 := by exact prefixLift 1142791
  have htrace : WordTrace (prefixWord ++ tailWord_1142791) baseStart_1142791 baseEnd_1142791 := by
    simpa [prefixWord, tailWord_1142791, baseEnd_1142791] using wordTrace_append hprefix tailTrace_1142791
  have hstable : (prefixWord ++ tailWord_1142791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142791).length < 2 ^ (prefixWord ++ tailWord_1142791).sum := by decide
  have hdescent : baseEnd_1142791 < baseStart_1142791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142797 : List Nat := [1, 7, 1, 2, 1, 1, 3, 5]
def baseStart_1142797 : Nat := 118140960795 + 1142797 * 2 ^ 59
def prefixEnd_1142797 : Nat := 4983230072969 + 3 ^ 40 * 1142797 * 2
def baseEnd_1142797 : Nat := 86933948372780820026945

theorem tailTrace_1142797 : CollatzResearch.WordTrace tailWord_1142797 prefixEnd_1142797 86933948372780820026945 := by
  unfold tailWord_1142797
  simp only [CollatzResearch.WordTrace]
  refine ⟨41681230840849118034098645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27787487227232745356065763 41681230840849118034098645)
  ·
    refine ⟨976903847832401203924187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 41681230840849118034098645 976903847832401203924187)
    ·
      refine ⟨1465355771748601805886281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 976903847832401203924187 1465355771748601805886281)
      ·
        refine ⟨1099016828811451354414711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1465355771748601805886281 1099016828811451354414711)
        ·
          refine ⟨1648525243217177031622067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099016828811451354414711 1648525243217177031622067)
          ·
            refine ⟨2472787864825765547433101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648525243217177031622067 2472787864825765547433101)
            ·
              refine ⟨927295449309662080287413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2472787864825765547433101 927295449309662080287413)
              ·
                refine ⟨86933948372780820026945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 927295449309662080287413 86933948372780820026945)
                ·
                  rfl

theorem cell21_1142797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 5].length) (baseStart_1142797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142797 prefixEnd_1142797 := by exact prefixLift 1142797
  have htrace : WordTrace (prefixWord ++ tailWord_1142797) baseStart_1142797 baseEnd_1142797 := by
    simpa [prefixWord, tailWord_1142797, baseEnd_1142797] using wordTrace_append hprefix tailTrace_1142797
  have hstable : (prefixWord ++ tailWord_1142797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142797).length < 2 ^ (prefixWord ++ tailWord_1142797).sum := by decide
  have hdescent : baseEnd_1142797 < baseStart_1142797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142819 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 7]
def baseStart_1142819 : Nat := 118140960795 + 1142819 * 2 ^ 59
def prefixEnd_1142819 : Nat := 4983230072969 + 3 ^ 40 * 1142819 * 2
def baseEnd_1142819 : Nat := 260806865818075310714123

theorem tailTrace_1142819 : CollatzResearch.WordTrace tailWord_1142819 prefixEnd_1142819 260806865818075310714123 := by
  unfold tailWord_1142819
  simp only [CollatzResearch.WordTrace]
  refine ⟨41682033246769415791399511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27788022164512943860933007 41682033246769415791399511)
  ·
    refine ⟨62523049870154123687099267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41682033246769415791399511 62523049870154123687099267)
    ·
      refine ⟨93784574805231185530648901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62523049870154123687099267 93784574805231185530648901)
      ·
        refine ⟨17584607775980847286996669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93784574805231185530648901 17584607775980847286996669)
        ·
          refine ⟨6594227915992817732623751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17584607775980847286996669 6594227915992817732623751)
          ·
            refine ⟨9891341873989226598935627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6594227915992817732623751 9891341873989226598935627)
            ·
              refine ⟨14837012810983839898403441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9891341873989226598935627 14837012810983839898403441)
              ·
                refine ⟨11127759608237879923802581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14837012810983839898403441 11127759608237879923802581)
                ·
                  refine ⟨260806865818075310714123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11127759608237879923802581 260806865818075310714123)
                  ·
                    rfl

theorem cell21_1142819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_1142819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142819 prefixEnd_1142819 := by exact prefixLift 1142819
  have htrace : WordTrace (prefixWord ++ tailWord_1142819) baseStart_1142819 baseEnd_1142819 := by
    simpa [prefixWord, tailWord_1142819, baseEnd_1142819] using wordTrace_append hprefix tailTrace_1142819
  have hstable : (prefixWord ++ tailWord_1142819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142819).length < 2 ^ (prefixWord ++ tailWord_1142819).sum := by decide
  have hdescent : baseEnd_1142819 < baseStart_1142819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142943 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 4]
def baseStart_1142943 : Nat := 118140960795 + 1142943 * 2 ^ 59
def prefixEnd_1142943 : Nat := 4983230072969 + 3 ^ 40 * 1142943 * 2
def baseEnd_1142943 : Nat := 260835164307478650647203

theorem tailTrace_1142943 : CollatzResearch.WordTrace tailWord_1142943 prefixEnd_1142943 260835164307478650647203 := by
  unfold tailWord_1142943
  simp only [CollatzResearch.WordTrace]
  refine ⟨41686555898320184968913483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27791037265546789979275655 41686555898320184968913483)
  ·
    refine ⟨62529833847480277453370225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41686555898320184968913483 62529833847480277453370225)
    ·
      refine ⟨46897375385610208090027669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62529833847480277453370225 46897375385610208090027669)
      ·
        refine ⟨2198314471200478504220047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46897375385610208090027669 2198314471200478504220047)
        ·
          refine ⟨3297471706800717756330071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2198314471200478504220047 3297471706800717756330071)
          ·
            refine ⟨4946207560201076634495107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3297471706800717756330071 4946207560201076634495107)
            ·
              refine ⟨7419311340301614951742661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4946207560201076634495107 7419311340301614951742661)
              ·
                refine ⟨1391120876306552803451749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7419311340301614951742661 1391120876306552803451749)
                ·
                  refine ⟨260835164307478650647203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391120876306552803451749 260835164307478650647203)
                  ·
                    rfl

theorem cell21_1142943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 4].length) (baseStart_1142943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142943 prefixEnd_1142943 := by exact prefixLift 1142943
  have htrace : WordTrace (prefixWord ++ tailWord_1142943) baseStart_1142943 baseEnd_1142943 := by
    simpa [prefixWord, tailWord_1142943, baseEnd_1142943] using wordTrace_append hprefix tailTrace_1142943
  have hstable : (prefixWord ++ tailWord_1142943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142943).length < 2 ^ (prefixWord ++ tailWord_1142943).sum := by decide
  have hdescent : baseEnd_1142943 < baseStart_1142943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142946 : List Nat := [3, 3, 1, 3, 1, 2, 1, 4, 3]
def baseStart_1142946 : Nat := 118140960795 + 1142946 * 2 ^ 59
def prefixEnd_1142946 : Nat := 4983230072969 + 3 ^ 40 * 1142946 * 2
def baseEnd_1142946 : Nat := 260835848948351312097197

theorem tailTrace_1142946 : CollatzResearch.WordTrace tailWord_1142946 prefixEnd_1142946 260835848948351312097197 := by
  unfold tailWord_1142946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10421666329327329120318173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27791110211539544320848461 10421666329327329120318173)
  ·
    refine ⟨3908124873497748420119315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10421666329327329120318173 3908124873497748420119315)
    ·
      refine ⟨5862187310246622630178973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3908124873497748420119315 5862187310246622630178973)
      ·
        refine ⟨2198320241342483486317115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5862187310246622630178973 2198320241342483486317115)
        ·
          refine ⟨3297480362013725229475673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2198320241342483486317115 3297480362013725229475673)
          ·
            refine ⟨2473110271510293922106755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3297480362013725229475673 2473110271510293922106755)
            ·
              refine ⟨3709665407265440883160133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473110271510293922106755 3709665407265440883160133)
              ·
                refine ⟨695562263862270165592525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3709665407265440883160133 695562263862270165592525)
                ·
                  refine ⟨260835848948351312097197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695562263862270165592525 260835848948351312097197)
                  ·
                    rfl

theorem cell21_1142946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_1142946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142946 prefixEnd_1142946 := by exact prefixLift 1142946
  have htrace : WordTrace (prefixWord ++ tailWord_1142946) baseStart_1142946 baseEnd_1142946 := by
    simpa [prefixWord, tailWord_1142946, baseEnd_1142946] using wordTrace_append hprefix tailTrace_1142946
  have hstable : (prefixWord ++ tailWord_1142946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142946).length < 2 ^ (prefixWord ++ tailWord_1142946).sum := by decide
  have hdescent : baseEnd_1142946 < baseStart_1142946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142971 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 5]
def baseStart_1142971 : Nat := 118140960795 + 1142971 * 2 ^ 59
def prefixEnd_1142971 : Nat := 4983230072969 + 3 ^ 40 * 1142971 * 2
def baseEnd_1142971 : Nat := 260841554288956824180479

theorem tailTrace_1142971 : CollatzResearch.WordTrace tailWord_1142971 prefixEnd_1142971 260841554288956824180479 := by
  unfold tailWord_1142971
  simp only [CollatzResearch.WordTrace]
  refine ⟨41687577142218745750932767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27791718094812497167288511 41687577142218745750932767)
  ·
    refine ⟨62531365713328118626399151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41687577142218745750932767 62531365713328118626399151)
    ·
      refine ⟨93797048569992177939598727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62531365713328118626399151 93797048569992177939598727)
      ·
        refine ⟨140695572854988266909398091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93797048569992177939598727 140695572854988266909398091)
        ·
          refine ⟨211043359282482400364097137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140695572854988266909398091 211043359282482400364097137)
          ·
            refine ⟨158282519461861800273072853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211043359282482400364097137 158282519461861800273072853)
            ·
              refine ⟨3709746549887385943900145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 158282519461861800273072853 3709746549887385943900145)
              ·
                refine ⟨2782309912415539457925109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3709746549887385943900145 2782309912415539457925109)
                ·
                  refine ⟨260841554288956824180479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2782309912415539457925109 260841554288956824180479)
                  ·
                    rfl

theorem cell21_1142971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_1142971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1142971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1142971 prefixEnd_1142971 := by exact prefixLift 1142971
  have htrace : WordTrace (prefixWord ++ tailWord_1142971) baseStart_1142971 baseEnd_1142971 := by
    simpa [prefixWord, tailWord_1142971, baseEnd_1142971] using wordTrace_append hprefix tailTrace_1142971
  have hstable : (prefixWord ++ tailWord_1142971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142971).length < 2 ^ (prefixWord ++ tailWord_1142971).sum := by decide
  have hdescent : baseEnd_1142971 < baseStart_1142971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143005 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1143005 : Nat := 118140960795 + 1143005 * 2 ^ 59
def prefixEnd_1143005 : Nat := 4983230072969 + 3 ^ 40 * 1143005 * 2
def baseEnd_1143005 : Nat := 260849313552180320613743

theorem tailTrace_1143005 : CollatzResearch.WordTrace tailWord_1143005 prefixEnd_1143005 260849313552180320613743 := by
  unfold tailWord_1143005
  simp only [CollatzResearch.WordTrace]
  refine ⟨41688817224095569557670469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27792544816063713038446979 41688817224095569557670469)
  ·
    refine ⟨7816653229517919292063213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41688817224095569557670469 7816653229517919292063213)
    ·
      refine ⟨2931244961069219734523705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7816653229517919292063213 2931244961069219734523705)
      ·
        refine ⟨2198433720801914800892779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2931244961069219734523705 2198433720801914800892779)
        ·
          refine ⟨3297650581202872201339169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2198433720801914800892779 3297650581202872201339169)
          ·
            refine ⟨2473237935902154151004377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3297650581202872201339169 2473237935902154151004377)
            ·
              refine ⟨1854928451926615613253283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2473237935902154151004377 1854928451926615613253283)
              ·
                refine ⟨2782392677889923419879925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854928451926615613253283 2782392677889923419879925)
                ·
                  refine ⟨260849313552180320613743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2782392677889923419879925 260849313552180320613743)
                  ·
                    rfl

theorem cell21_1143005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1143005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143005 prefixEnd_1143005 := by exact prefixLift 1143005
  have htrace : WordTrace (prefixWord ++ tailWord_1143005) baseStart_1143005 baseEnd_1143005 := by
    simpa [prefixWord, tailWord_1143005, baseEnd_1143005] using wordTrace_append hprefix tailTrace_1143005
  have hstable : (prefixWord ++ tailWord_1143005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143005).length < 2 ^ (prefixWord ++ tailWord_1143005).sum := by decide
  have hdescent : baseEnd_1143005 < baseStart_1143005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143019 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 4]
def baseStart_1143019 : Nat := 118140960795 + 1143019 * 2 ^ 59
def prefixEnd_1143019 : Nat := 4983230072969 + 3 ^ 40 * 1143019 * 2
def baseEnd_1143019 : Nat := 260852508542919407380381

theorem tailTrace_1143019 : CollatzResearch.WordTrace tailWord_1143019 prefixEnd_1143019 260852508542919407380381 := by
  unfold tailWord_1143019
  simp only [CollatzResearch.WordTrace]
  refine ⟨41689327846044849948680111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27792885230696566632453407 41689327846044849948680111)
  ·
    refine ⟨62533991769067274923020167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41689327846044849948680111 62533991769067274923020167)
    ·
      refine ⟨93800987653600912384530251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62533991769067274923020167 93800987653600912384530251)
      ·
        refine ⟨140701481480401368576795377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93800987653600912384530251 140701481480401368576795377)
        ·
          refine ⟨105526111110301026432596533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140701481480401368576795377 105526111110301026432596533)
          ·
            refine ⟨9893072916590721228055925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105526111110301026432596533 9893072916590721228055925)
            ·
              refine ⟨927475585930380115130243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9893072916590721228055925 927475585930380115130243)
              ·
                refine ⟨1391213378895570172695365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927475585930380115130243 1391213378895570172695365)
                ·
                  refine ⟨260852508542919407380381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391213378895570172695365 260852508542919407380381)
                  ·
                    rfl

theorem cell21_1143019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 4].length) (baseStart_1143019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143019 prefixEnd_1143019 := by exact prefixLift 1143019
  have htrace : WordTrace (prefixWord ++ tailWord_1143019) baseStart_1143019 baseEnd_1143019 := by
    simpa [prefixWord, tailWord_1143019, baseEnd_1143019] using wordTrace_append hprefix tailTrace_1143019
  have hstable : (prefixWord ++ tailWord_1143019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143019).length < 2 ^ (prefixWord ++ tailWord_1143019).sum := by decide
  have hdescent : baseEnd_1143019 < baseStart_1143019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143070 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1143070 : Nat := 118140960795 + 1143070 * 2 ^ 59
def prefixEnd_1143070 : Nat := 4983230072969 + 3 ^ 40 * 1143070 * 2
def baseEnd_1143070 : Nat := 260864147437754652030277

theorem tailTrace_1143070 : CollatzResearch.WordTrace tailWord_1143070 prefixEnd_1143070 260864147437754652030277 := by
  unfold tailWord_1143070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211398496107510707348333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27794125312573390439191109 5211398496107510707348333)
  ·
    refine ⟨1954274436040316515255625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5211398496107510707348333 1954274436040316515255625)
    ·
      refine ⟨1465705827030237386441719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1954274436040316515255625 1465705827030237386441719)
      ·
        refine ⟨2198558740545356079662579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1465705827030237386441719 2198558740545356079662579)
        ·
          refine ⟨3297838110818034119493869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2198558740545356079662579 3297838110818034119493869)
          ·
            refine ⟨1236689291556762794810201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3297838110818034119493869 1236689291556762794810201)
            ·
              refine ⟨927516968667572096107651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236689291556762794810201 927516968667572096107651)
              ·
                refine ⟨1391275453001358144161477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927516968667572096107651 1391275453001358144161477)
                ·
                  refine ⟨260864147437754652030277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391275453001358144161477 260864147437754652030277)
                  ·
                    rfl

theorem cell21_1143070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1143070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143070 prefixEnd_1143070 := by exact prefixLift 1143070
  have htrace : WordTrace (prefixWord ++ tailWord_1143070) baseStart_1143070 baseEnd_1143070 := by
    simpa [prefixWord, tailWord_1143070, baseEnd_1143070] using wordTrace_append hprefix tailTrace_1143070
  have hstable : (prefixWord ++ tailWord_1143070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143070).length < 2 ^ (prefixWord ++ tailWord_1143070).sum := by decide
  have hdescent : baseEnd_1143070 < baseStart_1143070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143137 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 10]
def baseStart_1143137 : Nat := 118140960795 + 1143137 * 2 ^ 59
def prefixEnd_1143137 : Nat := 4983230072969 + 3 ^ 40 * 1143137 * 2
def baseEnd_1143137 : Nat := 260879437750577424413473

theorem tailTrace_1143137 : CollatzResearch.WordTrace tailWord_1143137 prefixEnd_1143137 260879437750577424413473 := by
  unfold tailWord_1143137
  simp only [CollatzResearch.WordTrace]
  refine ⟨41693631659617356101475665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27795754439744904067650443 41693631659617356101475665)
  ·
    refine ⟨31270223744713017076106749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41693631659617356101475665 31270223744713017076106749)
    ·
      refine ⟨11726333904267381403540031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31270223744713017076106749 11726333904267381403540031)
      ·
        refine ⟨17589500856401072105310047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11726333904267381403540031 17589500856401072105310047)
        ·
          refine ⟨26384251284601608157965071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17589500856401072105310047 26384251284601608157965071)
          ·
            refine ⟨39576376926902412236947607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26384251284601608157965071 39576376926902412236947607)
            ·
              refine ⟨59364565390353618355421411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39576376926902412236947607 59364565390353618355421411)
              ·
                refine ⟨89046848085530427533132117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59364565390353618355421411 89046848085530427533132117)
                ·
                  refine ⟨260879437750577424413473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89046848085530427533132117 260879437750577424413473)
                  ·
                    rfl

theorem cell21_1143137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_1143137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143137 prefixEnd_1143137 := by exact prefixLift 1143137
  have htrace : WordTrace (prefixWord ++ tailWord_1143137) baseStart_1143137 baseEnd_1143137 := by
    simpa [prefixWord, tailWord_1143137, baseEnd_1143137] using wordTrace_append hprefix tailTrace_1143137
  have hstable : (prefixWord ++ tailWord_1143137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143137).length < 2 ^ (prefixWord ++ tailWord_1143137).sum := by decide
  have hdescent : baseEnd_1143137 < baseStart_1143137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143157 : List Nat := [1, 3, 4, 1, 2, 1, 1, 5, 3]
def baseStart_1143157 : Nat := 118140960795 + 1143157 * 2 ^ 59
def prefixEnd_1143157 : Nat := 4983230072969 + 3 ^ 40 * 1143157 * 2
def baseEnd_1143157 : Nat := 260884002023061834080099

theorem tailTrace_1143157 : CollatzResearch.WordTrace tailWord_1143157 prefixEnd_1143157 260884002023061834080099 := by
  unfold tailWord_1143157
  simp only [CollatzResearch.WordTrace]
  refine ⟨41694361119544899517203725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27796240746363266344802483 41694361119544899517203725)
  ·
    refine ⟨15635385419829337318951397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41694361119544899517203725 15635385419829337318951397)
    ·
      refine ⟨2931634766218000747303387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15635385419829337318951397 2931634766218000747303387)
      ·
        refine ⟨4397452149327001120955081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931634766218000747303387 4397452149327001120955081)
        ·
          refine ⟨3298089111995250840716311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4397452149327001120955081 3298089111995250840716311)
          ·
            refine ⟨4947133667992876261074467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3298089111995250840716311 4947133667992876261074467)
            ·
              refine ⟨7420700501989314391611701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4947133667992876261074467 7420700501989314391611701)
              ·
                refine ⟨695690672061498224213597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7420700501989314391611701 695690672061498224213597)
                ·
                  refine ⟨260884002023061834080099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695690672061498224213597 260884002023061834080099)
                  ·
                    rfl

theorem cell21_1143157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_1143157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143157 prefixEnd_1143157 := by exact prefixLift 1143157
  have htrace : WordTrace (prefixWord ++ tailWord_1143157) baseStart_1143157 baseEnd_1143157 := by
    simpa [prefixWord, tailWord_1143157, baseEnd_1143157] using wordTrace_append hprefix tailTrace_1143157
  have hstable : (prefixWord ++ tailWord_1143157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143157).length < 2 ^ (prefixWord ++ tailWord_1143157).sum := by decide
  have hdescent : baseEnd_1143157 < baseStart_1143157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143199 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 5]
def baseStart_1143199 : Nat := 118140960795 + 1143199 * 2 ^ 59
def prefixEnd_1143199 : Nat := 4983230072969 + 3 ^ 40 * 1143199 * 2
def baseEnd_1143199 : Nat := 260893586995279094380013

theorem tailTrace_1143199 : CollatzResearch.WordTrace tailWord_1143199 prefixEnd_1143199 260893586995279094380013 := by
  unfold tailWord_1143199
  simp only [CollatzResearch.WordTrace]
  refine ⟨41695892985392740690232651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27797261990261827126821767 41695892985392740690232651)
  ·
    refine ⟨62543839478089111035348977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41695892985392740690232651 62543839478089111035348977)
    ·
      refine ⟨46907879608566833276511733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62543839478089111035348977 46907879608566833276511733)
      ·
        refine ⟨4397613713303140619672975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46907879608566833276511733 4397613713303140619672975)
        ·
          refine ⟨6596420569954710929509463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4397613713303140619672975 6596420569954710929509463)
          ·
            refine ⟨9894630854932066394264195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6596420569954710929509463 9894630854932066394264195)
            ·
              refine ⟨14841946282398099591396293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9894630854932066394264195 14841946282398099591396293)
              ·
                refine ⟨2782864927949643673386805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14841946282398099591396293 2782864927949643673386805)
                ·
                  refine ⟨260893586995279094380013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2782864927949643673386805 260893586995279094380013)
                  ·
                    rfl

theorem cell21_1143199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_1143199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143199 prefixEnd_1143199 := by exact prefixLift 1143199
  have htrace : WordTrace (prefixWord ++ tailWord_1143199) baseStart_1143199 baseEnd_1143199 := by
    simpa [prefixWord, tailWord_1143199, baseEnd_1143199] using wordTrace_append hprefix tailTrace_1143199
  have hstable : (prefixWord ++ tailWord_1143199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143199).length < 2 ^ (prefixWord ++ tailWord_1143199).sum := by decide
  have hdescent : baseEnd_1143199 < baseStart_1143199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143230 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_1143230 : Nat := 118140960795 + 1143230 * 2 ^ 59
def prefixEnd_1143230 : Nat := 4983230072969 + 3 ^ 40 * 1143230 * 2
def baseEnd_1143230 : Nat := 260900661617629929363283

theorem tailTrace_1143230 : CollatzResearch.WordTrace tailWord_1143230 prefixEnd_1143230 260900661617629929363283 := by
  unfold tailWord_1143230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212127956035054123076393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27798015765520288656407429 5212127956035054123076393)
  ·
    refine ⟨3909095967026290592307295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5212127956035054123076393 3909095967026290592307295)
    ·
      refine ⟨5863643950539435888460943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3909095967026290592307295 5863643950539435888460943)
      ·
        refine ⟨8795465925809153832691415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5863643950539435888460943 8795465925809153832691415)
        ·
          refine ⟨13193198888713730749037123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8795465925809153832691415 13193198888713730749037123)
          ·
            refine ⟨19789798333070596123555685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13193198888713730749037123 19789798333070596123555685)
            ·
              refine ⟨3710587187450736773166691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19789798333070596123555685 3710587187450736773166691)
              ·
                refine ⟨5565880781176105159750037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710587187450736773166691 5565880781176105159750037)
                ·
                  refine ⟨260900661617629929363283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5565880781176105159750037 260900661617629929363283)
                  ·
                    rfl

theorem cell21_1143230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_1143230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143230 prefixEnd_1143230 := by exact prefixLift 1143230
  have htrace : WordTrace (prefixWord ++ tailWord_1143230) baseStart_1143230 baseEnd_1143230 := by
    simpa [prefixWord, tailWord_1143230, baseEnd_1143230] using wordTrace_append hprefix tailTrace_1143230
  have hstable : (prefixWord ++ tailWord_1143230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143230).length < 2 ^ (prefixWord ++ tailWord_1143230).sum := by decide
  have hdescent : baseEnd_1143230 < baseStart_1143230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143289 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 6]
def baseStart_1143289 : Nat := 118140960795 + 1143289 * 2 ^ 59
def prefixEnd_1143289 : Nat := 4983230072969 + 3 ^ 40 * 1143289 * 2
def baseEnd_1143289 : Nat := 260914126221458937879829

theorem tailTrace_1143289 : CollatzResearch.WordTrace tailWord_1143289 prefixEnd_1143289 260914126221458937879829 := by
  unfold tailWord_1143289
  simp only [CollatzResearch.WordTrace]
  refine ⟨41699175555066686061008921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27799450370044457374005947 41699175555066686061008921)
  ·
    refine ⟨31274381666300014545756691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41699175555066686061008921 31274381666300014545756691)
    ·
      refine ⟨46911572499450021818635037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31274381666300014545756691 46911572499450021818635037)
      ·
        refine ⟨17591839687293758181988139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46911572499450021818635037 17591839687293758181988139)
        ·
          refine ⟨26387759530940637272982209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17591839687293758181988139 26387759530940637272982209)
          ·
            refine ⟨19790819648205477954736657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26387759530940637272982209 19790819648205477954736657)
            ·
              refine ⟨14843114736154108466052493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19790819648205477954736657 14843114736154108466052493)
              ·
                refine ⟨5566168026057790674769685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14843114736154108466052493 5566168026057790674769685)
                ·
                  refine ⟨260914126221458937879829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5566168026057790674769685 260914126221458937879829)
                  ·
                    rfl

theorem cell21_1143289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_1143289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143289 prefixEnd_1143289 := by exact prefixLift 1143289
  have htrace : WordTrace (prefixWord ++ tailWord_1143289) baseStart_1143289 baseEnd_1143289 := by
    simpa [prefixWord, tailWord_1143289, baseEnd_1143289] using wordTrace_append hprefix tailTrace_1143289
  have hstable : (prefixWord ++ tailWord_1143289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143289).length < 2 ^ (prefixWord ++ tailWord_1143289).sum := by decide
  have hdescent : baseEnd_1143289 < baseStart_1143289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143306 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_1143306 : Nat := 118140960795 + 1143306 * 2 ^ 59
def prefixEnd_1143306 : Nat := 4983230072969 + 3 ^ 40 * 1143306 * 2
def baseEnd_1143306 : Nat := 260918005853070686096461

theorem tailTrace_1143306 : CollatzResearch.WordTrace tailWord_1143306 prefixEnd_1143306 260918005853070686096461 := by
  unfold tailWord_1143306
  simp only [CollatzResearch.WordTrace]
  refine ⟨10424948899001274491094443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27799863730670065309585181 10424948899001274491094443)
  ·
    refine ⟨15637423348501911736641665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10424948899001274491094443 15637423348501911736641665)
    ·
      refine ⟨11728067511376433802481249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15637423348501911736641665 11728067511376433802481249)
      ·
        refine ⟨8796050633532325351860937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11728067511376433802481249 8796050633532325351860937)
        ·
          refine ⟨6597037975149244013895703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8796050633532325351860937 6597037975149244013895703)
          ·
            refine ⟨9895556962723866020843555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6597037975149244013895703 9895556962723866020843555)
            ·
              refine ⟨14843335444085799031265333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9895556962723866020843555 14843335444085799031265333)
              ·
                refine ⟨1391562697883043659181125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14843335444085799031265333 1391562697883043659181125)
                ·
                  refine ⟨260918005853070686096461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391562697883043659181125 260918005853070686096461)
                  ·
                    rfl

theorem cell21_1143306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_1143306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143306 prefixEnd_1143306 := by exact prefixLift 1143306
  have htrace : WordTrace (prefixWord ++ tailWord_1143306) baseStart_1143306 baseEnd_1143306 := by
    simpa [prefixWord, tailWord_1143306, baseEnd_1143306] using wordTrace_append hprefix tailTrace_1143306
  have hstable : (prefixWord ++ tailWord_1143306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143306).length < 2 ^ (prefixWord ++ tailWord_1143306).sum := by decide
  have hdescent : baseEnd_1143306 < baseStart_1143306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143309 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1143309 : Nat := 118140960795 + 1143309 * 2 ^ 59
def prefixEnd_1143309 : Nat := 4983230072969 + 3 ^ 40 * 1143309 * 2
def baseEnd_1143309 : Nat := 260918690493943347546455

theorem tailTrace_1143309 : CollatzResearch.WordTrace tailWord_1143309 prefixEnd_1143309 260918690493943347546455 := by
  unfold tailWord_1143309
  simp only [CollatzResearch.WordTrace]
  refine ⟨41699905014994229476736981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27799936676662819651157987 41699905014994229476736981)
  ·
    refine ⟨977341523788927253361023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 41699905014994229476736981 977341523788927253361023)
    ·
      refine ⟨1466012285683390880041535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977341523788927253361023 1466012285683390880041535)
      ·
        refine ⟨2199018428525086320062303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466012285683390880041535 2199018428525086320062303)
        ·
          refine ⟨3298527642787629480093455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199018428525086320062303 3298527642787629480093455)
          ·
            refine ⟨4947791464181444220140183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3298527642787629480093455 4947791464181444220140183)
            ·
              refine ⟨7421687196272166330210275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4947791464181444220140183 7421687196272166330210275)
              ·
                refine ⟨11132530794408249495315413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7421687196272166330210275 11132530794408249495315413)
                ·
                  refine ⟨260918690493943347546455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11132530794408249495315413 260918690493943347546455)
                  ·
                    rfl

theorem cell21_1143309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1143309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143309 prefixEnd_1143309 := by exact prefixLift 1143309
  have htrace : WordTrace (prefixWord ++ tailWord_1143309) baseStart_1143309 baseEnd_1143309 := by
    simpa [prefixWord, tailWord_1143309, baseEnd_1143309] using wordTrace_append hprefix tailTrace_1143309
  have hstable : (prefixWord ++ tailWord_1143309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143309).length < 2 ^ (prefixWord ++ tailWord_1143309).sum := by decide
  have hdescent : baseEnd_1143309 < baseStart_1143309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143351 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 5]
def baseStart_1143351 : Nat := 118140960795 + 1143351 * 2 ^ 59
def prefixEnd_1143351 : Nat := 4983230072969 + 3 ^ 40 * 1143351 * 2
def baseEnd_1143351 : Nat := 260928275466160607846369

theorem tailTrace_1143351 : CollatzResearch.WordTrace tailWord_1143351 prefixEnd_1143351 260928275466160607846369 := by
  unfold tailWord_1143351
  simp only [CollatzResearch.WordTrace]
  refine ⟨41701436880842070649765907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27800957920561380433177271 41701436880842070649765907)
  ·
    refine ⟨62552155321263105974648861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41701436880842070649765907 62552155321263105974648861)
    ·
      refine ⟨23457058245473664740493323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62552155321263105974648861 23457058245473664740493323)
      ·
        refine ⟨35185587368210497110739985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23457058245473664740493323 35185587368210497110739985)
        ·
          refine ⟨26389190526157872833054989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35185587368210497110739985 26389190526157872833054989)
          ·
            refine ⟨9895946447309202312395621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26389190526157872833054989 9895946447309202312395621)
            ·
              refine ⟨1855489958870475433574179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9895946447309202312395621 1855489958870475433574179)
              ·
                refine ⟨2783234938305713150361269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855489958870475433574179 2783234938305713150361269)
                ·
                  refine ⟨260928275466160607846369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2783234938305713150361269 260928275466160607846369)
                  ·
                    rfl

theorem cell21_1143351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 5].length) (baseStart_1143351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143351 prefixEnd_1143351 := by exact prefixLift 1143351
  have htrace : WordTrace (prefixWord ++ tailWord_1143351) baseStart_1143351 baseEnd_1143351 := by
    simpa [prefixWord, tailWord_1143351, baseEnd_1143351] using wordTrace_append hprefix tailTrace_1143351
  have hstable : (prefixWord ++ tailWord_1143351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143351).length < 2 ^ (prefixWord ++ tailWord_1143351).sum := by decide
  have hdescent : baseEnd_1143351 < baseStart_1143351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143455 : List Nat := [1, 1, 2, 17]
def baseStart_1143455 : Nat := 118140960795 + 1143455 * 2 ^ 59
def prefixEnd_1143455 : Nat := 4983230072969 + 3 ^ 40 * 1143455 * 2
def baseEnd_1143455 : Nat := 1073876583057940486061

theorem tailTrace_1143455 : CollatzResearch.WordTrace tailWord_1143455 prefixEnd_1143455 1073876583057940486061 := by
  unfold tailWord_1143455
  simp only [CollatzResearch.WordTrace]
  refine ⟨41705230072465296411551819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27803486714976864274367879 41705230072465296411551819)
  ·
    refine ⟨62557845108697944617327729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41705230072465296411551819 62557845108697944617327729)
    ·
      refine ⟨46918383831523458462995797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62557845108697944617327729 46918383831523458462995797)
      ·
        refine ⟨1073876583057940486061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 46918383831523458462995797 1073876583057940486061)
        ·
          rfl

theorem cell21_1143455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 17].length) (baseStart_1143455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143455 prefixEnd_1143455 := by exact prefixLift 1143455
  have htrace : WordTrace (prefixWord ++ tailWord_1143455) baseStart_1143455 baseEnd_1143455 := by
    simpa [prefixWord, tailWord_1143455, baseEnd_1143455] using wordTrace_append hprefix tailTrace_1143455
  have hstable : (prefixWord ++ tailWord_1143455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143455).length < 2 ^ (prefixWord ++ tailWord_1143455).sum := by decide
  have hdescent : baseEnd_1143455 < baseStart_1143455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143509 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 4]
def baseStart_1143509 : Nat := 118140960795 + 1143509 * 2 ^ 59
def prefixEnd_1143509 : Nat := 4983230072969 + 3 ^ 40 * 1143509 * 2
def baseEnd_1143509 : Nat := 260964333218787444212713

theorem tailTrace_1143509 : CollatzResearch.WordTrace tailWord_1143509 prefixEnd_1143509 260964333218787444212713 := by
  unfold tailWord_1143509
  simp only [CollatzResearch.WordTrace]
  refine ⟨41707199614269663634017581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27804799742846442422678387 41707199614269663634017581)
  ·
    refine ⟨15640199855351123862756593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41707199614269663634017581 15640199855351123862756593)
    ·
      refine ⟨11730149891513342897067445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15640199855351123862756593 11730149891513342897067445)
      ·
        refine ⟨1099701552329375896600073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11730149891513342897067445 1099701552329375896600073)
        ·
          refine ⟨824776164247031922450055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1099701552329375896600073 824776164247031922450055)
          ·
            refine ⟨1237164246370547883675083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824776164247031922450055 1237164246370547883675083)
            ·
              refine ⟨1855746369555821825512625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237164246370547883675083 1855746369555821825512625)
              ·
                refine ⟨1391809777166866369134469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855746369555821825512625 1391809777166866369134469)
                ·
                  refine ⟨260964333218787444212713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391809777166866369134469 260964333218787444212713)
                  ·
                    rfl

theorem cell21_1143509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_1143509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143509 prefixEnd_1143509 := by exact prefixLift 1143509
  have htrace : WordTrace (prefixWord ++ tailWord_1143509) baseStart_1143509 baseEnd_1143509 := by
    simpa [prefixWord, tailWord_1143509, baseEnd_1143509] using wordTrace_append hprefix tailTrace_1143509
  have hstable : (prefixWord ++ tailWord_1143509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143509).length < 2 ^ (prefixWord ++ tailWord_1143509).sum := by decide
  have hdescent : baseEnd_1143509 < baseStart_1143509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143531 : List Nat := [1, 1, 1, 1, 2, 4, 1, 10]
def baseStart_1143531 : Nat := 118140960795 + 1143531 * 2 ^ 59
def prefixEnd_1143531 : Nat := 4983230072969 + 3 ^ 40 * 1143531 * 2
def baseEnd_1143531 : Nat := 86989784639506764948667

theorem tailTrace_1143531 : CollatzResearch.WordTrace tailWord_1143531 prefixEnd_1143531 86989784639506764948667 := by
  unfold tailWord_1143531
  simp only [CollatzResearch.WordTrace]
  refine ⟨41708002020189961391318447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27805334680126640927545631 41708002020189961391318447)
  ·
    refine ⟨62562003030284942086977671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41708002020189961391318447 62562003030284942086977671)
    ·
      refine ⟨93843004545427413130466507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62562003030284942086977671 93843004545427413130466507)
      ·
        refine ⟨140764506818141119695699761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93843004545427413130466507 140764506818141119695699761)
        ·
          refine ⟨105573380113605839771774821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140764506818141119695699761 105573380113605839771774821)
          ·
            refine ⟨19795008771301094957207779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105573380113605839771774821 19795008771301094957207779)
            ·
              refine ⟨29692513156951642435811669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19795008771301094957207779 29692513156951642435811669)
              ·
                refine ⟨86989784639506764948667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29692513156951642435811669 86989784639506764948667)
                ·
                  rfl

theorem cell21_1143531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 10].length) (baseStart_1143531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143531 prefixEnd_1143531 := by exact prefixLift 1143531
  have htrace : WordTrace (prefixWord ++ tailWord_1143531) baseStart_1143531 baseEnd_1143531 := by
    simpa [prefixWord, tailWord_1143531, baseEnd_1143531] using wordTrace_append hprefix tailTrace_1143531
  have hstable : (prefixWord ++ tailWord_1143531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143531).length < 2 ^ (prefixWord ++ tailWord_1143531).sum := by decide
  have hdescent : baseEnd_1143531 < baseStart_1143531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143540 : List Nat := [2, 6, 1, 1, 2, 2, 2, 5]
def baseStart_1143540 : Nat := 118140960795 + 1143540 * 2 ^ 59
def prefixEnd_1143540 : Nat := 4983230072969 + 3 ^ 40 * 1143540 * 2
def baseEnd_1143540 : Nat := 86990469280379426398661

theorem tailTrace_1143540 : CollatzResearch.WordTrace tailWord_1143540 prefixEnd_1143540 86990469280379426398661 := by
  unfold tailWord_1143540
  simp only [CollatzResearch.WordTrace]
  refine ⟨20854165138578677964198037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27805553518104903952264049 20854165138578677964198037)
  ·
    refine ⟨977538990870875529571783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20854165138578677964198037 977538990870875529571783)
    ·
      refine ⟨1466308486306313294357675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977538990870875529571783 1466308486306313294357675)
      ·
        refine ⟨2199462729459469941536513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466308486306313294357675 2199462729459469941536513)
        ·
          refine ⟨1649597047094602456152385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2199462729459469941536513 1649597047094602456152385)
          ·
            refine ⟨1237197785320951842114289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1649597047094602456152385 1237197785320951842114289)
            ·
              refine ⟨927898338990713881585717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1237197785320951842114289 927898338990713881585717)
              ·
                refine ⟨86990469280379426398661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 927898338990713881585717 86990469280379426398661)
                ·
                  rfl

theorem cell21_1143540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_1143540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143540 prefixEnd_1143540 := by exact prefixLift 1143540
  have htrace : WordTrace (prefixWord ++ tailWord_1143540) baseStart_1143540 baseEnd_1143540 := by
    simpa [prefixWord, tailWord_1143540, baseEnd_1143540] using wordTrace_append hprefix tailTrace_1143540
  have hstable : (prefixWord ++ tailWord_1143540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143540).length < 2 ^ (prefixWord ++ tailWord_1143540).sum := by decide
  have hdescent : baseEnd_1143540 < baseStart_1143540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143548 : List Nat := [2, 2, 2, 1, 3, 3, 1, 7]
def baseStart_1143548 : Nat := 118140960795 + 1143548 * 2 ^ 59
def prefixEnd_1143548 : Nat := 4983230072969 + 3 ^ 40 * 1143548 * 2
def baseEnd_1143548 : Nat := 86991077850044014354211

theorem tailTrace_1143548 : CollatzResearch.WordTrace tailWord_1143548 prefixEnd_1143548 86991077850044014354211 := by
  unfold tailWord_1143548
  simp only [CollatzResearch.WordTrace]
  refine ⟨20854311030564186647343649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27805748040752248863124865 20854311030564186647343649)
  ·
    refine ⟨15640733272923139985507737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20854311030564186647343649 15640733272923139985507737)
    ·
      refine ⟨11730549954692354989130803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15640733272923139985507737 11730549954692354989130803)
      ·
        refine ⟨17595824932038532483696205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11730549954692354989130803 17595824932038532483696205)
        ·
          refine ⟨6598434349514449681386077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17595824932038532483696205 6598434349514449681386077)
          ·
            refine ⟨2474412881067918630519779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6598434349514449681386077 2474412881067918630519779)
            ·
              refine ⟨3711619321601877945779669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474412881067918630519779 3711619321601877945779669)
              ·
                refine ⟨86991077850044014354211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3711619321601877945779669 86991077850044014354211)
                ·
                  rfl

theorem cell21_1143548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_1143548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143548 prefixEnd_1143548 := by exact prefixLift 1143548
  have htrace : WordTrace (prefixWord ++ tailWord_1143548) baseStart_1143548 baseEnd_1143548 := by
    simpa [prefixWord, tailWord_1143548, baseEnd_1143548] using wordTrace_append hprefix tailTrace_1143548
  have hstable : (prefixWord ++ tailWord_1143548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143548).length < 2 ^ (prefixWord ++ tailWord_1143548).sum := by decide
  have hdescent : baseEnd_1143548 < baseStart_1143548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143554 : List Nat := [3, 4, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1143554 : Nat := 118140960795 + 1143554 * 2 ^ 59
def prefixEnd_1143554 : Nat := 4983230072969 + 3 ^ 40 * 1143554 * 2
def baseEnd_1143554 : Nat := 260974602831877365962621

theorem tailTrace_1143554 : CollatzResearch.WordTrace tailWord_1143554 prefixEnd_1143554 260974602831877365962621 := by
  unfold tailWord_1143554
  simp only [CollatzResearch.WordTrace]
  refine ⟨10427210224776659079851429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27805893932737757546270477 10427210224776659079851429)
  ·
    refine ⟨1955101917145623577472143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10427210224776659079851429 1955101917145623577472143)
    ·
      refine ⟨2932652875718435366208215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1955101917145623577472143 2932652875718435366208215)
      ·
        refine ⟨4398979313577653049312323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2932652875718435366208215 4398979313577653049312323)
        ·
          refine ⟨6598468970366479573968485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4398979313577653049312323 6598468970366479573968485)
          ·
            refine ⟨1237212931943714920119091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6598468970366479573968485 1237212931943714920119091)
            ·
              refine ⟨1855819397915572380178637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237212931943714920119091 1855819397915572380178637)
              ·
                refine ⟨695932274218339642566989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1855819397915572380178637 695932274218339642566989)
                ·
                  refine ⟨260974602831877365962621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695932274218339642566989 260974602831877365962621)
                  ·
                    rfl

theorem cell21_1143554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1143554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143554 prefixEnd_1143554 := by exact prefixLift 1143554
  have htrace : WordTrace (prefixWord ++ tailWord_1143554) baseStart_1143554 baseEnd_1143554 := by
    simpa [prefixWord, tailWord_1143554, baseEnd_1143554] using wordTrace_append hprefix tailTrace_1143554
  have hstable : (prefixWord ++ tailWord_1143554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143554).length < 2 ^ (prefixWord ++ tailWord_1143554).sum := by decide
  have hdescent : baseEnd_1143554 < baseStart_1143554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143593 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 4]
def baseStart_1143593 : Nat := 118140960795 + 1143593 * 2 ^ 59
def prefixEnd_1143593 : Nat := 4983230072969 + 3 ^ 40 * 1143593 * 2
def baseEnd_1143593 : Nat := 260983503163221964812541

theorem tailTrace_1143593 : CollatzResearch.WordTrace tailWord_1143593 prefixEnd_1143593 260983503163221964812541 := by
  unfold tailWord_1143593
  simp only [CollatzResearch.WordTrace]
  refine ⟨41710263345965345980075433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27806842230643563986716955 41710263345965345980075433)
  ·
    refine ⟨31282697509474009485056575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41710263345965345980075433 31282697509474009485056575)
    ·
      refine ⟨46924046264211014227584863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31282697509474009485056575 46924046264211014227584863)
      ·
        refine ⟨70386069396316521341377295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46924046264211014227584863 70386069396316521341377295)
        ·
          refine ⟨105579104094474782012065943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70386069396316521341377295 105579104094474782012065943)
          ·
            refine ⟨158368656141712173018098915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105579104094474782012065943 158368656141712173018098915)
            ·
              refine ⟨237552984212568259527148373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158368656141712173018098915 237552984212568259527148373)
              ·
                refine ⟨1391912016870517145666885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 237552984212568259527148373 1391912016870517145666885)
                ·
                  refine ⟨260983503163221964812541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391912016870517145666885 260983503163221964812541)
                  ·
                    rfl

theorem cell21_1143593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_1143593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143593 prefixEnd_1143593 := by exact prefixLift 1143593
  have htrace : WordTrace (prefixWord ++ tailWord_1143593) baseStart_1143593 baseEnd_1143593 := by
    simpa [prefixWord, tailWord_1143593, baseEnd_1143593] using wordTrace_append hprefix tailTrace_1143593
  have hstable : (prefixWord ++ tailWord_1143593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143593).length < 2 ^ (prefixWord ++ tailWord_1143593).sum := by decide
  have hdescent : baseEnd_1143593 < baseStart_1143593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143607 : List Nat := [1, 1, 3, 1, 2, 1, 3, 9]
def baseStart_1143607 : Nat := 118140960795 + 1143607 * 2 ^ 59
def prefixEnd_1143607 : Nat := 4983230072969 + 3 ^ 40 * 1143607 * 2
def baseEnd_1143607 : Nat := 86995566051320350526393

theorem tailTrace_1143607 : CollatzResearch.WordTrace tailWord_1143607 prefixEnd_1143607 86995566051320350526393 := by
  unfold tailWord_1143607
  simp only [CollatzResearch.WordTrace]
  refine ⟨41710773967914626371085075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27807182645276417580723383 41710773967914626371085075)
  ·
    refine ⟨62566160951871939556627613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41710773967914626371085075 62566160951871939556627613)
    ·
      refine ⟨23462310356951977333735355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62566160951871939556627613 23462310356951977333735355)
      ·
        refine ⟨35193465535427966000603033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23462310356951977333735355 35193465535427966000603033)
        ·
          refine ⟨26395099151570974500452275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35193465535427966000603033 26395099151570974500452275)
          ·
            refine ⟨39592648727356461750678413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26395099151570974500452275 39592648727356461750678413)
            ·
              refine ⟨14847243272758673156504405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39592648727356461750678413 14847243272758673156504405)
              ·
                refine ⟨86995566051320350526393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14847243272758673156504405 86995566051320350526393)
                ·
                  rfl

theorem cell21_1143607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 9].length) (baseStart_1143607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143607 prefixEnd_1143607 := by exact prefixLift 1143607
  have htrace : WordTrace (prefixWord ++ tailWord_1143607) baseStart_1143607 baseEnd_1143607 := by
    simpa [prefixWord, tailWord_1143607, baseEnd_1143607] using wordTrace_append hprefix tailTrace_1143607
  have hstable : (prefixWord ++ tailWord_1143607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143607).length < 2 ^ (prefixWord ++ tailWord_1143607).sum := by decide
  have hdescent : baseEnd_1143607 < baseStart_1143607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143655 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 5]
def baseStart_1143655 : Nat := 118140960795 + 1143655 * 2 ^ 59
def prefixEnd_1143655 : Nat := 4983230072969 + 3 ^ 40 * 1143655 * 2
def baseEnd_1143655 : Nat := 260997652407923634779081

theorem tailTrace_1143655 : CollatzResearch.WordTrace tailWord_1143655 prefixEnd_1143655 260997652407923634779081 := by
  unfold tailWord_1143655
  simp only [CollatzResearch.WordTrace]
  refine ⟨41712524671740730568832419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27808349781160487045888279 41712524671740730568832419)
  ·
    refine ⟨62568787007611095853248629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41712524671740730568832419 62568787007611095853248629)
    ·
      refine ⟨5865823781963540236242059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62568787007611095853248629 5865823781963540236242059)
      ·
        refine ⟨8798735672945310354363089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5865823781963540236242059 8798735672945310354363089)
        ·
          refine ⟨6599051754708982765772317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8798735672945310354363089 6599051754708982765772317)
          ·
            refine ⟨2474644408015868537164619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6599051754708982765772317 2474644408015868537164619)
            ·
              refine ⟨3711966612023802805746929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474644408015868537164619 3711966612023802805746929)
              ·
                refine ⟨2783974959017852104310197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3711966612023802805746929 2783974959017852104310197)
                ·
                  refine ⟨260997652407923634779081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2783974959017852104310197 260997652407923634779081)
                  ·
                    rfl

theorem cell21_1143655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 5].length) (baseStart_1143655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143655 prefixEnd_1143655 := by exact prefixLift 1143655
  have htrace : WordTrace (prefixWord ++ tailWord_1143655) baseStart_1143655 baseEnd_1143655 := by
    simpa [prefixWord, tailWord_1143655, baseEnd_1143655] using wordTrace_append hprefix tailTrace_1143655
  have hstable : (prefixWord ++ tailWord_1143655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143655).length < 2 ^ (prefixWord ++ tailWord_1143655).sum := by decide
  have hdescent : baseEnd_1143655 < baseStart_1143655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143683 : List Nat := [1, 1, 1, 3, 4, 1, 10]
def baseStart_1143683 : Nat := 118140960795 + 1143683 * 2 ^ 59
def prefixEnd_1143683 : Nat := 4983230072969 + 3 ^ 40 * 1143683 * 2
def baseEnd_1143683 : Nat := 29000449154377978701373

theorem tailTrace_1143683 : CollatzResearch.WordTrace tailWord_1143683 prefixEnd_1143683 29000449154377978701373 := by
  unfold tailWord_1143683
  simp only [CollatzResearch.WordTrace]
  refine ⟨41713545915639291350851703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27809030610426194233901135 41713545915639291350851703)
  ·
    refine ⟨62570318873458937026277555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41713545915639291350851703 62570318873458937026277555)
    ·
      refine ⟨93855478310188405539416333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62570318873458937026277555 93855478310188405539416333)
      ·
        refine ⟨35195804366320652077281125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93855478310188405539416333 35195804366320652077281125)
        ·
          refine ⟨6599213318685122264490211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35195804366320652077281125 6599213318685122264490211)
          ·
            refine ⟨9898819978027683396735317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6599213318685122264490211 9898819978027683396735317)
            ·
              refine ⟨29000449154377978701373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9898819978027683396735317 29000449154377978701373)
              ·
                rfl

theorem cell21_1143683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 10].length) (baseStart_1143683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143683 prefixEnd_1143683 := by exact prefixLift 1143683
  have htrace : WordTrace (prefixWord ++ tailWord_1143683) baseStart_1143683 baseEnd_1143683 := by
    simpa [prefixWord, tailWord_1143683, baseEnd_1143683] using wordTrace_append hprefix tailTrace_1143683
  have hstable : (prefixWord ++ tailWord_1143683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143683).length < 2 ^ (prefixWord ++ tailWord_1143683).sum := by decide
  have hdescent : baseEnd_1143683 < baseStart_1143683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143700 : List Nat := [2, 4, 2, 1, 1, 1, 2, 8]
def baseStart_1143700 : Nat := 118140960795 + 1143700 * 2 ^ 59
def prefixEnd_1143700 : Nat := 4983230072969 + 3 ^ 40 * 1143700 * 2
def baseEnd_1143700 : Nat := 87002640673671185509663

theorem tailTrace_1143700 : CollatzResearch.WordTrace tailWord_1143700 prefixEnd_1143700 87002640673671185509663 := by
  unfold tailWord_1143700
  simp only [CollatzResearch.WordTrace]
  refine ⟨20857082978288851627110277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27809443971051802169480369 20857082978288851627110277)
  ·
    refine ⟨3910703058429159680083177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20857082978288851627110277 3910703058429159680083177)
    ·
      refine ⟨2933027293821869760062383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3910703058429159680083177 2933027293821869760062383)
      ·
        refine ⟨4399540940732804640093575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2933027293821869760062383 4399540940732804640093575)
        ·
          refine ⟨6599311411099206960140363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4399540940732804640093575 6599311411099206960140363)
          ·
            refine ⟨9898967116648810440210545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6599311411099206960140363 9898967116648810440210545)
            ·
              refine ⟨7424225337486607830157909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9898967116648810440210545 7424225337486607830157909)
              ·
                refine ⟨87002640673671185509663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7424225337486607830157909 87002640673671185509663)
                ·
                  rfl

theorem cell21_1143700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_1143700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143700 prefixEnd_1143700 := by exact prefixLift 1143700
  have htrace : WordTrace (prefixWord ++ tailWord_1143700) baseStart_1143700 baseEnd_1143700 := by
    simpa [prefixWord, tailWord_1143700, baseEnd_1143700] using wordTrace_append hprefix tailTrace_1143700
  have hstable : (prefixWord ++ tailWord_1143700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143700).length < 2 ^ (prefixWord ++ tailWord_1143700).sum := by decide
  have hdescent : baseEnd_1143700 < baseStart_1143700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143731 : List Nat := [1, 1, 1, 2, 3, 1, 2, 7, 3]
def baseStart_1143731 : Nat := 118140960795 + 1143731 * 2 ^ 59
def prefixEnd_1143731 : Nat := 4983230072969 + 3 ^ 40 * 1143731 * 2
def baseEnd_1143731 : Nat := 261014996643364391512259

theorem tailTrace_1143731 : CollatzResearch.WordTrace tailWord_1143731 prefixEnd_1143731 261014996643364391512259 := by
  unfold tailWord_1143731
  simp only [CollatzResearch.WordTrace]
  refine ⟨41715296619465395548599047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27810197746310263699066031 41715296619465395548599047)
  ·
    refine ⟨62572944929198093322898571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41715296619465395548599047 62572944929198093322898571)
    ·
      refine ⟨93859417393797139984347857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62572944929198093322898571 93859417393797139984347857)
      ·
        refine ⟨70394563045347854988260893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93859417393797139984347857 70394563045347854988260893)
        ·
          refine ⟨26397961142005445620597835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70394563045347854988260893 26397961142005445620597835)
          ·
            refine ⟨39596941713008168430896753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26397961142005445620597835 39596941713008168430896753)
            ·
              refine ⟨29697706284756126323172565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39596941713008168430896753 29697706284756126323172565)
              ·
                refine ⟨696039991048971710699357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29697706284756126323172565 696039991048971710699357)
                ·
                  refine ⟨261014996643364391512259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696039991048971710699357 261014996643364391512259)
                  ·
                    rfl

theorem cell21_1143731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 3].length) (baseStart_1143731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143731 prefixEnd_1143731 := by exact prefixLift 1143731
  have htrace : WordTrace (prefixWord ++ tailWord_1143731) baseStart_1143731 baseEnd_1143731 := by
    simpa [prefixWord, tailWord_1143731, baseEnd_1143731] using wordTrace_append hprefix tailTrace_1143731
  have hstable : (prefixWord ++ tailWord_1143731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143731).length < 2 ^ (prefixWord ++ tailWord_1143731).sum := by decide
  have hdescent : baseEnd_1143731 < baseStart_1143731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143759 : List Nat := [1, 1, 2, 1, 1, 6, 1, 8]
def baseStart_1143759 : Nat := 118140960795 + 1143759 * 2 ^ 59
def prefixEnd_1143759 : Nat := 4983230072969 + 3 ^ 40 * 1143759 * 2
def baseEnd_1143759 : Nat := 87007128874947521681845

theorem tailTrace_1143759 : CollatzResearch.WordTrace tailWord_1143759 prefixEnd_1143759 87007128874947521681845 := by
  unfold tailWord_1143759
  simp only [CollatzResearch.WordTrace]
  refine ⟨41716317863363956330618331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27810878575575970887078887 41716317863363956330618331)
  ·
    refine ⟨62574476795045934495927497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41716317863363956330618331 62574476795045934495927497)
    ·
      refine ⟨46930857596284450871945623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62574476795045934495927497 46930857596284450871945623)
      ·
        refine ⟨70396286394426676307918435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46930857596284450871945623 70396286394426676307918435)
        ·
          refine ⟨105594429591640014461877653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70396286394426676307918435 105594429591640014461877653)
          ·
            refine ⟨4949738887108125677900515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105594429591640014461877653 4949738887108125677900515)
            ·
              refine ⟨7424608330662188516850773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4949738887108125677900515 7424608330662188516850773)
              ·
                refine ⟨87007128874947521681845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7424608330662188516850773 87007128874947521681845)
                ·
                  rfl

theorem cell21_1143759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 8].length) (baseStart_1143759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143759 prefixEnd_1143759 := by exact prefixLift 1143759
  have htrace : WordTrace (prefixWord ++ tailWord_1143759) baseStart_1143759 baseEnd_1143759 := by
    simpa [prefixWord, tailWord_1143759, baseEnd_1143759] using wordTrace_append hprefix tailTrace_1143759
  have hstable : (prefixWord ++ tailWord_1143759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143759).length < 2 ^ (prefixWord ++ tailWord_1143759).sum := by decide
  have hdescent : baseEnd_1143759 < baseStart_1143759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143866 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_1143866 : Nat := 118140960795 + 1143866 * 2 ^ 59
def prefixEnd_1143866 : Nat := 4983230072969 + 3 ^ 40 * 1143866 * 2
def baseEnd_1143866 : Nat := 261045805482634156761983

theorem tailTrace_1143866 : CollatzResearch.WordTrace tailWord_1143866 prefixEnd_1143866 261045805482634156761983 := by
  unfold tailWord_1143866
  simp only [CollatzResearch.WordTrace]
  refine ⟨10430055118494078401190863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27813480315984209069842301 10430055118494078401190863)
  ·
    refine ⟨15645082677741117601786295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10430055118494078401190863 15645082677741117601786295)
    ·
      refine ⟨23467624016611676402679443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15645082677741117601786295 23467624016611676402679443)
      ·
        refine ⟨35201436024917514604019165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23467624016611676402679443 35201436024917514604019165)
        ·
          refine ⟨13200538509344067976507187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35201436024917514604019165 13200538509344067976507187)
          ·
            refine ⟨19800807764016101964760781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13200538509344067976507187 19800807764016101964760781)
            ·
              refine ⟨7425302911506038236785293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19800807764016101964760781 7425302911506038236785293)
              ·
                refine ⟨2784488591814764338794485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7425302911506038236785293 2784488591814764338794485)
                ·
                  refine ⟨261045805482634156761983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2784488591814764338794485 261045805482634156761983)
                  ·
                    rfl

theorem cell21_1143866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_1143866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143866 prefixEnd_1143866 := by exact prefixLift 1143866
  have htrace : WordTrace (prefixWord ++ tailWord_1143866) baseStart_1143866 baseEnd_1143866 := by
    simpa [prefixWord, tailWord_1143866, baseEnd_1143866] using wordTrace_append hprefix tailTrace_1143866
  have hstable : (prefixWord ++ tailWord_1143866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143866).length < 2 ^ (prefixWord ++ tailWord_1143866).sum := by decide
  have hdescent : baseEnd_1143866 < baseStart_1143866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143911 : List Nat := [1, 1, 5, 1, 1, 3, 9]
def baseStart_1143911 : Nat := 118140960795 + 1143911 * 2 ^ 59
def prefixEnd_1143911 : Nat := 4983230072969 + 3 ^ 40 * 1143911 * 2
def baseEnd_1143911 : Nat := 29006230566191564279099

theorem tailTrace_1143911 : CollatzResearch.WordTrace tailWord_1143911 prefixEnd_1143911 29006230566191564279099 := by
  unfold tailWord_1143911
  simp only [CollatzResearch.WordTrace]
  refine ⟨41721861758813286290151587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27814574505875524193434391 41721861758813286290151587)
  ·
    refine ⟨62582792638219929435227381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41721861758813286290151587 62582792638219929435227381)
    ·
      refine ⟨5867136809833118384552567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62582792638219929435227381 5867136809833118384552567)
      ·
        refine ⟨8800705214749677576828851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5867136809833118384552567 8800705214749677576828851)
        ·
          refine ⟨13201057822124516365243277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8800705214749677576828851 13201057822124516365243277)
          ·
            refine ⟨4950396683296693636966229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13201057822124516365243277 4950396683296693636966229)
            ·
              refine ⟨29006230566191564279099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4950396683296693636966229 29006230566191564279099)
              ·
                rfl

theorem cell21_1143911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 9].length) (baseStart_1143911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143911 prefixEnd_1143911 := by exact prefixLift 1143911
  have htrace : WordTrace (prefixWord ++ tailWord_1143911) baseStart_1143911 baseEnd_1143911 := by
    simpa [prefixWord, tailWord_1143911, baseEnd_1143911] using wordTrace_append hprefix tailTrace_1143911
  have hstable : (prefixWord ++ tailWord_1143911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143911).length < 2 ^ (prefixWord ++ tailWord_1143911).sum := by decide
  have hdescent : baseEnd_1143911 < baseStart_1143911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143917 : List Nat := [1, 5, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1143917 : Nat := 118140960795 + 1143917 * 2 ^ 59
def prefixEnd_1143917 : Nat := 4983230072969 + 3 ^ 40 * 1143917 * 2
def baseEnd_1143917 : Nat := 261057444377469401411879

theorem tailTrace_1143917 : CollatzResearch.WordTrace tailWord_1143917 prefixEnd_1143917 261057444377469401411879 := by
  unfold tailWord_1143917
  simp only [CollatzResearch.WordTrace]
  refine ⟨41722080596791549314870005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27814720397861032876580003 41722080596791549314870005)
  ·
    refine ⟨3911445055949207748269063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41722080596791549314870005 3911445055949207748269063)
    ·
      refine ⟨5867167583923811622403595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911445055949207748269063 5867167583923811622403595)
      ·
        refine ⟨8800751375885717433605393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5867167583923811622403595 8800751375885717433605393)
        ·
          refine ⟨6600563531914288075204045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8800751375885717433605393 6600563531914288075204045)
          ·
            refine ⟨2475211324467858028201517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6600563531914288075204045 2475211324467858028201517)
            ·
              refine ⟨928204246675446760575569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2475211324467858028201517 928204246675446760575569)
              ·
                refine ⟨696153185006585070431677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928204246675446760575569 696153185006585070431677)
                ·
                  refine ⟨261057444377469401411879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696153185006585070431677 261057444377469401411879)
                  ·
                    rfl

theorem cell21_1143917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1143917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143917 prefixEnd_1143917 := by exact prefixLift 1143917
  have htrace : WordTrace (prefixWord ++ tailWord_1143917) baseStart_1143917 baseEnd_1143917 := by
    simpa [prefixWord, tailWord_1143917, baseEnd_1143917] using wordTrace_append hprefix tailTrace_1143917
  have hstable : (prefixWord ++ tailWord_1143917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143917).length < 2 ^ (prefixWord ++ tailWord_1143917).sum := by decide
  have hdescent : baseEnd_1143917 < baseStart_1143917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143973 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 4]
def baseStart_1143973 : Nat := 118140960795 + 1143973 * 2 ^ 59
def prefixEnd_1143973 : Nat := 4983230072969 + 3 ^ 40 * 1143973 * 2
def baseEnd_1143973 : Nat := 261070224340425748478431

theorem tailTrace_1143973 : CollatzResearch.WordTrace tailWord_1143973 prefixEnd_1143973 261070224340425748478431 := by
  unfold tailWord_1143973
  simp only [CollatzResearch.WordTrace]
  refine ⟨41724123084588670878908573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27816082056392447252605715 41724123084588670878908573)
  ·
    refine ⟨15646546156720751579590715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41724123084588670878908573 15646546156720751579590715)
    ·
      refine ⟨23469819235081127369386073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15646546156720751579590715 23469819235081127369386073)
      ·
        refine ⟨17602364426310845527039555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23469819235081127369386073 17602364426310845527039555)
        ·
          refine ⟨26403546639466268290559333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17602364426310845527039555 26403546639466268290559333)
          ·
            refine ⟨4950664994899925304479875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26403546639466268290559333 4950664994899925304479875)
            ·
              refine ⟨7425997492349887956719813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950664994899925304479875 7425997492349887956719813)
              ·
                refine ⟨1392374529815603991884965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7425997492349887956719813 1392374529815603991884965)
                ·
                  refine ⟨261070224340425748478431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1392374529815603991884965 261070224340425748478431)
                  ·
                    rfl

theorem cell21_1143973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_1143973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143973 prefixEnd_1143973 := by exact prefixLift 1143973
  have htrace : WordTrace (prefixWord ++ tailWord_1143973) baseStart_1143973 baseEnd_1143973 := by
    simpa [prefixWord, tailWord_1143973, baseEnd_1143973] using wordTrace_append hprefix tailTrace_1143973
  have hstable : (prefixWord ++ tailWord_1143973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143973).length < 2 ^ (prefixWord ++ tailWord_1143973).sum := by decide
  have hdescent : baseEnd_1143973 < baseStart_1143973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143987 : List Nat := [1, 1, 1, 2, 3, 2, 5, 6]
def baseStart_1143987 : Nat := 118140960795 + 1143987 * 2 ^ 59
def prefixEnd_1143987 : Nat := 4983230072969 + 3 ^ 40 * 1143987 * 2
def baseEnd_1143987 : Nat := 87024473110388278415023

theorem tailTrace_1143987 : CollatzResearch.WordTrace tailWord_1143987 prefixEnd_1143987 87024473110388278415023 := by
  unfold tailWord_1143987
  simp only [CollatzResearch.WordTrace]
  refine ⟨41724633706537951269918215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27816422471025300846612143 41724633706537951269918215)
  ·
    refine ⟨62586950559806926904877323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41724633706537951269918215 62586950559806926904877323)
    ·
      refine ⟨93880425839710390357315985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62586950559806926904877323 93880425839710390357315985)
      ·
        refine ⟨70410319379782792767986989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93880425839710390357315985 70410319379782792767986989)
        ·
          refine ⟨26403869767418547287995121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70410319379782792767986989 26403869767418547287995121)
          ·
            refine ⟨19802902325563910465996341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26403869767418547287995121 19802902325563910465996341)
            ·
              refine ⟨1856522093021616606187157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19802902325563910465996341 1856522093021616606187157)
              ·
                refine ⟨87024473110388278415023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1856522093021616606187157 87024473110388278415023)
                ·
                  rfl

theorem cell21_1143987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 6].length) (baseStart_1143987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1143987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1143987 prefixEnd_1143987 := by exact prefixLift 1143987
  have htrace : WordTrace (prefixWord ++ tailWord_1143987) baseStart_1143987 baseEnd_1143987 := by
    simpa [prefixWord, tailWord_1143987, baseEnd_1143987] using wordTrace_append hprefix tailTrace_1143987
  have hstable : (prefixWord ++ tailWord_1143987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143987).length < 2 ^ (prefixWord ++ tailWord_1143987).sum := by decide
  have hdescent : baseEnd_1143987 < baseStart_1143987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144018 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1144018 : Nat := 118140960795 + 1144018 * 2 ^ 59
def prefixEnd_1144018 : Nat := 4983230072969 + 3 ^ 40 * 1144018 * 2
def baseEnd_1144018 : Nat := 261080493953515670228339

theorem tailTrace_1144018 : CollatzResearch.WordTrace tailWord_1144018 prefixEnd_1144018 261080493953515670228339 := by
  unfold tailWord_1144018
  simp only [CollatzResearch.WordTrace]
  refine ⟨10431441092356410891074177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27817176246283762376197805 10431441092356410891074177)
  ·
    refine ⟨7823580819267308168305633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10431441092356410891074177 7823580819267308168305633)
    ·
      refine ⟨5867685614450481126229225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7823580819267308168305633 5867685614450481126229225)
      ·
        refine ⟨4400764210837860844671919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5867685614450481126229225 4400764210837860844671919)
        ·
          refine ⟨6601146316256791267007879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4400764210837860844671919 6601146316256791267007879)
          ·
            refine ⟨9901719474385186900511819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6601146316256791267007879 9901719474385186900511819)
            ·
              refine ⟨14852579211577780350767729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9901719474385186900511819 14852579211577780350767729)
              ·
                refine ⟨11139434408683335263075797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14852579211577780350767729 11139434408683335263075797)
                ·
                  refine ⟨261080493953515670228339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11139434408683335263075797 261080493953515670228339)
                  ·
                    rfl

theorem cell21_1144018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1144018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144018 prefixEnd_1144018 := by exact prefixLift 1144018
  have htrace : WordTrace (prefixWord ++ tailWord_1144018) baseStart_1144018 baseEnd_1144018 := by
    simpa [prefixWord, tailWord_1144018, baseEnd_1144018] using wordTrace_append hprefix tailTrace_1144018
  have hstable : (prefixWord ++ tailWord_1144018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144018).length < 2 ^ (prefixWord ++ tailWord_1144018).sum := by decide
  have hdescent : baseEnd_1144018 < baseStart_1144018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144063 : List Nat := [1, 1, 2, 2, 1, 6, 1, 7]
def baseStart_1144063 : Nat := 118140960795 + 1144063 * 2 ^ 59
def prefixEnd_1144063 : Nat := 4983230072969 + 3 ^ 40 * 1144063 * 2
def baseEnd_1144063 : Nat := 87030254522201863992749

theorem tailTrace_1144063 : CollatzResearch.WordTrace tailWord_1144063 prefixEnd_1144063 87030254522201863992749 := by
  unfold tailWord_1144063
  simp only [CollatzResearch.WordTrace]
  refine ⟨41727405654262616249684843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27818270436175077499789895 41727405654262616249684843)
  ·
    refine ⟨62591108481393924374527265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41727405654262616249684843 62591108481393924374527265)
    ·
      refine ⟨46943331361045443280895449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62591108481393924374527265 46943331361045443280895449)
      ·
        refine ⟨35207498520784082460671587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46943331361045443280895449 35207498520784082460671587)
        ·
          refine ⟨52811247781176123691007381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35207498520784082460671587 52811247781176123691007381)
          ·
            refine ⟨2475527239742630798015971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52811247781176123691007381 2475527239742630798015971)
            ·
              refine ⟨3713290859613946197023957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2475527239742630798015971 3713290859613946197023957)
              ·
                refine ⟨87030254522201863992749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3713290859613946197023957 87030254522201863992749)
                ·
                  rfl

theorem cell21_1144063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 7].length) (baseStart_1144063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144063 prefixEnd_1144063 := by exact prefixLift 1144063
  have htrace : WordTrace (prefixWord ++ tailWord_1144063) baseStart_1144063 baseEnd_1144063 := by
    simpa [prefixWord, tailWord_1144063, baseEnd_1144063] using wordTrace_append hprefix tailTrace_1144063
  have hstable : (prefixWord ++ tailWord_1144063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144063).length < 2 ^ (prefixWord ++ tailWord_1144063).sum := by decide
  have hdescent : baseEnd_1144063 < baseStart_1144063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144187 : List Nat := [1, 1, 1, 1, 1, 6, 4, 3, 3]
def baseStart_1144187 : Nat := 118140960795 + 1144187 * 2 ^ 59
def prefixEnd_1144187 : Nat := 4983230072969 + 3 ^ 40 * 1144187 * 2
def baseEnd_1144187 : Nat := 261119062056008931911327

theorem tailTrace_1144187 : CollatzResearch.WordTrace tailWord_1144187 prefixEnd_1144187 261119062056008931911327 := by
  unfold tailWord_1144187
  simp only [CollatzResearch.WordTrace]
  refine ⟨41731928305813385427198815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27821285537208923618132543 41731928305813385427198815)
  ·
    refine ⟨62597892458720078140798223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41731928305813385427198815 62597892458720078140798223)
    ·
      refine ⟨93896838688080117211197335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62597892458720078140798223 93896838688080117211197335)
      ·
        refine ⟨140845258032120175816796003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93896838688080117211197335 140845258032120175816796003)
        ·
          refine ⟨211267887048180263725194005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140845258032120175816796003 211267887048180263725194005)
          ·
            refine ⟨9903182205383449862118469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211267887048180263725194005 9903182205383449862118469)
            ·
              refine ⟨1856846663509396849147213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9903182205383449862118469 1856846663509396849147213)
              ·
                refine ⟨696317498816023818430205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1856846663509396849147213 696317498816023818430205)
                ·
                  refine ⟨261119062056008931911327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696317498816023818430205 261119062056008931911327)
                  ·
                    rfl

theorem cell21_1144187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 3].length) (baseStart_1144187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144187 prefixEnd_1144187 := by exact prefixLift 1144187
  have htrace : WordTrace (prefixWord ++ tailWord_1144187) baseStart_1144187 baseEnd_1144187 := by
    simpa [prefixWord, tailWord_1144187, baseEnd_1144187] using wordTrace_append hprefix tailTrace_1144187
  have hstable : (prefixWord ++ tailWord_1144187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144187).length < 2 ^ (prefixWord ++ tailWord_1144187).sum := by decide
  have hdescent : baseEnd_1144187 < baseStart_1144187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144201 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 6]
def baseStart_1144201 : Nat := 118140960795 + 1144201 * 2 ^ 59
def prefixEnd_1144201 : Nat := 4983230072969 + 3 ^ 40 * 1144201 * 2
def baseEnd_1144201 : Nat := 261122257046748018677965

theorem tailTrace_1144201 : CollatzResearch.WordTrace tailWord_1144201 prefixEnd_1144201 261122257046748018677965 := by
  unfold tailWord_1144201
  simp only [CollatzResearch.WordTrace]
  refine ⟨41732438927762665818208457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27821625951841777212138971 41732438927762665818208457)
  ·
    refine ⟨31299329195821999363656343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41732438927762665818208457 31299329195821999363656343)
    ·
      refine ⟨46948993793732999045484515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31299329195821999363656343 46948993793732999045484515)
      ·
        refine ⟨70423490690599498568226773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46948993793732999045484515 70423490690599498568226773)
        ·
          refine ⟨1650550563060925747692815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 70423490690599498568226773 1650550563060925747692815)
          ·
            refine ⟨2475825844591388621539223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650550563060925747692815 2475825844591388621539223)
            ·
              refine ⟨3713738766887082932308835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2475825844591388621539223 3713738766887082932308835)
              ·
                refine ⟨5570608150330624398463253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713738766887082932308835 5570608150330624398463253)
                ·
                  refine ⟨261122257046748018677965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5570608150330624398463253 261122257046748018677965)
                  ·
                    rfl

theorem cell21_1144201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_1144201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144201 prefixEnd_1144201 := by exact prefixLift 1144201
  have htrace : WordTrace (prefixWord ++ tailWord_1144201) baseStart_1144201 baseEnd_1144201 := by
    simpa [prefixWord, tailWord_1144201, baseEnd_1144201] using wordTrace_append hprefix tailTrace_1144201
  have hstable : (prefixWord ++ tailWord_1144201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144201).length < 2 ^ (prefixWord ++ tailWord_1144201).sum := by decide
  have hdescent : baseEnd_1144201 < baseStart_1144201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144218 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_1144218 : Nat := 118140960795 + 1144218 * 2 ^ 59
def prefixEnd_1144218 : Nat := 4983230072969 + 3 ^ 40 * 1144218 * 2
def baseEnd_1144218 : Nat := 261126136678359766894597

theorem tailTrace_1144218 : CollatzResearch.WordTrace tailWord_1144218 prefixEnd_1144218 261126136678359766894597 := by
  unfold tailWord_1144218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10433264742175269430394327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27822039312467385147718205 10433264742175269430394327)
  ·
    refine ⟨15649897113262904145591491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10433264742175269430394327 15649897113262904145591491)
    ·
      refine ⟨23474845669894356218387237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15649897113262904145591491 23474845669894356218387237)
      ·
        refine ⟨4401533563105191790947607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23474845669894356218387237 4401533563105191790947607)
        ·
          refine ⟨6602300344657787686421411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401533563105191790947607 6602300344657787686421411)
          ·
            refine ⟨9903450516986681529632117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6602300344657787686421411 9903450516986681529632117)
            ·
              refine ⟨928448485967501393403011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9903450516986681529632117 928448485967501393403011)
              ·
                refine ⟨1392672728951252090104517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928448485967501393403011 1392672728951252090104517)
                ·
                  refine ⟨261126136678359766894597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1392672728951252090104517 261126136678359766894597)
                  ·
                    rfl

theorem cell21_1144218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_1144218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144218 prefixEnd_1144218 := by exact prefixLift 1144218
  have htrace : WordTrace (prefixWord ++ tailWord_1144218) baseStart_1144218 baseEnd_1144218 := by
    simpa [prefixWord, tailWord_1144218, baseEnd_1144218] using wordTrace_append hprefix tailTrace_1144218
  have hstable : (prefixWord ++ tailWord_1144218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144218).length < 2 ^ (prefixWord ++ tailWord_1144218).sum := by decide
  have hdescent : baseEnd_1144218 < baseStart_1144218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144229 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 7]
def baseStart_1144229 : Nat := 118140960795 + 1144229 * 2 ^ 59
def prefixEnd_1144229 : Nat := 4983230072969 + 3 ^ 40 * 1144229 * 2
def baseEnd_1144229 : Nat := 261128647028226192211241

theorem tailTrace_1144229 : CollatzResearch.WordTrace tailWord_1144229 prefixEnd_1144229 261128647028226192211241 := by
  unfold tailWord_1144229
  simp only [CollatzResearch.WordTrace]
  refine ⟨41733460171661226600227741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27822306781107484400151827 41733460171661226600227741)
  ·
    refine ⟨15650047564372959975085403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41733460171661226600227741 15650047564372959975085403)
    ·
      refine ⟨23475071346559439962628105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15650047564372959975085403 23475071346559439962628105)
      ·
        refine ⟨17606303509919579971971079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23475071346559439962628105 17606303509919579971971079)
        ·
          refine ⟨26409455264879369957956619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17606303509919579971971079 26409455264879369957956619)
          ·
            refine ⟨39614182897319054936934929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26409455264879369957956619 39614182897319054936934929)
            ·
              refine ⟨29710637172989291202701197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39614182897319054936934929 29710637172989291202701197)
              ·
                refine ⟨11141488939870984201012949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29710637172989291202701197 11141488939870984201012949)
                ·
                  refine ⟨261128647028226192211241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11141488939870984201012949 261128647028226192211241)
                  ·
                    rfl

theorem cell21_1144229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_1144229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144229 prefixEnd_1144229 := by exact prefixLift 1144229
  have htrace : WordTrace (prefixWord ++ tailWord_1144229) baseStart_1144229 baseEnd_1144229 := by
    simpa [prefixWord, tailWord_1144229, baseEnd_1144229] using wordTrace_append hprefix tailTrace_1144229
  have hstable : (prefixWord ++ tailWord_1144229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144229).length < 2 ^ (prefixWord ++ tailWord_1144229).sum := by decide
  have hdescent : baseEnd_1144229 < baseStart_1144229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144277 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 4]
def baseStart_1144277 : Nat := 118140960795 + 1144277 * 2 ^ 59
def prefixEnd_1144277 : Nat := 4983230072969 + 3 ^ 40 * 1144277 * 2
def baseEnd_1144277 : Nat := 261139601282188775411143

theorem tailTrace_1144277 : CollatzResearch.WordTrace tailWord_1144277 prefixEnd_1144277 261139601282188775411143 := by
  unfold tailWord_1144277
  simp only [CollatzResearch.WordTrace]
  refine ⟨41735210875487330797975085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27823473916991553865316723 41735210875487330797975085)
  ·
    refine ⟨15650704078307749049240657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41735210875487330797975085 15650704078307749049240657)
    ·
      refine ⟨11738028058730811786930493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15650704078307749049240657 11738028058730811786930493)
      ·
        refine ⟨4401760522024054420098935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11738028058730811786930493 4401760522024054420098935)
        ·
          refine ⟨6602640783036081630148403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401760522024054420098935 6602640783036081630148403)
          ·
            refine ⟨9903961174554122445222605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6602640783036081630148403 9903961174554122445222605)
            ·
              refine ⟨3713985440457795916958477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9903961174554122445222605 3713985440457795916958477)
              ·
                refine ⟨1392744540171673468859429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3713985440457795916958477 1392744540171673468859429)
                ·
                  refine ⟨261139601282188775411143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1392744540171673468859429 261139601282188775411143)
                  ·
                    rfl

theorem cell21_1144277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_1144277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144277 prefixEnd_1144277 := by exact prefixLift 1144277
  have htrace : WordTrace (prefixWord ++ tailWord_1144277) baseStart_1144277 baseEnd_1144277 := by
    simpa [prefixWord, tailWord_1144277, baseEnd_1144277] using wordTrace_append hprefix tailTrace_1144277
  have hstable : (prefixWord ++ tailWord_1144277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144277).length < 2 ^ (prefixWord ++ tailWord_1144277).sum := by decide
  have hdescent : baseEnd_1144277 < baseStart_1144277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144291 : List Nat := [1, 1, 1, 6, 2, 1, 2, 7]
def baseStart_1144291 : Nat := 118140960795 + 1144291 * 2 ^ 59
def prefixEnd_1144291 : Nat := 4983230072969 + 3 ^ 40 * 1144291 * 2
def baseEnd_1144291 : Nat := 87047598757642620725927

theorem tailTrace_1144291 : CollatzResearch.WordTrace tailWord_1144291 prefixEnd_1144291 87047598757642620725927 := by
  unfold tailWord_1144291
  simp only [CollatzResearch.WordTrace]
  refine ⟨41735721497436611188984727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27823814331624407459323151 41735721497436611188984727)
  ·
    refine ⟨62603582246154916783477091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41735721497436611188984727 62603582246154916783477091)
    ·
      refine ⟨93905373369232375175215637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62603582246154916783477091 93905373369232375175215637)
      ·
        refine ⟨4401814376682767586338233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93905373369232375175215637 4401814376682767586338233)
        ·
          refine ⟨3301360782512075689753675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4401814376682767586338233 3301360782512075689753675)
          ·
            refine ⟨4952041173768113534630513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301360782512075689753675 4952041173768113534630513)
            ·
              refine ⟨3714030880326085150972885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4952041173768113534630513 3714030880326085150972885)
              ·
                refine ⟨87047598757642620725927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3714030880326085150972885 87047598757642620725927)
                ·
                  rfl

theorem cell21_1144291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 7].length) (baseStart_1144291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144291 prefixEnd_1144291 := by exact prefixLift 1144291
  have htrace : WordTrace (prefixWord ++ tailWord_1144291) baseStart_1144291 baseEnd_1144291 := by
    simpa [prefixWord, tailWord_1144291, baseEnd_1144291] using wordTrace_append hprefix tailTrace_1144291
  have hstable : (prefixWord ++ tailWord_1144291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144291).length < 2 ^ (prefixWord ++ tailWord_1144291).sum := by decide
  have hdescent : baseEnd_1144291 < baseStart_1144291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144432 : List Nat := [2, 1, 1, 1, 6, 2, 3, 2, 3]
def baseStart_1144432 : Nat := 118140960795 + 1144432 * 2 ^ 59
def prefixEnd_1144432 : Nat := 4983230072969 + 3 ^ 40 * 1144432 * 2
def baseEnd_1144432 : Nat := 261174974393942950327493

theorem tailTrace_1144432 : CollatzResearch.WordTrace tailWord_1144432 prefixEnd_1144432 261174974393942950327493 := by
  unfold tailWord_1144432
  simp only [CollatzResearch.WordTrace]
  refine ⟨20870432094962896134933775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27827242793283861513245033 20870432094962896134933775)
  ·
    refine ⟨31305648142444344202400663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20870432094962896134933775 31305648142444344202400663)
    ·
      refine ⟨46958472213666516303600995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31305648142444344202400663 46958472213666516303600995)
      ·
        refine ⟨70437708320499774455401493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46958472213666516303600995 70437708320499774455401493)
        ·
          refine ⟨3301767577523426927596945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70437708320499774455401493 3301767577523426927596945)
          ·
            refine ⟨2476325683142570195697709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3301767577523426927596945 2476325683142570195697709)
            ·
              refine ⟨928622131178463823386641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2476325683142570195697709 928622131178463823386641)
              ·
                refine ⟨696466598383847867539981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928622131178463823386641 696466598383847867539981)
                ·
                  refine ⟨261174974393942950327493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696466598383847867539981 261174974393942950327493)
                  ·
                    rfl

theorem cell21_1144432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 3].length) (baseStart_1144432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144432 prefixEnd_1144432 := by exact prefixLift 1144432
  have htrace : WordTrace (prefixWord ++ tailWord_1144432) baseStart_1144432 baseEnd_1144432 := by
    simpa [prefixWord, tailWord_1144432, baseEnd_1144432] using wordTrace_append hprefix tailTrace_1144432
  have hstable : (prefixWord ++ tailWord_1144432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144432).length < 2 ^ (prefixWord ++ tailWord_1144432).sum := by decide
  have hdescent : baseEnd_1144432 < baseStart_1144432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144457 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 5]
def baseStart_1144457 : Nat := 118140960795 + 1144457 * 2 ^ 59
def prefixEnd_1144457 : Nat := 4983230072969 + 3 ^ 40 * 1144457 * 2
def baseEnd_1144457 : Nat := 261180679734548462410775

theorem tailTrace_1144457 : CollatzResearch.WordTrace tailWord_1144457 prefixEnd_1144457 261180679734548462410775 := by
  unfold tailWord_1144457
  simp only [CollatzResearch.WordTrace]
  refine ⟨41741776014835221539527625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27827850676556814359685083 41741776014835221539527625)
  ·
    refine ⟨31306332011126416154645719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41741776014835221539527625 31306332011126416154645719)
    ·
      refine ⟨46959498016689624231968579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31306332011126416154645719 46959498016689624231968579)
      ·
        refine ⟨70439247025034436347952869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46959498016689624231968579 70439247025034436347952869)
        ·
          refine ⟨13207358817193956815241163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70439247025034436347952869 13207358817193956815241163)
          ·
            refine ⟨19811038225790935222861745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13207358817193956815241163 19811038225790935222861745)
            ·
              refine ⟨14858278669343201417146309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19811038225790935222861745 14858278669343201417146309)
              ·
                refine ⟨2785927250501850265714933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14858278669343201417146309 2785927250501850265714933)
                ·
                  refine ⟨261180679734548462410775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2785927250501850265714933 261180679734548462410775)
                  ·
                    rfl

theorem cell21_1144457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_1144457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144457 prefixEnd_1144457 := by exact prefixLift 1144457
  have htrace : WordTrace (prefixWord ++ tailWord_1144457) baseStart_1144457 baseEnd_1144457 := by
    simpa [prefixWord, tailWord_1144457, baseEnd_1144457] using wordTrace_append hprefix tailTrace_1144457
  have hstable : (prefixWord ++ tailWord_1144457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144457).length < 2 ^ (prefixWord ++ tailWord_1144457).sum := by decide
  have hdescent : baseEnd_1144457 < baseStart_1144457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144494 : List Nat := [4, 1, 4, 1, 3, 1, 1, 6]
def baseStart_1144494 : Nat := 118140960795 + 1144494 * 2 ^ 59
def prefixEnd_1144494 : Nat := 4983230072969 + 3 ^ 40 * 1144494 * 2
def baseEnd_1144494 : Nat := 87063041212881540098011

theorem tailTrace_1144494 : CollatzResearch.WordTrace tailWord_1144494 prefixEnd_1144494 87063041212881540098011 := by
  unfold tailWord_1144494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5217890689462647107328067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27828750343800784572416357 5217890689462647107328067)
  ·
    refine ⟨7826836034193970660992101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5217890689462647107328067 7826836034193970660992101)
    ·
      refine ⟨1467531756411369498936019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7826836034193970660992101 1467531756411369498936019)
      ·
        refine ⟨2201297634617054248404029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1467531756411369498936019 2201297634617054248404029)
        ·
          refine ⟨825486612981395343151511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2201297634617054248404029 825486612981395343151511)
          ·
            refine ⟨1238229919472093014727267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825486612981395343151511 1238229919472093014727267)
            ·
              refine ⟨1857344879208139522090901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238229919472093014727267 1857344879208139522090901)
              ·
                refine ⟨87063041212881540098011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1857344879208139522090901 87063041212881540098011)
                ·
                  rfl

theorem cell21_1144494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_1144494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144494 prefixEnd_1144494 := by exact prefixLift 1144494
  have htrace : WordTrace (prefixWord ++ tailWord_1144494) baseStart_1144494 baseEnd_1144494 := by
    simpa [prefixWord, tailWord_1144494, baseEnd_1144494] using wordTrace_append hprefix tailTrace_1144494
  have hstable : (prefixWord ++ tailWord_1144494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144494).length < 2 ^ (prefixWord ++ tailWord_1144494).sum := by decide
  have hdescent : baseEnd_1144494 < baseStart_1144494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144519 : List Nat := [1, 1, 4, 1, 1, 1, 7, 5]
def baseStart_1144519 : Nat := 118140960795 + 1144519 * 2 ^ 59
def prefixEnd_1144519 : Nat := 4983230072969 + 3 ^ 40 * 1144519 * 2
def baseEnd_1144519 : Nat := 87064942993083377459105

theorem tailTrace_1144519 : CollatzResearch.WordTrace tailWord_1144519 prefixEnd_1144519 87064942993083377459105 := by
  unfold tailWord_1144519
  simp only [CollatzResearch.WordTrace]
  refine ⟨41744037340610606128284611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27829358227073737418856407 41744037340610606128284611)
  ·
    refine ⟨62616056010915909192426917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41744037340610606128284611 62616056010915909192426917)
    ·
      refine ⟨11740510502046732973580047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62616056010915909192426917 11740510502046732973580047)
      ·
        refine ⟨17610765753070099460370071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11740510502046732973580047 17610765753070099460370071)
        ·
          refine ⟨26416148629605149190555107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17610765753070099460370071 26416148629605149190555107)
          ·
            refine ⟨39624222944407723785832661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26416148629605149190555107 39624222944407723785832661)
            ·
              refine ⟨928692725259556026230453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39624222944407723785832661 928692725259556026230453)
              ·
                refine ⟨87064942993083377459105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 928692725259556026230453 87064942993083377459105)
                ·
                  rfl

theorem cell21_1144519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 5].length) (baseStart_1144519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144519 prefixEnd_1144519 := by exact prefixLift 1144519
  have htrace : WordTrace (prefixWord ++ tailWord_1144519) baseStart_1144519 baseEnd_1144519 := by
    simpa [prefixWord, tailWord_1144519, baseEnd_1144519] using wordTrace_append hprefix tailTrace_1144519
  have hstable : (prefixWord ++ tailWord_1144519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144519).length < 2 ^ (prefixWord ++ tailWord_1144519).sum := by decide
  have hdescent : baseEnd_1144519 < baseStart_1144519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144525 : List Nat := [1, 6, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1144525 : Nat := 118140960795 + 1144525 * 2 ^ 59
def prefixEnd_1144525 : Nat := 4983230072969 + 3 ^ 40 * 1144525 * 2
def baseEnd_1144525 : Nat := 261196198260995455277303

theorem tailTrace_1144525 : CollatzResearch.WordTrace tailWord_1144525 prefixEnd_1144525 261196198260995455277303 := by
  unfold tailWord_1144525
  simp only [CollatzResearch.WordTrace]
  refine ⟨41744256178588869153003029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27829504119059246102002019 41744256178588869153003029)
  ·
    refine ⟨1956762008371353241547017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41744256178588869153003029 1956762008371353241547017)
    ·
      refine ⟨1467571506278514931160263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1956762008371353241547017 1467571506278514931160263)
      ·
        refine ⟨2201357259417772396740395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1467571506278514931160263 2201357259417772396740395)
        ·
          refine ⟨3302035889126658595110593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201357259417772396740395 3302035889126658595110593)
          ·
            refine ⟨2476526916844993946332945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3302035889126658595110593 2476526916844993946332945)
            ·
              refine ⟨1857395187633745459749709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2476526916844993946332945 1857395187633745459749709)
              ·
                refine ⟨696523195362654547406141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1857395187633745459749709 696523195362654547406141)
                ·
                  refine ⟨261196198260995455277303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696523195362654547406141 261196198260995455277303)
                  ·
                    rfl

theorem cell21_1144525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1144525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144525 prefixEnd_1144525 := by exact prefixLift 1144525
  have htrace : WordTrace (prefixWord ++ tailWord_1144525) baseStart_1144525 baseEnd_1144525 := by
    simpa [prefixWord, tailWord_1144525, baseEnd_1144525] using wordTrace_append hprefix tailTrace_1144525
  have hstable : (prefixWord ++ tailWord_1144525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144525).length < 2 ^ (prefixWord ++ tailWord_1144525).sum := by decide
  have hdescent : baseEnd_1144525 < baseStart_1144525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144657 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 4]
def baseStart_1144657 : Nat := 118140960795 + 1144657 * 2 ^ 59
def prefixEnd_1144657 : Nat := 4983230072969 + 3 ^ 40 * 1144657 * 2
def baseEnd_1144657 : Nat := 261226322459392559077033

theorem tailTrace_1144657 : CollatzResearch.WordTrace tailWord_1144657 prefixEnd_1144657 261226322459392559077033 := by
  unfold tailWord_1144657
  simp only [CollatzResearch.WordTrace]
  refine ⟨41749070614110655696808225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27832713742740437131205483 41749070614110655696808225)
  ·
    refine ⟨31311802960582991772606169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41749070614110655696808225 31311802960582991772606169)
    ·
      refine ⟨23483852220437243829454627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31311802960582991772606169 23483852220437243829454627)
      ·
        refine ⟨35225778330655865744181941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23483852220437243829454627 35225778330655865744181941)
        ·
          refine ⟨3302416718498987413517057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35225778330655865744181941 3302416718498987413517057)
          ·
            refine ⟨2476812538874240560137793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3302416718498987413517057 2476812538874240560137793)
            ·
              refine ⟨1857609404155680420103345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2476812538874240560137793 1857609404155680420103345)
              ·
                refine ⟨1393207053116760315077509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1857609404155680420103345 1393207053116760315077509)
                ·
                  refine ⟨261226322459392559077033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1393207053116760315077509 261226322459392559077033)
                  ·
                    rfl

theorem cell21_1144657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_1144657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144657 prefixEnd_1144657 := by exact prefixLift 1144657
  have htrace : WordTrace (prefixWord ++ tailWord_1144657) baseStart_1144657 baseEnd_1144657 := by
    simpa [prefixWord, tailWord_1144657, baseEnd_1144657] using wordTrace_append hprefix tailTrace_1144657
  have hstable : (prefixWord ++ tailWord_1144657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144657).length < 2 ^ (prefixWord ++ tailWord_1144657).sum := by decide
  have hdescent : baseEnd_1144657 < baseStart_1144657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144660 : List Nat := [2, 4, 1, 1, 3, 1, 4, 2, 3]
def baseStart_1144660 : Nat := 118140960795 + 1144660 * 2 ^ 59
def prefixEnd_1144660 : Nat := 4983230072969 + 3 ^ 40 * 1144660 * 2
def baseEnd_1144660 : Nat := 261227007100265220527027

theorem tailTrace_1144660 : CollatzResearch.WordTrace tailWord_1144660 prefixEnd_1144660 261227007100265220527027 := by
  unfold tailWord_1144660
  simp only [CollatzResearch.WordTrace]
  refine ⟨20874590016549893604583717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27832786688733191472778289 20874590016549893604583717)
  ·
    refine ⟨3913985628103105050859447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20874590016549893604583717 3913985628103105050859447)
    ·
      refine ⟨5870978442154657576289171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3913985628103105050859447 5870978442154657576289171)
      ·
        refine ⟨8806467663231986364433757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5870978442154657576289171 8806467663231986364433757)
        ·
          refine ⟨3302425373711994886662659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8806467663231986364433757 3302425373711994886662659)
          ·
            refine ⟨4953638060567992329993989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302425373711994886662659 4953638060567992329993989)
            ·
              refine ⟨928807136356498561873873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4953638060567992329993989 928807136356498561873873)
              ·
                refine ⟨696605352267373921405405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928807136356498561873873 696605352267373921405405)
                ·
                  refine ⟨261227007100265220527027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696605352267373921405405 261227007100265220527027)
                  ·
                    rfl

theorem cell21_1144660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_1144660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144660 prefixEnd_1144660 := by exact prefixLift 1144660
  have htrace : WordTrace (prefixWord ++ tailWord_1144660) baseStart_1144660 baseEnd_1144660 := by
    simpa [prefixWord, tailWord_1144660, baseEnd_1144660] using wordTrace_append hprefix tailTrace_1144660
  have hstable : (prefixWord ++ tailWord_1144660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144660).length < 2 ^ (prefixWord ++ tailWord_1144660).sum := by decide
  have hdescent : baseEnd_1144660 < baseStart_1144660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144671 : List Nat := [1, 1, 2, 3, 1, 6, 1, 6]
def baseStart_1144671 : Nat := 118140960795 + 1144671 * 2 ^ 59
def prefixEnd_1144671 : Nat := 4983230072969 + 3 ^ 40 * 1144671 * 2
def baseEnd_1144671 : Nat := 87076505816710548614557

theorem tailTrace_1144671 : CollatzResearch.WordTrace tailWord_1144671 prefixEnd_1144671 87076505816710548614557 := by
  unfold tailWord_1144671
  simp only [CollatzResearch.WordTrace]
  refine ⟨41749581236059936087817867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27833054157373290725211911 41749581236059936087817867)
  ·
    refine ⟨62624371854089904131726801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41749581236059936087817867 62624371854089904131726801)
    ·
      refine ⟨46968278890567428098795101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62624371854089904131726801 46968278890567428098795101)
      ·
        refine ⟨17613104583962785537048163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46968278890567428098795101 17613104583962785537048163)
        ·
          refine ⟨26419656875944178305572245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17613104583962785537048163 26419656875944178305572245)
          ·
            refine ⟨1238421416059883358073699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26419656875944178305572245 1238421416059883358073699)
            ·
              refine ⟨1857632124089825037110549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238421416059883358073699 1857632124089825037110549)
              ·
                refine ⟨87076505816710548614557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1857632124089825037110549 87076505816710548614557)
                ·
                  rfl

theorem cell21_1144671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 6].length) (baseStart_1144671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144671 prefixEnd_1144671 := by exact prefixLift 1144671
  have htrace : WordTrace (prefixWord ++ tailWord_1144671) baseStart_1144671 baseEnd_1144671 := by
    simpa [prefixWord, tailWord_1144671, baseEnd_1144671] using wordTrace_append hprefix tailTrace_1144671
  have hstable : (prefixWord ++ tailWord_1144671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144671).length < 2 ^ (prefixWord ++ tailWord_1144671).sum := by decide
  have hdescent : baseEnd_1144671 < baseStart_1144671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144685 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1144685 : Nat := 118140960795 + 1144685 * 2 ^ 59
def prefixEnd_1144685 : Nat := 4983230072969 + 3 ^ 40 * 1144685 * 2
def baseEnd_1144685 : Nat := 261232712440870732610309

theorem tailTrace_1144685 : CollatzResearch.WordTrace tailWord_1144685 prefixEnd_1144685 261232712440870732610309 := by
  unfold tailWord_1144685
  simp only [CollatzResearch.WordTrace]
  refine ⟨41750091858009216478827509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27833394572006144319218339 41750091858009216478827509)
  ·
    refine ⟨3914071111688364044890079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41750091858009216478827509 3914071111688364044890079)
    ·
      refine ⟨5871106667532546067335119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3914071111688364044890079 5871106667532546067335119)
      ·
        refine ⟨8806660001298819101002679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5871106667532546067335119 8806660001298819101002679)
        ·
          refine ⟨13209990001948228651504019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8806660001298819101002679 13209990001948228651504019)
          ·
            refine ⟨19814985002922342977256029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13209990001948228651504019 19814985002922342977256029)
            ·
              refine ⟨7430619376095878616471011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19814985002922342977256029 7430619376095878616471011)
              ·
                refine ⟨11145929064143817924706517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7430619376095878616471011 11145929064143817924706517)
                ·
                  refine ⟨261232712440870732610309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11145929064143817924706517 261232712440870732610309)
                  ·
                    rfl

theorem cell21_1144685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1144685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144685 prefixEnd_1144685 := by exact prefixLift 1144685
  have htrace : WordTrace (prefixWord ++ tailWord_1144685) baseStart_1144685 baseEnd_1144685 := by
    simpa [prefixWord, tailWord_1144685, baseEnd_1144685] using wordTrace_append hprefix tailTrace_1144685
  have hstable : (prefixWord ++ tailWord_1144685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144685).length < 2 ^ (prefixWord ++ tailWord_1144685).sum := by decide
  have hdescent : baseEnd_1144685 < baseStart_1144685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144699 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 6]
def baseStart_1144699 : Nat := 118140960795 + 1144699 * 2 ^ 59
def prefixEnd_1144699 : Nat := 4983230072969 + 3 ^ 40 * 1144699 * 2
def baseEnd_1144699 : Nat := 261235907431609819376947

theorem tailTrace_1144699 : CollatzResearch.WordTrace tailWord_1144699 prefixEnd_1144699 261235907431609819376947 := by
  unfold tailWord_1144699
  simp only [CollatzResearch.WordTrace]
  refine ⟨41750602479958496869837151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27833734986638997913224767 41750602479958496869837151)
  ·
    refine ⟨62625903719937745304755727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41750602479958496869837151 62625903719937745304755727)
    ·
      refine ⟨93938855579906617957133591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62625903719937745304755727 93938855579906617957133591)
      ·
        refine ⟨140908283369859926935700387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93938855579906617957133591 140908283369859926935700387)
        ·
          refine ⟨211362425054789890403550581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140908283369859926935700387 211362425054789890403550581)
          ·
            refine ⟨19815227348886552225332867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211362425054789890403550581 19815227348886552225332867)
            ·
              refine ⟨29722841023329828337999301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19815227348886552225332867 29722841023329828337999301)
              ·
                refine ⟨5573032691874342813374869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29722841023329828337999301 5573032691874342813374869)
                ·
                  refine ⟨261235907431609819376947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5573032691874342813374869 261235907431609819376947)
                  ·
                    rfl

theorem cell21_1144699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_1144699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144699 prefixEnd_1144699 := by exact prefixLift 1144699
  have htrace : WordTrace (prefixWord ++ tailWord_1144699) baseStart_1144699 baseEnd_1144699 := by
    simpa [prefixWord, tailWord_1144699, baseEnd_1144699] using wordTrace_append hprefix tailTrace_1144699
  have hstable : (prefixWord ++ tailWord_1144699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144699).length < 2 ^ (prefixWord ++ tailWord_1144699).sum := by decide
  have hdescent : baseEnd_1144699 < baseStart_1144699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144764 : List Nat := [2, 2, 2, 5, 1, 2, 7]
def baseStart_1144764 : Nat := 118140960795 + 1144764 * 2 ^ 59
def prefixEnd_1144764 : Nat := 4983230072969 + 3 ^ 40 * 1144764 * 2
def baseEnd_1144764 : Nat := 29027860146353794532609

theorem tailTrace_1144764 : CollatzResearch.WordTrace tailWord_1144764 prefixEnd_1144764 29027860146353794532609 := by
  unfold tailWord_1144764
  simp only [CollatzResearch.WordTrace]
  refine ⟨20876486612361506485476673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27835315483148675313968897 20876486612361506485476673)
  ·
    refine ⟨15657364959271129864107505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20876486612361506485476673 15657364959271129864107505)
    ·
      refine ⟨11743023719453347398080629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15657364959271129864107505 11743023719453347398080629)
      ·
        refine ⟨1100908473698751318570059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11743023719453347398080629 1100908473698751318570059)
        ·
          refine ⟨1651362710548126977855089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100908473698751318570059 1651362710548126977855089)
          ·
            refine ⟨1238522032911095233391317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1651362710548126977855089 1238522032911095233391317)
            ·
              refine ⟨29027860146353794532609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1238522032911095233391317 29027860146353794532609)
              ·
                rfl

theorem cell21_1144764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 7].length) (baseStart_1144764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144764 prefixEnd_1144764 := by exact prefixLift 1144764
  have htrace : WordTrace (prefixWord ++ tailWord_1144764) baseStart_1144764 baseEnd_1144764 := by
    simpa [prefixWord, tailWord_1144764, baseEnd_1144764] using wordTrace_append hprefix tailTrace_1144764
  have hstable : (prefixWord ++ tailWord_1144764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144764).length < 2 ^ (prefixWord ++ tailWord_1144764).sum := by decide
  have hdescent : baseEnd_1144764 < baseStart_1144764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144778 : List Nat := [3, 1, 2, 1, 2, 1, 2, 6, 3]
def baseStart_1144778 : Nat := 118140960795 + 1144778 * 2 ^ 59
def prefixEnd_1144778 : Nat := 4983230072969 + 3 ^ 40 * 1144778 * 2
def baseEnd_1144778 : Nat := 261253936307923237560119

theorem tailTrace_1144778 : CollatzResearch.WordTrace tailWord_1144778 prefixEnd_1144778 261253936307923237560119 := by
  unfold tailWord_1144778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10438370961668073340490747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27835655897781528907975325 10438370961668073340490747)
  ·
    refine ⟨15657556442502110010736121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10438370961668073340490747 15657556442502110010736121)
    ·
      refine ⟨11743167331876582508052091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15657556442502110010736121 11743167331876582508052091)
      ·
        refine ⟨17614750997814873762078137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11743167331876582508052091 17614750997814873762078137)
        ·
          refine ⟨13211063248361155321558603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17614750997814873762078137 13211063248361155321558603)
          ·
            refine ⟨19816594872541732982337905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13211063248361155321558603 19816594872541732982337905)
            ·
              refine ⟨14862446154406299736753429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19816594872541732982337905 14862446154406299736753429)
              ·
                refine ⟨696677163487795300160317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14862446154406299736753429 696677163487795300160317)
                ·
                  refine ⟨261253936307923237560119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696677163487795300160317 261253936307923237560119)
                  ·
                    rfl

theorem cell21_1144778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_1144778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144778 prefixEnd_1144778 := by exact prefixLift 1144778
  have htrace : WordTrace (prefixWord ++ tailWord_1144778) baseStart_1144778 baseEnd_1144778 := by
    simpa [prefixWord, tailWord_1144778, baseEnd_1144778] using wordTrace_append hprefix tailTrace_1144778
  have hstable : (prefixWord ++ tailWord_1144778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144778).length < 2 ^ (prefixWord ++ tailWord_1144778).sum := by decide
  have hdescent : baseEnd_1144778 < baseStart_1144778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144792 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_1144792 : Nat := 118140960795 + 1144792 * 2 ^ 59
def prefixEnd_1144792 : Nat := 4983230072969 + 3 ^ 40 * 1144792 * 2
def baseEnd_1144792 : Nat := 261257131298662324326757

theorem tailTrace_1144792 : CollatzResearch.WordTrace tailWord_1144792 prefixEnd_1144792 261257131298662324326757 := by
  unfold tailWord_1144792
  simp only [CollatzResearch.WordTrace]
  refine ⟨20876997234310786876486315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27835996312414382501981753 20876997234310786876486315)
  ·
    refine ⟨31315495851466180314729473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20876997234310786876486315 31315495851466180314729473)
    ·
      refine ⟨23486621888599635236047105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31315495851466180314729473 23486621888599635236047105)
      ·
        refine ⟨17614966416449726427035329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23486621888599635236047105 17614966416449726427035329)
        ·
          refine ⟨13211224812337294820276497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17614966416449726427035329 13211224812337294820276497)
          ·
            refine ⟨9908418609252971115207373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13211224812337294820276497 9908418609252971115207373)
            ·
              refine ⟨3715656978469864168202765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9908418609252971115207373 3715656978469864168202765)
              ·
                refine ⟨1393371366926199063076037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3715656978469864168202765 1393371366926199063076037)
                ·
                  refine ⟨261257131298662324326757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1393371366926199063076037 261257131298662324326757)
                  ·
                    rfl

theorem cell21_1144792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_1144792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144792 prefixEnd_1144792 := by exact prefixLift 1144792
  have htrace : WordTrace (prefixWord ++ tailWord_1144792) baseStart_1144792 baseEnd_1144792 := by
    simpa [prefixWord, tailWord_1144792, baseEnd_1144792] using wordTrace_append hprefix tailTrace_1144792
  have hstable : (prefixWord ++ tailWord_1144792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144792).length < 2 ^ (prefixWord ++ tailWord_1144792).sum := by decide
  have hdescent : baseEnd_1144792 < baseStart_1144792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144882 : List Nat := [3, 2, 1, 1, 2, 4, 8]
def baseStart_1144882 : Nat := 118140960795 + 1144882 * 2 ^ 59
def prefixEnd_1144882 : Nat := 4983230072969 + 3 ^ 40 * 1144882 * 2
def baseEnd_1144882 : Nat := 29030852280538018647397

theorem tailTrace_1144882 : CollatzResearch.WordTrace tailWord_1144882 prefixEnd_1144882 29030852280538018647397 := by
  unfold tailWord_1144882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10439319259573879780937225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27838184692197012749165933 10439319259573879780937225)
  ·
    refine ⟨7829489444680409835702919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10439319259573879780937225 7829489444680409835702919)
    ·
      refine ⟨11744234167020614753554379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7829489444680409835702919 11744234167020614753554379)
      ·
        refine ⟨17616351250530922130331569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11744234167020614753554379 17616351250530922130331569)
        ·
          refine ⟨13212263437898191597748677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17616351250530922130331569 13212263437898191597748677)
          ·
            refine ⟨2477299394605910924577877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13212263437898191597748677 2477299394605910924577877)
            ·
              refine ⟨29030852280538018647397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2477299394605910924577877 29030852280538018647397)
              ·
                rfl

theorem cell21_1144882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 8].length) (baseStart_1144882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144882 prefixEnd_1144882 := by exact prefixLift 1144882
  have htrace : WordTrace (prefixWord ++ tailWord_1144882) baseStart_1144882 baseEnd_1144882 := by
    simpa [prefixWord, tailWord_1144882, baseEnd_1144882] using wordTrace_append hprefix tailTrace_1144882
  have hstable : (prefixWord ++ tailWord_1144882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144882).length < 2 ^ (prefixWord ++ tailWord_1144882).sum := by decide
  have hdescent : baseEnd_1144882 < baseStart_1144882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144961 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 4]
def baseStart_1144961 : Nat := 118140960795 + 1144961 * 2 ^ 59
def prefixEnd_1144961 : Nat := 4983230072969 + 3 ^ 40 * 1144961 * 2
def baseEnd_1144961 : Nat := 261295699401155586009745

theorem tailTrace_1144961 : CollatzResearch.WordTrace tailWord_1144961 prefixEnd_1144961 261295699401155586009745 := by
  unfold tailWord_1144961
  simp only [CollatzResearch.WordTrace]
  refine ⟨41760158405009315615874737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27840105603339543743916491 41760158405009315615874737)
  ·
    refine ⟨31320118803756986711906053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41760158405009315615874737 31320118803756986711906053)
    ·
      refine ⟨5872522275704435008482385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31320118803756986711906053 5872522275704435008482385)
      ·
        refine ⟨4404391706778326256361789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5872522275704435008482385 4404391706778326256361789)
        ·
          refine ⟨1651646890041872346135671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4404391706778326256361789 1651646890041872346135671)
          ·
            refine ⟨2477470335062808519203507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651646890041872346135671 2477470335062808519203507)
            ·
              refine ⟨3716205502594212778805261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477470335062808519203507 3716205502594212778805261)
              ·
                refine ⟨1393577063472829792051973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3716205502594212778805261 1393577063472829792051973)
                ·
                  refine ⟨261295699401155586009745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1393577063472829792051973 261295699401155586009745)
                  ·
                    rfl

theorem cell21_1144961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_1144961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144961 prefixEnd_1144961 := by exact prefixLift 1144961
  have htrace : WordTrace (prefixWord ++ tailWord_1144961) baseStart_1144961 baseEnd_1144961 := by
    simpa [prefixWord, tailWord_1144961, baseEnd_1144961] using wordTrace_append hprefix tailTrace_1144961
  have hstable : (prefixWord ++ tailWord_1144961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144961).length < 2 ^ (prefixWord ++ tailWord_1144961).sum := by decide
  have hdescent : baseEnd_1144961 < baseStart_1144961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145169 : List Nat := [1, 2, 2, 1, 4, 11]
def baseStart_1145169 : Nat := 118140960795 + 1145169 * 2 ^ 59
def prefixEnd_1145169 : Nat := 4983230072969 + 3 ^ 40 * 1145169 * 2
def baseEnd_1145169 : Nat := 9679376586481238760839

theorem tailTrace_1145169 : CollatzResearch.WordTrace tailWord_1145169 prefixEnd_1145169 9679376586481238760839 := by
  unfold tailWord_1145169
  simp only [CollatzResearch.WordTrace]
  refine ⟨41767744788255767139446561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27845163192170511426297707 41767744788255767139446561)
  ·
    refine ⟨31325808591191825354584921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41767744788255767139446561 31325808591191825354584921)
    ·
      refine ⟨23494356443393869015938691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31325808591191825354584921 23494356443393869015938691)
      ·
        refine ⟨35241534665090803523908037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23494356443393869015938691 35241534665090803523908037)
        ·
          refine ⟨6607787749704525660732757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35241534665090803523908037 6607787749704525660732757)
          ·
            refine ⟨9679376586481238760839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6607787749704525660732757 9679376586481238760839)
            ·
              rfl

theorem cell21_1145169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 11].length) (baseStart_1145169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145169 prefixEnd_1145169 := by exact prefixLift 1145169
  have htrace : WordTrace (prefixWord ++ tailWord_1145169) baseStart_1145169 baseEnd_1145169 := by
    simpa [prefixWord, tailWord_1145169, baseEnd_1145169] using wordTrace_append hprefix tailTrace_1145169
  have hstable : (prefixWord ++ tailWord_1145169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145169).length < 2 ^ (prefixWord ++ tailWord_1145169).sum := by decide
  have hdescent : baseEnd_1145169 < baseStart_1145169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145172 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1145172 : Nat := 118140960795 + 1145172 * 2 ^ 59
def prefixEnd_1145172 : Nat := 4983230072969 + 3 ^ 40 * 1145172 * 2
def baseEnd_1145172 : Nat := 261343852475866107992647

theorem tailTrace_1145172 : CollatzResearch.WordTrace tailWord_1145172 prefixEnd_1145172 261343852475866107992647 := by
  unfold tailWord_1145172
  simp only [CollatzResearch.WordTrace]
  refine ⟨20883927103622449325902885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27845236138163265767870513 20883927103622449325902885)
  ·
    refine ⟨3915736331929209248606791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20883927103622449325902885 3915736331929209248606791)
    ·
      refine ⟨5873604497893813872910187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3915736331929209248606791 5873604497893813872910187)
      ·
        refine ⟨8810406746840720809365281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5873604497893813872910187 8810406746840720809365281)
        ·
          refine ⟨6607805060130540607023961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8810406746840720809365281 6607805060130540607023961)
          ·
            refine ⟨4955853795097905455267971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6607805060130540607023961 4955853795097905455267971)
            ·
              refine ⟨7433780692646858182901957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4955853795097905455267971 7433780692646858182901957)
              ·
                refine ⟨1393833879871285909294117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7433780692646858182901957 1393833879871285909294117)
                ·
                  refine ⟨261343852475866107992647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1393833879871285909294117 261343852475866107992647)
                  ·
                    rfl

theorem cell21_1145172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1145172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145172 prefixEnd_1145172 := by exact prefixLift 1145172
  have htrace : WordTrace (prefixWord ++ tailWord_1145172) baseStart_1145172 baseEnd_1145172 := by
    simpa [prefixWord, tailWord_1145172, baseEnd_1145172] using wordTrace_append hprefix tailTrace_1145172
  have hstable : (prefixWord ++ tailWord_1145172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145172).length < 2 ^ (prefixWord ++ tailWord_1145172).sum := by decide
  have hdescent : baseEnd_1145172 < baseStart_1145172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145200 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_1145200 : Nat := 118140960795 + 1145200 * 2 ^ 59
def prefixEnd_1145200 : Nat := 4983230072969 + 3 ^ 40 * 1145200 * 2
def baseEnd_1145200 : Nat := 261350242457344281525923

theorem tailTrace_1145200 : CollatzResearch.WordTrace tailWord_1145200 prefixEnd_1145200 261350242457344281525923 := by
  unfold tailWord_1145200
  simp only [CollatzResearch.WordTrace]
  refine ⟨20884437725571729716912527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27845916967428972955883369 20884437725571729716912527)
  ·
    refine ⟨31326656588357594575368791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20884437725571729716912527 31326656588357594575368791)
    ·
      refine ⟨46989984882536391863053187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31326656588357594575368791 46989984882536391863053187)
      ·
        refine ⟨70484977323804587794579781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46989984882536391863053187 70484977323804587794579781)
        ·
          refine ⟨13215933248213360211483709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70484977323804587794579781 13215933248213360211483709)
          ·
            refine ⟨4955974968080010079306391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13215933248213360211483709 4955974968080010079306391)
            ·
              refine ⟨7433962452120015118959587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4955974968080010079306391 7433962452120015118959587)
              ·
                refine ⟨11150943678180022678439381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7433962452120015118959587 11150943678180022678439381)
                ·
                  refine ⟨261350242457344281525923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11150943678180022678439381 261350242457344281525923)
                  ·
                    rfl

theorem cell21_1145200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_1145200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145200 prefixEnd_1145200 := by exact prefixLift 1145200
  have htrace : WordTrace (prefixWord ++ tailWord_1145200) baseStart_1145200 baseEnd_1145200 := by
    simpa [prefixWord, tailWord_1145200, baseEnd_1145200] using wordTrace_append hprefix tailTrace_1145200
  have hstable : (prefixWord ++ tailWord_1145200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145200).length < 2 ^ (prefixWord ++ tailWord_1145200).sum := by decide
  have hdescent : baseEnd_1145200 < baseStart_1145200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145352 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_1145352 : Nat := 118140960795 + 1145352 * 2 ^ 59
def prefixEnd_1145352 : Nat := 4983230072969 + 3 ^ 40 * 1145352 * 2
def baseEnd_1145352 : Nat := 261384930928225794992279

theorem tailTrace_1145352 : CollatzResearch.WordTrace tailWord_1145352 prefixEnd_1145352 261384930928225794992279 := by
  unfold tailWord_1145352
  simp only [CollatzResearch.WordTrace]
  refine ⟨20887209673296394696679155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27849612897728526262238873 20887209673296394696679155)
  ·
    refine ⟨31330814509944592045018733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20887209673296394696679155 31330814509944592045018733)
    ·
      refine ⟨11749055441229222016882025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31330814509944592045018733 11749055441229222016882025)
      ·
        refine ⟨8811791580921916512661519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11749055441229222016882025 8811791580921916512661519)
        ·
          refine ⟨13217687371382874768992279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8811791580921916512661519 13217687371382874768992279)
          ·
            refine ⟨19826531057074312153488419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13217687371382874768992279 19826531057074312153488419)
            ·
              refine ⟨29739796585611468230232629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19826531057074312153488419 29739796585611468230232629)
              ·
                refine ⟨2788105929901075146584309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29739796585611468230232629 2788105929901075146584309)
                ·
                  refine ⟨261384930928225794992279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2788105929901075146584309 261384930928225794992279)
                  ·
                    rfl

theorem cell21_1145352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_1145352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145352 prefixEnd_1145352 := by exact prefixLift 1145352
  have htrace : WordTrace (prefixWord ++ tailWord_1145352) baseStart_1145352 baseEnd_1145352 := by
    simpa [prefixWord, tailWord_1145352, baseEnd_1145352] using wordTrace_append hprefix tailTrace_1145352
  have hstable : (prefixWord ++ tailWord_1145352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145352).length < 2 ^ (prefixWord ++ tailWord_1145352).sum := by decide
  have hdescent : baseEnd_1145352 < baseStart_1145352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145386 : List Nat := [3, 1, 4, 1, 1, 2, 1, 5, 3]
def baseStart_1145386 : Nat := 118140960795 + 1145386 * 2 ^ 59
def prefixEnd_1145386 : Nat := 4983230072969 + 3 ^ 40 * 1145386 * 2
def baseEnd_1145386 : Nat := 261392690191449291425543

theorem tailTrace_1145386 : CollatzResearch.WordTrace tailWord_1145386 prefixEnd_1145386 261392690191449291425543 := by
  unfold tailWord_1145386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443914857117403300024003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27850439618979742133397341 10443914857117403300024003)
  ·
    refine ⟨15665872285676104950036005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10443914857117403300024003 15665872285676104950036005)
    ·
      refine ⟨2937351053564269678131751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15665872285676104950036005 2937351053564269678131751)
      ·
        refine ⟨4406026580346404517197627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937351053564269678131751 4406026580346404517197627)
        ·
          refine ⟨6609039870519606775796441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406026580346404517197627 6609039870519606775796441)
          ·
            refine ⟨4956779902889705081847331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6609039870519606775796441 4956779902889705081847331)
            ·
              refine ⟨7435169854334557622770997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4956779902889705081847331 7435169854334557622770997)
              ·
                refine ⟨697047173843864777134781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7435169854334557622770997 697047173843864777134781)
                ·
                  refine ⟨261392690191449291425543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697047173843864777134781 261392690191449291425543)
                  ·
                    rfl

theorem cell21_1145386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_1145386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145386 prefixEnd_1145386 := by exact prefixLift 1145386
  have htrace : WordTrace (prefixWord ++ tailWord_1145386) baseStart_1145386 baseEnd_1145386 := by
    simpa [prefixWord, tailWord_1145386, baseEnd_1145386] using wordTrace_append hprefix tailTrace_1145386
  have hstable : (prefixWord ++ tailWord_1145386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145386).length < 2 ^ (prefixWord ++ tailWord_1145386).sum := by decide
  have hdescent : baseEnd_1145386 < baseStart_1145386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145397 : List Nat := [1, 3, 3, 1, 1, 2, 10]
def baseStart_1145397 : Nat := 118140960795 + 1145397 * 2 ^ 59
def prefixEnd_1145397 : Nat := 4983230072969 + 3 ^ 40 * 1145397 * 2
def baseEnd_1145397 : Nat := 29043911171257301860243

theorem tailTrace_1145397 : CollatzResearch.WordTrace tailWord_1145397 prefixEnd_1145397 29043911171257301860243 := by
  unfold tailWord_1145397
  simp only [CollatzResearch.WordTrace]
  refine ⟨41776060631429762078746445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27850707087619841385830963 41776060631429762078746445)
  ·
    refine ⟨15666022736786160779529917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41776060631429762078746445 15666022736786160779529917)
    ·
      refine ⟨5874758526294810292323719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15666022736786160779529917 5874758526294810292323719)
      ·
        refine ⟨8812137789442215438485579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5874758526294810292323719 8812137789442215438485579)
        ·
          refine ⟨13218206684163323157728369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8812137789442215438485579 13218206684163323157728369)
          ·
            refine ⟨9913655013122492368296277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13218206684163323157728369 9913655013122492368296277)
            ·
              refine ⟨29043911171257301860243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9913655013122492368296277 29043911171257301860243)
              ·
                rfl

theorem cell21_1145397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 10].length) (baseStart_1145397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145397 prefixEnd_1145397 := by exact prefixLift 1145397
  have htrace : WordTrace (prefixWord ++ tailWord_1145397) baseStart_1145397 baseEnd_1145397 := by
    simpa [prefixWord, tailWord_1145397, baseEnd_1145397] using wordTrace_append hprefix tailTrace_1145397
  have hstable : (prefixWord ++ tailWord_1145397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145397).length < 2 ^ (prefixWord ++ tailWord_1145397).sum := by decide
  have hdescent : baseEnd_1145397 < baseStart_1145397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145476 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_1145476 : Nat := 118140960795 + 1145476 * 2 ^ 59
def prefixEnd_1145476 : Nat := 4983230072969 + 3 ^ 40 * 1145476 * 2
def baseEnd_1145476 : Nat := 261413229417629134925359

theorem tailTrace_1145476 : CollatzResearch.WordTrace tailWord_1145476 prefixEnd_1145476 261413229417629134925359 := by
  unfold tailWord_1145476
  simp only [CollatzResearch.WordTrace]
  refine ⟨20889470999071779285436141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27852627998762372380581521 20889470999071779285436141)
  ·
    refine ⟨7833551624651917232038553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20889470999071779285436141 7833551624651917232038553)
    ·
      refine ⟨5875163718488937924028915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7833551624651917232038553 5875163718488937924028915)
      ·
        refine ⟨8812745577733406886043373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5875163718488937924028915 8812745577733406886043373)
        ·
          refine ⟨3304779591650027582266265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8812745577733406886043373 3304779591650027582266265)
          ·
            refine ⟨2478584693737520686699699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3304779591650027582266265 2478584693737520686699699)
            ·
              refine ⟨3717877040606281030049549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478584693737520686699699 3717877040606281030049549)
              ·
                refine ⟨1394203890227355386268581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3717877040606281030049549 1394203890227355386268581)
                ·
                  refine ⟨261413229417629134925359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394203890227355386268581 261413229417629134925359)
                  ·
                    rfl

theorem cell21_1145476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_1145476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145476 prefixEnd_1145476 := by exact prefixLift 1145476
  have htrace : WordTrace (prefixWord ++ tailWord_1145476) baseStart_1145476 baseEnd_1145476 := by
    simpa [prefixWord, tailWord_1145476, baseEnd_1145476] using wordTrace_append hprefix tailTrace_1145476
  have hstable : (prefixWord ++ tailWord_1145476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145476).length < 2 ^ (prefixWord ++ tailWord_1145476).sum := by decide
  have hdescent : baseEnd_1145476 < baseStart_1145476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145490 : List Nat := [3, 2, 3, 1, 2, 1, 2, 7]
def baseStart_1145490 : Nat := 118140960795 + 1145490 * 2 ^ 59
def prefixEnd_1145490 : Nat := 4983230072969 + 3 ^ 40 * 1145490 * 2
def baseEnd_1145490 : Nat := 87138808136122740563999

theorem tailTrace_1145490 : CollatzResearch.WordTrace tailWord_1145490 prefixEnd_1145490 87138808136122740563999 := by
  unfold tailWord_1145490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10444863155023209740470481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27852968413395225974587949 10444863155023209740470481)
  ·
    refine ⟨7833647366267407305352861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10444863155023209740470481 7833647366267407305352861)
    ·
      refine ⟨2937617762350277739507323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7833647366267407305352861 2937617762350277739507323)
      ·
        refine ⟨4406426643525416609260985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937617762350277739507323 4406426643525416609260985)
        ·
          refine ⟨3304819982644062456945739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4406426643525416609260985 3304819982644062456945739)
          ·
            refine ⟨4957229973966093685418609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3304819982644062456945739 4957229973966093685418609)
            ·
              refine ⟨3717922480474570264063957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4957229973966093685418609 3717922480474570264063957)
              ·
                refine ⟨87138808136122740563999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3717922480474570264063957 87138808136122740563999)
                ·
                  rfl

theorem cell21_1145490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_1145490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145490 prefixEnd_1145490 := by exact prefixLift 1145490
  have htrace : WordTrace (prefixWord ++ tailWord_1145490) baseStart_1145490 baseEnd_1145490 := by
    simpa [prefixWord, tailWord_1145490, baseEnd_1145490] using wordTrace_append hprefix tailTrace_1145490
  have hstable : (prefixWord ++ tailWord_1145490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145490).length < 2 ^ (prefixWord ++ tailWord_1145490).sum := by decide
  have hdescent : baseEnd_1145490 < baseStart_1145490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145535 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 4]
def baseStart_1145535 : Nat := 118140960795 + 1145535 * 2 ^ 59
def prefixEnd_1145535 : Nat := 4983230072969 + 3 ^ 40 * 1145535 * 2
def baseEnd_1145535 : Nat := 261426694021458143441905

theorem tailTrace_1145535 : CollatzResearch.WordTrace tailWord_1145535 prefixEnd_1145535 261426694021458143441905 := by
  unfold tailWord_1145535
  simp only [CollatzResearch.WordTrace]
  refine ⟨41781093904929811647270059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27854062603286541098180039 41781093904929811647270059)
  ·
    refine ⟨62671640857394717470905089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41781093904929811647270059 62671640857394717470905089)
    ·
      refine ⟨47003730643046038103178817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62671640857394717470905089 47003730643046038103178817)
      ·
        refine ⟨35252797982284528577384113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47003730643046038103178817 35252797982284528577384113)
        ·
          refine ⟨26439598486713396433038085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35252797982284528577384113 26439598486713396433038085)
          ·
            refine ⟨4957424716258761831194641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26439598486713396433038085 4957424716258761831194641)
            ·
              refine ⟨3718068537194071373395981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4957424716258761831194641 3718068537194071373395981)
              ·
                refine ⟨1394275701447776765023493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3718068537194071373395981 1394275701447776765023493)
                ·
                  refine ⟨261426694021458143441905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394275701447776765023493 261426694021458143441905)
                  ·
                    rfl

theorem cell21_1145535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 4].length) (baseStart_1145535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145535 prefixEnd_1145535 := by exact prefixLift 1145535
  have htrace : WordTrace (prefixWord ++ tailWord_1145535) baseStart_1145535 baseEnd_1145535 := by
    simpa [prefixWord, tailWord_1145535, baseEnd_1145535] using wordTrace_append hprefix tailTrace_1145535
  have hstable : (prefixWord ++ tailWord_1145535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145535).length < 2 ^ (prefixWord ++ tailWord_1145535).sum := by decide
  have hdescent : baseEnd_1145535 < baseStart_1145535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145687 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 4]
def baseStart_1145687 : Nat := 118140960795 + 1145687 * 2 ^ 59
def prefixEnd_1145687 : Nat := 4983230072969 + 3 ^ 40 * 1145687 * 2
def baseEnd_1145687 : Nat := 261461382492339656908261

theorem tailTrace_1145687 : CollatzResearch.WordTrace tailWord_1145687 prefixEnd_1145687 261461382492339656908261 := by
  unfold tailWord_1145687
  simp only [CollatzResearch.WordTrace]
  refine ⟨41786637800379141606803315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27857758533586094404535543 41786637800379141606803315)
  ·
    refine ⟨62679956700568712410204973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41786637800379141606803315 62679956700568712410204973)
    ·
      refine ⟨23504983762713267153826865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62679956700568712410204973 23504983762713267153826865)
      ·
        refine ⟨17628737822034950365370149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23504983762713267153826865 17628737822034950365370149)
        ·
          refine ⟨3305388341631553193506903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17628737822034950365370149 3305388341631553193506903)
          ·
            refine ⟨4958082512447329790260355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305388341631553193506903 4958082512447329790260355)
            ·
              refine ⟨7437123768670994685390533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4958082512447329790260355 7437123768670994685390533)
              ·
                refine ⟨1394460706625811503510725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7437123768670994685390533 1394460706625811503510725)
                ·
                  refine ⟨261461382492339656908261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394460706625811503510725 261461382492339656908261)
                  ·
                    rfl

theorem cell21_1145687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 4].length) (baseStart_1145687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145687 prefixEnd_1145687 := by exact prefixLift 1145687
  have htrace : WordTrace (prefixWord ++ tailWord_1145687) baseStart_1145687 baseEnd_1145687 := by
    simpa [prefixWord, tailWord_1145687, baseEnd_1145687] using wordTrace_append hprefix tailTrace_1145687
  have hstable : (prefixWord ++ tailWord_1145687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145687).length < 2 ^ (prefixWord ++ tailWord_1145687).sum := by decide
  have hdescent : baseEnd_1145687 < baseStart_1145687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145690 : List Nat := [3, 1, 1, 2, 1, 4, 4, 2, 3]
def baseStart_1145690 : Nat := 118140960795 + 1145690 * 2 ^ 59
def prefixEnd_1145690 : Nat := 4983230072969 + 3 ^ 40 * 1145690 * 2
def baseEnd_1145690 : Nat := 261462067133212318358255

theorem tailTrace_1145690 : CollatzResearch.WordTrace tailWord_1145690 prefixEnd_1145690 261462067133212318358255 := by
  unfold tailWord_1145690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10446686804842068279790631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27857831479578848746108349 10446686804842068279790631)
  ·
    refine ⟨15670030207263102419685947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10446686804842068279790631 15670030207263102419685947)
    ·
      refine ⟨23505045310894653629528921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15670030207263102419685947 23505045310894653629528921)
      ·
        refine ⟨17628783983170990222146691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23505045310894653629528921 17628783983170990222146691)
        ·
          refine ⟨26443175974756485333220037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17628783983170990222146691 26443175974756485333220037)
          ·
            refine ⟨4958095495266840999978757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26443175974756485333220037 4958095495266840999978757)
            ·
              refine ⟨929642905362532687496017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4958095495266840999978757 929642905362532687496017)
              ·
                refine ⟨697232179021899515622013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929642905362532687496017 697232179021899515622013)
                ·
                  refine ⟨261462067133212318358255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697232179021899515622013 261462067133212318358255)
                  ·
                    rfl

theorem cell21_1145690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_1145690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145690 prefixEnd_1145690 := by exact prefixLift 1145690
  have htrace : WordTrace (prefixWord ++ tailWord_1145690) baseStart_1145690 baseEnd_1145690 := by
    simpa [prefixWord, tailWord_1145690, baseEnd_1145690] using wordTrace_append hprefix tailTrace_1145690
  have hstable : (prefixWord ++ tailWord_1145690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145690).length < 2 ^ (prefixWord ++ tailWord_1145690).sum := by decide
  have hdescent : baseEnd_1145690 < baseStart_1145690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145701 : List Nat := [1, 3, 1, 3, 1, 1, 5, 6]
def baseStart_1145701 : Nat := 118140960795 + 1145701 * 2 ^ 59
def prefixEnd_1145701 : Nat := 4983230072969 + 3 ^ 40 * 1145701 * 2
def baseEnd_1145701 : Nat := 87154859161026247891633

theorem tailTrace_1145701 : CollatzResearch.WordTrace tailWord_1145701 prefixEnd_1145701 87154859161026247891633 := by
  unfold tailWord_1145701
  simp only [CollatzResearch.WordTrace]
  refine ⟨41787148422328421997812957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27858098948218947998541971 41787148422328421997812957)
  ·
    refine ⟨15670180658373158249179859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41787148422328421997812957 15670180658373158249179859)
    ·
      refine ⟨23505270987559737373769789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15670180658373158249179859 23505270987559737373769789)
      ·
        refine ⟨8814476620334901515163671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23505270987559737373769789 8814476620334901515163671)
        ·
          refine ⟨13221714930502352272745507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8814476620334901515163671 13221714930502352272745507)
          ·
            refine ⟨19832572395753528409118261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13221714930502352272745507 19832572395753528409118261)
            ·
              refine ⟨1859303662101893288354837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19832572395753528409118261 1859303662101893288354837)
              ·
                refine ⟨87154859161026247891633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1859303662101893288354837 87154859161026247891633)
                ·
                  rfl

theorem cell21_1145701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 6].length) (baseStart_1145701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145701 prefixEnd_1145701 := by exact prefixLift 1145701
  have htrace : WordTrace (prefixWord ++ tailWord_1145701) baseStart_1145701 baseEnd_1145701 := by
    simpa [prefixWord, tailWord_1145701, baseEnd_1145701] using wordTrace_append hprefix tailTrace_1145701
  have hstable : (prefixWord ++ tailWord_1145701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145701).length < 2 ^ (prefixWord ++ tailWord_1145701).sum := by decide
  have hdescent : baseEnd_1145701 < baseStart_1145701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145715 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 7]
def baseStart_1145715 : Nat := 118140960795 + 1145715 * 2 ^ 59
def prefixEnd_1145715 : Nat := 4983230072969 + 3 ^ 40 * 1145715 * 2
def baseEnd_1145715 : Nat := 261467772473817830441537

theorem tailTrace_1145715 : CollatzResearch.WordTrace tailWord_1145715 prefixEnd_1145715 261467772473817830441537 := by
  unfold tailWord_1145715
  simp only [CollatzResearch.WordTrace]
  refine ⟨41787659044277702388822599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27858439362851801592548399 41787659044277702388822599)
  ·
    refine ⟨62681488566416553583233899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41787659044277702388822599 62681488566416553583233899)
    ·
      refine ⟨94022232849624830374850849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62681488566416553583233899 94022232849624830374850849)
      ·
        refine ⟨70516674637218622781138137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94022232849624830374850849 70516674637218622781138137)
        ·
          refine ⟨52887505977913967085853603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70516674637218622781138137 52887505977913967085853603)
          ·
            refine ⟨79331258966870950628780405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52887505977913967085853603 79331258966870950628780405)
            ·
              refine ⟨7437305528144151621448163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79331258966870950628780405 7437305528144151621448163)
              ·
                refine ⟨11155958292216227432172245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7437305528144151621448163 11155958292216227432172245)
                ·
                  refine ⟨261467772473817830441537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11155958292216227432172245 261467772473817830441537)
                  ·
                    rfl

theorem cell21_1145715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_1145715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145715 prefixEnd_1145715 := by exact prefixLift 1145715
  have htrace : WordTrace (prefixWord ++ tailWord_1145715) baseStart_1145715 baseEnd_1145715 := by
    simpa [prefixWord, tailWord_1145715, baseEnd_1145715] using wordTrace_append hprefix tailTrace_1145715
  have hstable : (prefixWord ++ tailWord_1145715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145715).length < 2 ^ (prefixWord ++ tailWord_1145715).sum := by decide
  have hdescent : baseEnd_1145715 < baseStart_1145715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145749 : List Nat := [1, 3, 2, 1, 1, 4, 2, 4, 3]
def baseStart_1145749 : Nat := 118140960795 + 1145749 * 2 ^ 59
def prefixEnd_1145749 : Nat := 4983230072969 + 3 ^ 40 * 1145749 * 2
def baseEnd_1145749 : Nat := 261475531737041326874801

theorem tailTrace_1145749 : CollatzResearch.WordTrace tailWord_1145749 prefixEnd_1145749 261475531737041326874801 := by
  unfold tailWord_1145749
  simp only [CollatzResearch.WordTrace]
  refine ⟨41788899126154526195560301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27859266084103017463706867 41788899126154526195560301)
  ·
    refine ⟨15670837172307947323335113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41788899126154526195560301 15670837172307947323335113)
    ·
      refine ⟨11753127879230960492501335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15670837172307947323335113 11753127879230960492501335)
      ·
        refine ⟨17629691818846440738752003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11753127879230960492501335 17629691818846440738752003)
        ·
          refine ⟨26444537728269661108128005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17629691818846440738752003 26444537728269661108128005)
          ·
            refine ⟨4958350824050561457774001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26444537728269661108128005 4958350824050561457774001)
            ·
              refine ⟨3718763118037921093330501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4958350824050561457774001 3718763118037921093330501)
              ·
                refine ⟨697268084632110204999469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3718763118037921093330501 697268084632110204999469)
                ·
                  refine ⟨261475531737041326874801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697268084632110204999469 261475531737041326874801)
                  ·
                    rfl

theorem cell21_1145749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_1145749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145749 prefixEnd_1145749 := by exact prefixLift 1145749
  have htrace : WordTrace (prefixWord ++ tailWord_1145749) baseStart_1145749 baseEnd_1145749 := by
    simpa [prefixWord, tailWord_1145749, baseEnd_1145749] using wordTrace_append hprefix tailTrace_1145749
  have hstable : (prefixWord ++ tailWord_1145749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145749).length < 2 ^ (prefixWord ++ tailWord_1145749).sum := by decide
  have hdescent : baseEnd_1145749 < baseStart_1145749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145780 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1145780 : Nat := 118140960795 + 1145780 * 2 ^ 59
def prefixEnd_1145780 : Nat := 4983230072969 + 3 ^ 40 * 1145780 * 2
def baseEnd_1145780 : Nat := 261482606359392161858071

theorem tailTrace_1145780 : CollatzResearch.WordTrace tailWord_1145780 prefixEnd_1145780 261482606359392161858071 := by
  unfold tailWord_1145780
  simp only [CollatzResearch.WordTrace]
  refine ⟨20895014894521109244969397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27860019859361478993292529 20895014894521109244969397)
  ·
    refine ⟨1958907646361353991715881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20895014894521109244969397 1958907646361353991715881)
    ·
      refine ⟨1469180734771015493786911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1958907646361353991715881 1469180734771015493786911)
      ·
        refine ⟨2203771102156523240680367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469180734771015493786911 2203771102156523240680367)
        ·
          refine ⟨3305656653234784861020551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2203771102156523240680367 3305656653234784861020551)
          ·
            refine ⟨4958484979852177291530827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305656653234784861020551 4958484979852177291530827)
            ·
              refine ⟨7437727469778265937296241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4958484979852177291530827 7437727469778265937296241)
              ·
                refine ⟨5578295602333699452972181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7437727469778265937296241 5578295602333699452972181)
                ·
                  refine ⟨261482606359392161858071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5578295602333699452972181 261482606359392161858071)
                  ·
                    rfl

theorem cell21_1145780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1145780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145780 prefixEnd_1145780 := by exact prefixLift 1145780
  have htrace : WordTrace (prefixWord ++ tailWord_1145780) baseStart_1145780 baseEnd_1145780 := by
    simpa [prefixWord, tailWord_1145780, baseEnd_1145780] using wordTrace_append hprefix tailTrace_1145780
  have hstable : (prefixWord ++ tailWord_1145780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145780).length < 2 ^ (prefixWord ++ tailWord_1145780).sum := by decide
  have hdescent : baseEnd_1145780 < baseStart_1145780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145814 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1145814 : Nat := 118140960795 + 1145814 * 2 ^ 59
def prefixEnd_1145814 : Nat := 4983230072969 + 3 ^ 40 * 1145814 * 2
def baseEnd_1145814 : Nat := 261490365622615658291335

theorem tailTrace_1145814 : CollatzResearch.WordTrace tailWord_1145814 prefixEnd_1145814 261490365622615658291335 := by
  unfold tailWord_1145814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2611954366932440143542281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27860846580612694864450997 2611954366932440143542281)
  ·
    refine ⟨1958965775199330107656711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2611954366932440143542281 1958965775199330107656711)
    ·
      refine ⟨2938448662798995161485067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1958965775199330107656711 2938448662798995161485067)
      ·
        refine ⟨4407672994198492742227601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2938448662798995161485067 4407672994198492742227601)
        ·
          refine ⟨3305754745648869556670701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4407672994198492742227601 3305754745648869556670701)
          ·
            refine ⟨1239658029618326083751513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3305754745648869556670701 1239658029618326083751513)
            ·
              refine ⟨929743522213744562813635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1239658029618326083751513 929743522213744562813635)
              ·
                refine ⟨1394615283320616844220453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929743522213744562813635 1394615283320616844220453)
                ·
                  refine ⟨261490365622615658291335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394615283320616844220453 261490365622615658291335)
                  ·
                    rfl

theorem cell21_1145814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1145814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145814 prefixEnd_1145814 := by exact prefixLift 1145814
  have htrace : WordTrace (prefixWord ++ tailWord_1145814) baseStart_1145814 baseEnd_1145814 := by
    simpa [prefixWord, tailWord_1145814, baseEnd_1145814] using wordTrace_append hprefix tailTrace_1145814
  have hstable : (prefixWord ++ tailWord_1145814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145814).length < 2 ^ (prefixWord ++ tailWord_1145814).sum := by decide
  have hdescent : baseEnd_1145814 < baseStart_1145814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145870 : List Nat := [4, 1, 1, 2, 2, 4, 1, 6]
def baseStart_1145870 : Nat := 118140960795 + 1145870 * 2 ^ 59
def prefixEnd_1145870 : Nat := 4983230072969 + 3 ^ 40 * 1145870 * 2
def baseEnd_1145870 : Nat := 87167715195190668452629

theorem tailTrace_1145870 : CollatzResearch.WordTrace tailWord_1145870 prefixEnd_1145870 87167715195190668452629 := by
  unfold tailWord_1145870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5224164044839520482589383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27862208239144109240476709 5224164044839520482589383)
  ·
    refine ⟨7836246067259280723884075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5224164044839520482589383 7836246067259280723884075)
    ·
      refine ⟨11754369100888921085826113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7836246067259280723884075 11754369100888921085826113)
      ·
        refine ⟨8815776825666690814369585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11754369100888921085826113 8815776825666690814369585)
        ·
          refine ⟨6611832619250018110777189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8815776825666690814369585 6611832619250018110777189)
          ·
            refine ⟨1239718616109378395770723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6611832619250018110777189 1239718616109378395770723)
            ·
              refine ⟨1859577924164067593656085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239718616109378395770723 1859577924164067593656085)
              ·
                refine ⟨87167715195190668452629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1859577924164067593656085 87167715195190668452629)
                ·
                  rfl

theorem cell21_1145870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_1145870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145870 prefixEnd_1145870 := by exact prefixLift 1145870
  have htrace : WordTrace (prefixWord ++ tailWord_1145870) baseStart_1145870 baseEnd_1145870 := by
    simpa [prefixWord, tailWord_1145870, baseEnd_1145870] using wordTrace_append hprefix tailTrace_1145870
  have hstable : (prefixWord ++ tailWord_1145870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145870).length < 2 ^ (prefixWord ++ tailWord_1145870).sum := by decide
  have hdescent : baseEnd_1145870 < baseStart_1145870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145918 : List Nat := [4, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_1145918 : Nat := 118140960795 + 1145918 * 2 ^ 59
def prefixEnd_1145918 : Nat := 4983230072969 + 3 ^ 40 * 1145918 * 2
def baseEnd_1145918 : Nat := 261514099839534588557789

theorem tailTrace_1145918 : CollatzResearch.WordTrace tailWord_1145918 prefixEnd_1145918 261514099839534588557789 := by
  unfold tailWord_1145918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5224382882817783507307801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27863375375028178705641605 5224382882817783507307801)
  ·
    refine ⟨3918287162113337630480851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5224382882817783507307801 3918287162113337630480851)
    ·
      refine ⟨5877430743170006445721277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3918287162113337630480851 5877430743170006445721277)
      ·
        refine ⟨2204036528688752417145479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5877430743170006445721277 2204036528688752417145479)
        ·
          refine ⟨3306054793033128625718219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204036528688752417145479 3306054793033128625718219)
          ·
            refine ⟨4959082189549692938577329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306054793033128625718219 4959082189549692938577329)
            ·
              refine ⟨3719311642162269703932997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4959082189549692938577329 3719311642162269703932997)
              ·
                refine ⟨697370932905425569487437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3719311642162269703932997 697370932905425569487437)
                ·
                  refine ⟨261514099839534588557789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697370932905425569487437 261514099839534588557789)
                  ·
                    rfl

theorem cell21_1145918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_1145918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145918 prefixEnd_1145918 := by exact prefixLift 1145918
  have htrace : WordTrace (prefixWord ++ tailWord_1145918) baseStart_1145918 baseEnd_1145918 := by
    simpa [prefixWord, tailWord_1145918, baseEnd_1145918] using wordTrace_append hprefix tailTrace_1145918
  have hstable : (prefixWord ++ tailWord_1145918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145918).length < 2 ^ (prefixWord ++ tailWord_1145918).sum := by decide
  have hdescent : baseEnd_1145918 < baseStart_1145918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145977 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 5]
def baseStart_1145977 : Nat := 118140960795 + 1145977 * 2 ^ 59
def prefixEnd_1145977 : Nat := 4983230072969 + 3 ^ 40 * 1145977 * 2
def baseEnd_1145977 : Nat := 261527564443363597074335

theorem tailTrace_1145977 : CollatzResearch.WordTrace tailWord_1145977 prefixEnd_1145977 261527564443363597074335 := by
  unfold tailWord_1145977
  simp only [CollatzResearch.WordTrace]
  refine ⟨41797214969328521134860185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27864809979552347423240123 41797214969328521134860185)
  ·
    refine ⟨31347911226996390851145139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41797214969328521134860185 31347911226996390851145139)
    ·
      refine ⟨47021866840494586276717709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31347911226996390851145139 47021866840494586276717709)
      ·
        refine ⟨17633200065185469853769141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47021866840494586276717709 17633200065185469853769141)
        ·
          refine ⟨1653112506111137798790857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17633200065185469853769141 1653112506111137798790857)
          ·
            refine ⟨1239834379583353349093143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1653112506111137798790857 1239834379583353349093143)
            ·
              refine ⟨1859751569375030023639715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239834379583353349093143 1859751569375030023639715)
              ·
                refine ⟨2789627354062545035459573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859751569375030023639715 2789627354062545035459573)
                ·
                  refine ⟨261527564443363597074335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2789627354062545035459573 261527564443363597074335)
                  ·
                    rfl

theorem cell21_1145977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_1145977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1145977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1145977 prefixEnd_1145977 := by exact prefixLift 1145977
  have htrace : WordTrace (prefixWord ++ tailWord_1145977) baseStart_1145977 baseEnd_1145977 := by
    simpa [prefixWord, tailWord_1145977, baseEnd_1145977] using wordTrace_append hprefix tailTrace_1145977
  have hstable : (prefixWord ++ tailWord_1145977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145977).length < 2 ^ (prefixWord ++ tailWord_1145977).sum := by decide
  have hdescent : baseEnd_1145977 < baseStart_1145977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146126 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_1146126 : Nat := 118140960795 + 1146126 * 2 ^ 59
def prefixEnd_1146126 : Nat := 4983230072969 + 3 ^ 40 * 1146126 * 2
def baseEnd_1146126 : Nat := 261561568273372449090697

theorem tailTrace_1146126 : CollatzResearch.WordTrace tailWord_1146126 prefixEnd_1146126 261561568273372449090697 := by
  unfold tailWord_1146126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225331180723589947754279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27868432963859146388022821 5225331180723589947754279)
  ·
    refine ⟨7837996771085384921631419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5225331180723589947754279 7837996771085384921631419)
    ·
      refine ⟨11756995156628077382447129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7837996771085384921631419 11756995156628077382447129)
      ·
        refine ⟨8817746367471058036835347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11756995156628077382447129 8817746367471058036835347)
        ·
          refine ⟨13226619551206587055253021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8817746367471058036835347 13226619551206587055253021)
          ·
            refine ⟨4959982331702470145719883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13226619551206587055253021 4959982331702470145719883)
            ·
              refine ⟨7439973497553705218579825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959982331702470145719883 7439973497553705218579825)
              ·
                refine ⟨5579980123165278913934869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7439973497553705218579825 5579980123165278913934869)
                ·
                  refine ⟨261561568273372449090697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5579980123165278913934869 261561568273372449090697)
                  ·
                    rfl

theorem cell21_1146126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_1146126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146126 prefixEnd_1146126 := by exact prefixLift 1146126
  have htrace : WordTrace (prefixWord ++ tailWord_1146126) baseStart_1146126 baseEnd_1146126 := by
    simpa [prefixWord, tailWord_1146126, baseEnd_1146126] using wordTrace_append hprefix tailTrace_1146126
  have hstable : (prefixWord ++ tailWord_1146126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146126).length < 2 ^ (prefixWord ++ tailWord_1146126).sum := by decide
  have hdescent : baseEnd_1146126 < baseStart_1146126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146140 : List Nat := [2, 2, 3, 1, 1, 1, 11]
def baseStart_1146140 : Nat := 118140960795 + 1146140 * 2 ^ 59
def prefixEnd_1146140 : Nat := 4983230072969 + 3 ^ 40 * 1146140 * 2
def baseEnd_1146140 : Nat := 29062751473790170650815

theorem tailTrace_1146140 : CollatzResearch.WordTrace tailWord_1146140 prefixEnd_1146140 29062751473790170650815 := by
  unfold tailWord_1146140
  simp only [CollatzResearch.WordTrace]
  refine ⟨20901580033868999986521937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27868773378491999982029249 20901580033868999986521937)
  ·
    refine ⟨15676185025401749989891453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20901580033868999986521937 15676185025401749989891453)
    ·
      refine ⟨5878569384525656246209295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15676185025401749989891453 5878569384525656246209295)
      ·
        refine ⟨8817854076788484369313943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5878569384525656246209295 8817854076788484369313943)
        ·
          refine ⟨13226781115182726553970915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8817854076788484369313943 13226781115182726553970915)
          ·
            refine ⟨19840171672774089830956373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13226781115182726553970915 19840171672774089830956373)
            ·
              refine ⟨29062751473790170650815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19840171672774089830956373 29062751473790170650815)
              ·
                rfl

theorem cell21_1146140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 11].length) (baseStart_1146140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146140 prefixEnd_1146140 := by exact prefixLift 1146140
  have htrace : WordTrace (prefixWord ++ tailWord_1146140) baseStart_1146140 baseEnd_1146140 := by
    simpa [prefixWord, tailWord_1146140, baseEnd_1146140] using wordTrace_append hprefix tailTrace_1146140
  have hstable : (prefixWord ++ tailWord_1146140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146140).length < 2 ^ (prefixWord ++ tailWord_1146140).sum := by decide
  have hdescent : baseEnd_1146140 < baseStart_1146140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146146 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1146146 : Nat := 118140960795 + 1146146 * 2 ^ 59
def prefixEnd_1146146 : Nat := 4983230072969 + 3 ^ 40 * 1146146 * 2
def baseEnd_1146146 : Nat := 261566132545856858757323

theorem tailTrace_1146146 : CollatzResearch.WordTrace tailWord_1146146 prefixEnd_1146146 261566132545856858757323 := by
  unfold tailWord_1146146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10450844726429065749440573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27868919270477508665174861 10450844726429065749440573)
  ·
    refine ⟨3919066772410899656040215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10450844726429065749440573 3919066772410899656040215)
    ·
      refine ⟨5878600158616349484060323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3919066772410899656040215 5878600158616349484060323)
      ·
        refine ⟨8817900237924524226090485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5878600158616349484060323 8817900237924524226090485)
        ·
          refine ⟨826678147305424146195983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8817900237924524226090485 826678147305424146195983)
          ·
            refine ⟨1240017220958136219293975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826678147305424146195983 1240017220958136219293975)
            ·
              refine ⟨1860025831437204328940963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240017220958136219293975 1860025831437204328940963)
              ·
                refine ⟨2790038747155806493411445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860025831437204328940963 2790038747155806493411445)
                ·
                  refine ⟨261566132545856858757323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2790038747155806493411445 261566132545856858757323)
                  ·
                    rfl

theorem cell21_1146146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1146146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146146 prefixEnd_1146146 := by exact prefixLift 1146146
  have htrace : WordTrace (prefixWord ++ tailWord_1146146) baseStart_1146146 baseEnd_1146146 := by
    simpa [prefixWord, tailWord_1146146, baseEnd_1146146] using wordTrace_append hprefix tailTrace_1146146
  have hstable : (prefixWord ++ tailWord_1146146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146146).length < 2 ^ (prefixWord ++ tailWord_1146146).sum := by decide
  have hdescent : baseEnd_1146146 < baseStart_1146146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146185 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 8]
def baseStart_1146185 : Nat := 118140960795 + 1146185 * 2 ^ 59
def prefixEnd_1146185 : Nat := 4983230072969 + 3 ^ 40 * 1146185 * 2
def baseEnd_1146185 : Nat := 261575032877201457607243

theorem tailTrace_1146185 : CollatzResearch.WordTrace tailWord_1146185 prefixEnd_1146185 261575032877201457607243 := by
  unfold tailWord_1146185
  simp only [CollatzResearch.WordTrace]
  refine ⟨41804801352574972658432009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27869867568383315105621339 41804801352574972658432009)
  ·
    refine ⟨31353601014431229493824007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41804801352574972658432009 31353601014431229493824007)
    ·
      refine ⟨47030401521646844240736011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31353601014431229493824007 47030401521646844240736011)
      ·
        refine ⟨70545602282470266361104017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47030401521646844240736011 70545602282470266361104017)
        ·
          refine ⟨52909201711852699770828013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70545602282470266361104017 52909201711852699770828013)
          ·
            refine ⟨19840950641944762414060505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52909201711852699770828013 19840950641944762414060505)
            ·
              refine ⟨14880712981458571810545379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19840950641944762414060505 14880712981458571810545379)
              ·
                refine ⟨22321069472187857715818069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14880712981458571810545379 22321069472187857715818069)
                ·
                  refine ⟨261575032877201457607243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22321069472187857715818069 261575032877201457607243)
                  ·
                    rfl

theorem cell21_1146185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_1146185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146185 prefixEnd_1146185 := by exact prefixLift 1146185
  have htrace : WordTrace (prefixWord ++ tailWord_1146185) baseStart_1146185 baseEnd_1146185 := by
    simpa [prefixWord, tailWord_1146185, baseEnd_1146185] using wordTrace_append hprefix tailTrace_1146185
  have hstable : (prefixWord ++ tailWord_1146185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146185).length < 2 ^ (prefixWord ++ tailWord_1146185).sum := by decide
  have hdescent : baseEnd_1146185 < baseStart_1146185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146202 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_1146202 : Nat := 118140960795 + 1146202 * 2 ^ 59
def prefixEnd_1146202 : Nat := 4983230072969 + 3 ^ 40 * 1146202 * 2
def baseEnd_1146202 : Nat := 261578912508813205823875

theorem tailTrace_1146202 : CollatzResearch.WordTrace tailWord_1146202 prefixEnd_1146202 261578912508813205823875 := by
  unfold tailWord_1146202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10451355348378346140450215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27870280929008923041200573 10451355348378346140450215)
  ·
    refine ⟨15677033022567519210675323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10451355348378346140450215 15677033022567519210675323)
    ·
      refine ⟨23515549533851278816012985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15677033022567519210675323 23515549533851278816012985)
      ·
        refine ⟨17636662150388459112009739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23515549533851278816012985 17636662150388459112009739)
        ·
          refine ⟨26454993225582688668014609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17636662150388459112009739 26454993225582688668014609)
          ·
            refine ⟨19841244919187016501010957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26454993225582688668014609 19841244919187016501010957)
            ·
              refine ⟨7440466844695131187879109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19841244919187016501010957 7440466844695131187879109)
              ·
                refine ⟨1395087533380337097727333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7440466844695131187879109 1395087533380337097727333)
                ·
                  refine ⟨261578912508813205823875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1395087533380337097727333 261578912508813205823875)
                  ·
                    rfl

theorem cell21_1146202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_1146202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146202 prefixEnd_1146202 := by exact prefixLift 1146202
  have htrace : WordTrace (prefixWord ++ tailWord_1146202) baseStart_1146202 baseEnd_1146202 := by
    simpa [prefixWord, tailWord_1146202, baseEnd_1146202] using wordTrace_append hprefix tailTrace_1146202
  have hstable : (prefixWord ++ tailWord_1146202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146202).length < 2 ^ (prefixWord ++ tailWord_1146202).sum := by decide
  have hdescent : baseEnd_1146202 < baseStart_1146202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146326 : List Nat := [5, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1146326 : Nat := 118140960795 + 1146326 * 2 ^ 59
def prefixEnd_1146326 : Nat := 4983230072969 + 3 ^ 40 * 1146326 * 2
def baseEnd_1146326 : Nat := 87202403666072181918985

theorem tailTrace_1146326 : CollatzResearch.WordTrace tailWord_1146326 prefixEnd_1146326 87202403666072181918985 := by
  unfold tailWord_1146326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613121502816509608707177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27873296030042769159543221 2613121502816509608707177)
  ·
    refine ⟨1959841127112382206530383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2613121502816509608707177 1959841127112382206530383)
    ·
      refine ⟨2939761690668573309795575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1959841127112382206530383 2939761690668573309795575)
      ·
        refine ⟨4409642536002859964693363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2939761690668573309795575 4409642536002859964693363)
        ·
          refine ⟨6614463804004289947040045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4409642536002859964693363 6614463804004289947040045)
          ·
            refine ⟨2480423926501608730140017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6614463804004289947040045 2480423926501608730140017)
            ·
              refine ⟨1860317944876206547605013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2480423926501608730140017 1860317944876206547605013)
              ·
                refine ⟨87202403666072181918985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1860317944876206547605013 87202403666072181918985)
                ·
                  rfl

theorem cell21_1146326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1146326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146326 prefixEnd_1146326 := by exact prefixLift 1146326
  have htrace : WordTrace (prefixWord ++ tailWord_1146326) baseStart_1146326 baseEnd_1146326 := by
    simpa [prefixWord, tailWord_1146326, baseEnd_1146326] using wordTrace_append hprefix tailTrace_1146326
  have hstable : (prefixWord ++ tailWord_1146326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146326).length < 2 ^ (prefixWord ++ tailWord_1146326).sum := by decide
  have hdescent : baseEnd_1146326 < baseStart_1146326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146478 : List Nat := [4, 1, 2, 2, 4, 1, 7]
def baseStart_1146478 : Nat := 118140960795 + 1146478 * 2 ^ 59
def prefixEnd_1146478 : Nat := 4983230072969 + 3 ^ 40 * 1146478 * 2
def baseEnd_1146478 : Nat := 29071322163233117691479

theorem tailTrace_1146478 : CollatzResearch.WordTrace tailWord_1146478 prefixEnd_1146478 29071322163233117691479 := by
  unfold tailWord_1146478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5226935992564185462356011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27876991960342322465898725 5226935992564185462356011)
  ·
    refine ⟨7840403988846278193534017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5226935992564185462356011 7840403988846278193534017)
    ·
      refine ⟨5880302991634708645150513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7840403988846278193534017 5880302991634708645150513)
      ·
        refine ⟨4410227243726031483862885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5880302991634708645150513 4410227243726031483862885)
        ·
          refine ⟨826917608198630903224291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4410227243726031483862885 826917608198630903224291)
          ·
            refine ⟨1240376412297946354836437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826917608198630903224291 1240376412297946354836437)
            ·
              refine ⟨29071322163233117691479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1240376412297946354836437 29071322163233117691479)
              ·
                rfl

theorem cell21_1146478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 7].length) (baseStart_1146478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146478 prefixEnd_1146478 := by exact prefixLift 1146478
  have htrace : WordTrace (prefixWord ++ tailWord_1146478) baseStart_1146478 baseEnd_1146478 := by
    simpa [prefixWord, tailWord_1146478, baseEnd_1146478] using wordTrace_append hprefix tailTrace_1146478
  have hstable : (prefixWord ++ tailWord_1146478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146478).length < 2 ^ (prefixWord ++ tailWord_1146478).sum := by decide
  have hdescent : baseEnd_1146478 < baseStart_1146478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146489 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 6]
def baseStart_1146489 : Nat := 118140960795 + 1146489 * 2 ^ 59
def prefixEnd_1146489 : Nat := 4983230072969 + 3 ^ 40 * 1146489 * 2
def baseEnd_1146489 : Nat := 261644409818964484539955

theorem tailTrace_1146489 : CollatzResearch.WordTrace tailWord_1146489 prefixEnd_1146489 261644409818964484539955 := by
  unfold tailWord_1146489
  simp only [CollatzResearch.WordTrace]
  refine ⟨41815889143473632577498521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27877259428982421718332347 41815889143473632577498521)
  ·
    refine ⟨31361916857605224433123891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41815889143473632577498521 31361916857605224433123891)
    ·
      refine ⟨47042875286407836649685837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31361916857605224433123891 47042875286407836649685837)
      ·
        refine ⟨17641078232402938743632189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47042875286407836649685837 17641078232402938743632189)
        ·
          refine ⟨6615404337151102028862071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17641078232402938743632189 6615404337151102028862071)
          ·
            refine ⟨9923106505726653043293107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6615404337151102028862071 9923106505726653043293107)
            ·
              refine ⟨14884659758589979564939661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9923106505726653043293107 14884659758589979564939661)
              ·
                refine ⟨5581747409471242336852373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14884659758589979564939661 5581747409471242336852373)
                ·
                  refine ⟨261644409818964484539955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5581747409471242336852373 261644409818964484539955)
                  ·
                    rfl

theorem cell21_1146489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_1146489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146489 prefixEnd_1146489 := by exact prefixLift 1146489
  have htrace : WordTrace (prefixWord ++ tailWord_1146489) baseStart_1146489 baseEnd_1146489 := by
    simpa [prefixWord, tailWord_1146489, baseEnd_1146489] using wordTrace_append hprefix tailTrace_1146489
  have hstable : (prefixWord ++ tailWord_1146489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146489).length < 2 ^ (prefixWord ++ tailWord_1146489).sum := by decide
  have hdescent : baseEnd_1146489 < baseStart_1146489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146520 : List Nat := [2, 1, 2, 4, 1, 2, 2, 7]
def baseStart_1146520 : Nat := 118140960795 + 1146520 * 2 ^ 59
def prefixEnd_1146520 : Nat := 4983230072969 + 3 ^ 40 * 1146520 * 2
def baseEnd_1146520 : Nat := 87217161480438439841075

theorem tailTrace_1146520 : CollatzResearch.WordTrace tailWord_1146520 prefixEnd_1146520 87217161480438439841075 := by
  unfold tailWord_1146520
  simp only [CollatzResearch.WordTrace]
  refine ⟨20908509903180662435938507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27878013204240883247918009 20908509903180662435938507)
  ·
    refine ⟨31362764854770993653907761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20908509903180662435938507 31362764854770993653907761)
    ·
      refine ⟨23522073641078245240430821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31362764854770993653907761 23522073641078245240430821)
      ·
        refine ⟨4410388807702170982580779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23522073641078245240430821 4410388807702170982580779)
        ·
          refine ⟨6615583211553256473871169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4410388807702170982580779 6615583211553256473871169)
          ·
            refine ⟨4961687408664942355403377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6615583211553256473871169 4961687408664942355403377)
            ·
              refine ⟨3721265556498706766552533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4961687408664942355403377 3721265556498706766552533)
              ·
                refine ⟨87217161480438439841075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3721265556498706766552533 87217161480438439841075)
                ·
                  rfl

theorem cell21_1146520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_1146520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146520 prefixEnd_1146520 := by exact prefixLift 1146520
  have htrace : WordTrace (prefixWord ++ tailWord_1146520) baseStart_1146520 baseEnd_1146520 := by
    simpa [prefixWord, tailWord_1146520, baseEnd_1146520] using wordTrace_append hprefix tailTrace_1146520
  have hstable : (prefixWord ++ tailWord_1146520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146520).length < 2 ^ (prefixWord ++ tailWord_1146520).sum := by decide
  have hdescent : baseEnd_1146520 < baseStart_1146520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146599 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 6]
def baseStart_1146599 : Nat := 118140960795 + 1146599 * 2 ^ 59
def prefixEnd_1146599 : Nat := 4983230072969 + 3 ^ 40 * 1146599 * 2
def baseEnd_1146599 : Nat := 261669513317628737706397

theorem tailTrace_1146599 : CollatzResearch.WordTrace tailWord_1146599 prefixEnd_1146599 261669513317628737706397 := by
  unfold tailWord_1146599
  simp only [CollatzResearch.WordTrace]
  refine ⟨41819901173075121364002851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27879934115383414242668567 41819901173075121364002851)
  ·
    refine ⟨62729851759612682046004277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41819901173075121364002851 62729851759612682046004277)
    ·
      refine ⟨5880923602463688941812901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62729851759612682046004277 5880923602463688941812901)
      ·
        refine ⟨1102673175461941676589919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5880923602463688941812901 1102673175461941676589919)
        ·
          refine ⟨1654009763192912514884879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102673175461941676589919 1654009763192912514884879)
          ·
            refine ⟨2481014644789368772327319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1654009763192912514884879 2481014644789368772327319)
            ·
              refine ⟨3721521967184053158490979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481014644789368772327319 3721521967184053158490979)
              ·
                refine ⟨5582282950776079737736469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3721521967184053158490979 5582282950776079737736469)
                ·
                  refine ⟨261669513317628737706397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5582282950776079737736469 261669513317628737706397)
                  ·
                    rfl

theorem cell21_1146599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 6].length) (baseStart_1146599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146599 prefixEnd_1146599 := by exact prefixLift 1146599
  have htrace : WordTrace (prefixWord ++ tailWord_1146599) baseStart_1146599 baseEnd_1146599 := by
    simpa [prefixWord, tailWord_1146599, baseEnd_1146599] using wordTrace_append hprefix tailTrace_1146599
  have hstable : (prefixWord ++ tailWord_1146599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146599).length < 2 ^ (prefixWord ++ tailWord_1146599).sum := by decide
  have hdescent : baseEnd_1146599 < baseStart_1146599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146658 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1146658 : Nat := 118140960795 + 1146658 * 2 ^ 59
def prefixEnd_1146658 : Nat := 4983230072969 + 3 ^ 40 * 1146658 * 2
def baseEnd_1146658 : Nat := 261682977921457746222943

theorem tailTrace_1146658 : CollatzResearch.WordTrace tailWord_1146658 prefixEnd_1146658 261682977921457746222943 := by
  unfold tailWord_1146658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10455513269965343610100157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27881368719907582960267085 10455513269965343610100157)
  ·
    refine ⟨3920817476237003853787559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10455513269965343610100157 3920817476237003853787559)
    ·
      refine ⟨5881226214355505780681339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3920817476237003853787559 5881226214355505780681339)
      ·
        refine ⟨8821839321533258671022009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5881226214355505780681339 8821839321533258671022009)
        ·
          refine ⟨6616379491149944003266507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8821839321533258671022009 6616379491149944003266507)
          ·
            refine ⟨9924569236724916004899761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6616379491149944003266507 9924569236724916004899761)
            ·
              refine ⟨7443426927543687003674821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9924569236724916004899761 7443426927543687003674821)
              ·
                refine ⟨1395642548914441313189029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7443426927543687003674821 1395642548914441313189029)
                ·
                  refine ⟨261682977921457746222943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1395642548914441313189029 261682977921457746222943)
                  ·
                    rfl

theorem cell21_1146658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1146658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146658 prefixEnd_1146658 := by exact prefixLift 1146658
  have htrace : WordTrace (prefixWord ++ tailWord_1146658) baseStart_1146658 baseEnd_1146658 := by
    simpa [prefixWord, tailWord_1146658, baseEnd_1146658] using wordTrace_append hprefix tailTrace_1146658
  have hstable : (prefixWord ++ tailWord_1146658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146658).length < 2 ^ (prefixWord ++ tailWord_1146658).sum := by decide
  have hdescent : baseEnd_1146658 < baseStart_1146658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146661 : List Nat := [1, 3, 1, 2, 3, 3, 3, 2, 3]
def baseStart_1146661 : Nat := 118140960795 + 1146661 * 2 ^ 59
def prefixEnd_1146661 : Nat := 4983230072969 + 3 ^ 40 * 1146661 * 2
def baseEnd_1146661 : Nat := 261683662562330407672937

theorem tailTrace_1146661 : CollatzResearch.WordTrace tailWord_1146661 prefixEnd_1146661 261683662562330407672937 := by
  unfold tailWord_1146661
  simp only [CollatzResearch.WordTrace]
  refine ⟨41822162498850505952759837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27881441665900337301839891 41822162498850505952759837)
  ·
    refine ⟨15683310937068939732284939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41822162498850505952759837 15683310937068939732284939)
    ·
      refine ⟨23524966405603409598427409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15683310937068939732284939 23524966405603409598427409)
      ·
        refine ⟨17643724804202557198820557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23524966405603409598427409 17643724804202557198820557)
        ·
          refine ⟨6616396801575958949557709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17643724804202557198820557 6616396801575958949557709)
          ·
            refine ⟨2481148800590984606084141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6616396801575958949557709 2481148800590984606084141)
            ·
              refine ⟨930430800221619227281553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2481148800590984606084141 930430800221619227281553)
              ·
                refine ⟨697823100166214420461165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930430800221619227281553 697823100166214420461165)
                ·
                  refine ⟨261683662562330407672937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697823100166214420461165 261683662562330407672937)
                  ·
                    rfl

theorem cell21_1146661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_1146661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146661 prefixEnd_1146661 := by exact prefixLift 1146661
  have htrace : WordTrace (prefixWord ++ tailWord_1146661) baseStart_1146661 baseEnd_1146661 := by
    simpa [prefixWord, tailWord_1146661, baseEnd_1146661] using wordTrace_append hprefix tailTrace_1146661
  have hstable : (prefixWord ++ tailWord_1146661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146661).length < 2 ^ (prefixWord ++ tailWord_1146661).sum := by decide
  have hdescent : baseEnd_1146661 < baseStart_1146661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146720 : List Nat := [2, 1, 1, 3, 3, 3, 1, 4, 3]
def baseStart_1146720 : Nat := 118140960795 + 1146720 * 2 ^ 59
def prefixEnd_1146720 : Nat := 4983230072969 + 3 ^ 40 * 1146720 * 2
def baseEnd_1146720 : Nat := 261697127166159416189483

theorem tailTrace_1146720 : CollatzResearch.WordTrace tailWord_1146720 prefixEnd_1146720 261697127166159416189483 := by
  unfold tailWord_1146720
  simp only [CollatzResearch.WordTrace]
  refine ⟨20912157202818379514578807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27882876270424506019438409 20912157202818379514578807)
  ·
    refine ⟨31368235804227569271868211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20912157202818379514578807 31368235804227569271868211)
    ·
      refine ⟨47052353706341353907802317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31368235804227569271868211 47052353706341353907802317)
      ·
        refine ⟨17644632639878007715425869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47052353706341353907802317 17644632639878007715425869)
        ·
          refine ⟨6616737239954252893284701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17644632639878007715425869 6616737239954252893284701)
          ·
            refine ⟨2481276464982844834981763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6616737239954252893284701 2481276464982844834981763)
            ·
              refine ⟨3721914697474267252472645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481276464982844834981763 3721914697474267252472645)
              ·
                refine ⟨697859005776425109838621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3721914697474267252472645 697859005776425109838621)
                ·
                  refine ⟨261697127166159416189483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697859005776425109838621 261697127166159416189483)
                  ·
                    rfl

theorem cell21_1146720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 3].length) (baseStart_1146720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146720 prefixEnd_1146720 := by exact prefixLift 1146720
  have htrace : WordTrace (prefixWord ++ tailWord_1146720) baseStart_1146720 baseEnd_1146720 := by
    simpa [prefixWord, tailWord_1146720, baseEnd_1146720] using wordTrace_append hprefix tailTrace_1146720
  have hstable : (prefixWord ++ tailWord_1146720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146720).length < 2 ^ (prefixWord ++ tailWord_1146720).sum := by decide
  have hdescent : baseEnd_1146720 < baseStart_1146720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146813 : List Nat := [1, 4, 1, 2, 3, 3, 1, 3, 3]
def baseStart_1146813 : Nat := 118140960795 + 1146813 * 2 ^ 59
def prefixEnd_1146813 : Nat := 4983230072969 + 3 ^ 40 * 1146813 * 2
def baseEnd_1146813 : Nat := 261718351033211921139293

theorem tailTrace_1146813 : CollatzResearch.WordTrace tailWord_1146813 prefixEnd_1146813 261718351033211921139293 := by
  unfold tailWord_1146813
  simp only [CollatzResearch.WordTrace]
  refine ⟨41827706394299835912293093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27885137596199890608195395 41827706394299835912293093)
  ·
    refine ⟨7842694948931219233554955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41827706394299835912293093 7842694948931219233554955)
    ·
      refine ⟨11764042423396828850332433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7842694948931219233554955 11764042423396828850332433)
      ·
        refine ⟨8823031817547621637749325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11764042423396828850332433 8823031817547621637749325)
        ·
          refine ⟨3308636931580358114155997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8823031817547621637749325 3308636931580358114155997)
          ·
            refine ⟨1240738849342634292808499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3308636931580358114155997 1240738849342634292808499)
            ·
              refine ⟨1861108274013951439212749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240738849342634292808499 1861108274013951439212749)
              ·
                refine ⟨697915602755231789704781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1861108274013951439212749 697915602755231789704781)
                ·
                  refine ⟨261718351033211921139293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697915602755231789704781 261718351033211921139293)
                  ·
                    rfl

theorem cell21_1146813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_1146813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146813 prefixEnd_1146813 := by exact prefixLift 1146813
  have htrace : WordTrace (prefixWord ++ tailWord_1146813) baseStart_1146813 baseEnd_1146813 := by
    simpa [prefixWord, tailWord_1146813, baseEnd_1146813] using wordTrace_append hprefix tailTrace_1146813
  have hstable : (prefixWord ++ tailWord_1146813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146813).length < 2 ^ (prefixWord ++ tailWord_1146813).sum := by decide
  have hdescent : baseEnd_1146813 < baseStart_1146813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146824 : List Nat := [2, 1, 3, 1, 4, 3, 7]
def baseStart_1146824 : Nat := 118140960795 + 1146824 * 2 ^ 59
def prefixEnd_1146824 : Nat := 4983230072969 + 3 ^ 40 * 1146824 * 2
def baseEnd_1146824 : Nat := 29080095709230927383993

theorem tailTrace_1146824 : CollatzResearch.WordTrace tailWord_1146824 prefixEnd_1146824 29080095709230927383993 := by
  unfold tailWord_1146824
  simp only [CollatzResearch.WordTrace]
  refine ⟨20914053798629992395471763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27885405064839989860629017 20914053798629992395471763)
  ·
    refine ⟨31371080697944988593207645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20914053798629992395471763 31371080697944988593207645)
    ·
      refine ⟨11764155261729370722452867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31371080697944988593207645 11764155261729370722452867)
      ·
        refine ⟨17646232892594056083679301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11764155261729370722452867 17646232892594056083679301)
        ·
          refine ⟨3308668667361385515689869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17646232892594056083679301 3308668667361385515689869)
          ·
            refine ⟨1240750750260519568383701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3308668667361385515689869 1240750750260519568383701)
            ·
              refine ⟨29080095709230927383993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1240750750260519568383701 29080095709230927383993)
              ·
                rfl

theorem cell21_1146824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 7].length) (baseStart_1146824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146824 prefixEnd_1146824 := by exact prefixLift 1146824
  have htrace : WordTrace (prefixWord ++ tailWord_1146824) baseStart_1146824 baseEnd_1146824 := by
    simpa [prefixWord, tailWord_1146824, baseEnd_1146824] using wordTrace_append hprefix tailTrace_1146824
  have hstable : (prefixWord ++ tailWord_1146824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146824).length < 2 ^ (prefixWord ++ tailWord_1146824).sum := by decide
  have hdescent : baseEnd_1146824 < baseStart_1146824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146931 : List Nat := [1, 1, 1, 2, 4, 1, 3, 5, 3]
def baseStart_1146931 : Nat := 118140960795 + 1146931 * 2 ^ 59
def prefixEnd_1146931 : Nat := 4983230072969 + 3 ^ 40 * 1146931 * 2
def baseEnd_1146931 : Nat := 261745280240869938172385

theorem tailTrace_1146931 : CollatzResearch.WordTrace tailWord_1146931 prefixEnd_1146931 261745280240869938172385 := by
  unfold tailWord_1146931
  simp only [CollatzResearch.WordTrace]
  refine ⟨41832010207872342065088647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27888006805248228043392431 41832010207872342065088647)
  ·
    refine ⟨62748015311808513097632971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41832010207872342065088647 62748015311808513097632971)
    ·
      refine ⟨94122022967712769646449457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62748015311808513097632971 94122022967712769646449457)
      ·
        refine ⟨70591517225784577234837093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94122022967712769646449457 70591517225784577234837093)
        ·
          refine ⟨13235909479834608231531955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70591517225784577234837093 13235909479834608231531955)
          ·
            refine ⟨19853864219751912347297933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13235909479834608231531955 19853864219751912347297933)
            ·
              refine ⟨7445199082406967130236725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19853864219751912347297933 7445199082406967130236725)
              ·
                refine ⟨697987413975653168459693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7445199082406967130236725 697987413975653168459693)
                ·
                  refine ⟨261745280240869938172385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697987413975653168459693 261745280240869938172385)
                  ·
                    rfl

theorem cell21_1146931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 3].length) (baseStart_1146931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146931 prefixEnd_1146931 := by exact prefixLift 1146931
  have htrace : WordTrace (prefixWord ++ tailWord_1146931) baseStart_1146931 baseEnd_1146931 := by
    simpa [prefixWord, tailWord_1146931, baseEnd_1146931] using wordTrace_append hprefix tailTrace_1146931
  have hstable : (prefixWord ++ tailWord_1146931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146931).length < 2 ^ (prefixWord ++ tailWord_1146931).sum := by decide
  have hdescent : baseEnd_1146931 < baseStart_1146931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146976 : List Nat := [2, 1, 1, 3, 2, 3, 4, 5]
def baseStart_1146976 : Nat := 118140960795 + 1146976 * 2 ^ 59
def prefixEnd_1146976 : Nat := 4983230072969 + 3 ^ 40 * 1146976 * 2
def baseEnd_1146976 : Nat := 87251849951319953307431

theorem tailTrace_1146976 : CollatzResearch.WordTrace tailWord_1146976 prefixEnd_1146976 87251849951319953307431 := by
  unfold tailWord_1146976
  simp only [CollatzResearch.WordTrace]
  refine ⟨20916825746354657375238391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27889100995139543166984521 20916825746354657375238391)
  ·
    refine ⟨31375238619531986062857587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20916825746354657375238391 31375238619531986062857587)
    ·
      refine ⟨47062857929297979094286381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31375238619531986062857587 47062857929297979094286381)
      ·
        refine ⟨17648571723486742160357393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47062857929297979094286381 17648571723486742160357393)
        ·
          refine ⟨13236428792615056620268045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17648571723486742160357393 13236428792615056620268045)
          ·
            refine ⟨4963660797230646232600517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13236428792615056620268045 4963660797230646232600517)
            ·
              refine ⟨930686399480746168612597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4963660797230646232600517 930686399480746168612597)
              ·
                refine ⟨87251849951319953307431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 930686399480746168612597 87251849951319953307431)
                ·
                  rfl

theorem cell21_1146976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_1146976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1146976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1146976 prefixEnd_1146976 := by exact prefixLift 1146976
  have htrace : WordTrace (prefixWord ++ tailWord_1146976) baseStart_1146976 baseEnd_1146976 := by
    simpa [prefixWord, tailWord_1146976, baseEnd_1146976] using wordTrace_append hprefix tailTrace_1146976
  have hstable : (prefixWord ++ tailWord_1146976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146976).length < 2 ^ (prefixWord ++ tailWord_1146976).sum := by decide
  have hdescent : baseEnd_1146976 < baseStart_1146976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147080 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_1147080 : Nat := 118140960795 + 1147080 * 2 ^ 59
def prefixEnd_1147080 : Nat := 4983230072969 + 3 ^ 40 * 1147080 * 2
def baseEnd_1147080 : Nat := 261779284070878790188747

theorem tailTrace_1147080 : CollatzResearch.WordTrace tailWord_1147080 prefixEnd_1147080 261779284070878790188747 := by
  unfold tailWord_1147080
  simp only [CollatzResearch.WordTrace]
  refine ⟨20918722342166270256131347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27891629789555027008175129 20918722342166270256131347)
  ·
    refine ⟨31378083513249405384197021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20918722342166270256131347 31378083513249405384197021)
    ·
      refine ⟨11766781317468527019073883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31378083513249405384197021 11766781317468527019073883)
      ·
        refine ⟨17650171976202790528610825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11766781317468527019073883 17650171976202790528610825)
        ·
          refine ⟨13237628982152092896458119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17650171976202790528610825 13237628982152092896458119)
          ·
            refine ⟨19856443473228139344687179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13237628982152092896458119 19856443473228139344687179)
            ·
              refine ⟨29784665209842209017030769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19856443473228139344687179 29784665209842209017030769)
              ·
                refine ⟨22338498907381656762773077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29784665209842209017030769 22338498907381656762773077)
                ·
                  refine ⟨261779284070878790188747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22338498907381656762773077 261779284070878790188747)
                  ·
                    rfl

theorem cell21_1147080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_1147080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147080 prefixEnd_1147080 := by exact prefixLift 1147080
  have htrace : WordTrace (prefixWord ++ tailWord_1147080) baseStart_1147080 baseEnd_1147080 := by
    simpa [prefixWord, tailWord_1147080, baseEnd_1147080] using wordTrace_append hprefix tailTrace_1147080
  have hstable : (prefixWord ++ tailWord_1147080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147080).length < 2 ^ (prefixWord ++ tailWord_1147080).sum := by decide
  have hdescent : baseEnd_1147080 < baseStart_1147080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147106 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 4]
def baseStart_1147106 : Nat := 118140960795 + 1147106 * 2 ^ 59
def prefixEnd_1147106 : Nat := 4983230072969 + 3 ^ 40 * 1147106 * 2
def baseEnd_1147106 : Nat := 261785217625108522755361

theorem tailTrace_1147106 : CollatzResearch.WordTrace tailWord_1147106 prefixEnd_1147106 261785217625108522755361 := by
  unfold tailWord_1147106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10459598245559586738177293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27892261988158897968472781 10459598245559586738177293)
  ·
    refine ⟨3922349342084845026816485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10459598245559586738177293 3922349342084845026816485)
    ·
      refine ⟨735440501640908442528091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3922349342084845026816485 735440501640908442528091)
      ·
        refine ⟨1103160752461362663792137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735440501640908442528091 1103160752461362663792137)
        ·
          refine ⟨827370564346021997844103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103160752461362663792137 827370564346021997844103)
          ·
            refine ⟨1241055846519032996766155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827370564346021997844103 1241055846519032996766155)
            ·
              refine ⟨1861583769778549495149233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241055846519032996766155 1861583769778549495149233)
              ·
                refine ⟨1396187827333912121361925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1861583769778549495149233 1396187827333912121361925)
                ·
                  refine ⟨261785217625108522755361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1396187827333912121361925 261785217625108522755361)
                  ·
                    rfl

theorem cell21_1147106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_1147106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147106 prefixEnd_1147106 := by exact prefixLift 1147106
  have htrace : WordTrace (prefixWord ++ tailWord_1147106) baseStart_1147106 baseEnd_1147106 := by
    simpa [prefixWord, tailWord_1147106, baseEnd_1147106] using wordTrace_append hprefix tailTrace_1147106
  have hstable : (prefixWord ++ tailWord_1147106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147106).length < 2 ^ (prefixWord ++ tailWord_1147106).sum := by decide
  have hdescent : baseEnd_1147106 < baseStart_1147106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147176 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 5]
def baseStart_1147176 : Nat := 118140960795 + 1147176 * 2 ^ 59
def prefixEnd_1147176 : Nat := 4983230072969 + 3 ^ 40 * 1147176 * 2
def baseEnd_1147176 : Nat := 261801192578803956588551

theorem tailTrace_1147176 : CollatzResearch.WordTrace tailWord_1147176 prefixEnd_1147176 261801192578803956588551 := by
  unfold tailWord_1147176
  simp only [CollatzResearch.WordTrace]
  refine ⟨20920473045992374453878691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27893964061323165938504921 20920473045992374453878691)
  ·
    refine ⟨31380709568988561680818037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20920473045992374453878691 31380709568988561680818037)
    ·
      refine ⟨2941941522092677657576691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31380709568988561680818037 2941941522092677657576691)
      ·
        refine ⟨4412912283139016486365037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2941941522092677657576691 4412912283139016486365037)
        ·
          refine ⟨1654842106177131182386889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4412912283139016486365037 1654842106177131182386889)
          ·
            refine ⟨1241131579632848386790167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1654842106177131182386889 1241131579632848386790167)
            ·
              refine ⟨1861697369449272580185251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241131579632848386790167 1861697369449272580185251)
              ·
                refine ⟨2792546054173908870277877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861697369449272580185251 2792546054173908870277877)
                ·
                  refine ⟨261801192578803956588551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2792546054173908870277877 261801192578803956588551)
                  ·
                    rfl

theorem cell21_1147176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_1147176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147176 prefixEnd_1147176 := by exact prefixLift 1147176
  have htrace : WordTrace (prefixWord ++ tailWord_1147176) baseStart_1147176 baseEnd_1147176 := by
    simpa [prefixWord, tailWord_1147176, baseEnd_1147176] using wordTrace_append hprefix tailTrace_1147176
  have hstable : (prefixWord ++ tailWord_1147176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147176).length < 2 ^ (prefixWord ++ tailWord_1147176).sum := by decide
  have hdescent : baseEnd_1147176 < baseStart_1147176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147187 : List Nat := [1, 1, 1, 2, 5, 1, 4, 6]
def baseStart_1147187 : Nat := 118140960795 + 1147187 * 2 ^ 59
def prefixEnd_1147187 : Nat := 4983230072969 + 3 ^ 40 * 1147187 * 2
def baseEnd_1147187 : Nat := 87267900976223460635065

theorem tailTrace_1147187 : CollatzResearch.WordTrace tailWord_1147187 prefixEnd_1147187 87267900976223460635065 := by
  unfold tailWord_1147187
  simp only [CollatzResearch.WordTrace]
  refine ⟨41841347294944897786407815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27894231529963265190938543 41841347294944897786407815)
  ·
    refine ⟨62762020942417346679611723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41841347294944897786407815 62762020942417346679611723)
    ·
      refine ⟨94143031413626020019417585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62762020942417346679611723 94143031413626020019417585)
      ·
        refine ⟨70607273560219515014563189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94143031413626020019417585 70607273560219515014563189)
        ·
          refine ⟨6619431896270579532615299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70607273560219515014563189 6619431896270579532615299)
          ·
            refine ⟨9929147844405869298922949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6619431896270579532615299 9929147844405869298922949)
            ·
              refine ⟨1861715220826100493548053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9929147844405869298922949 1861715220826100493548053)
              ·
                refine ⟨87267900976223460635065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1861715220826100493548053 87267900976223460635065)
                ·
                  rfl

theorem cell21_1147187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 6].length) (baseStart_1147187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147187 prefixEnd_1147187 := by exact prefixLift 1147187
  have htrace : WordTrace (prefixWord ++ tailWord_1147187) baseStart_1147187 baseEnd_1147187 := by
    simpa [prefixWord, tailWord_1147187, baseEnd_1147187] using wordTrace_append hprefix tailTrace_1147187
  have hstable : (prefixWord ++ tailWord_1147187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147187).length < 2 ^ (prefixWord ++ tailWord_1147187).sum := by decide
  have hdescent : baseEnd_1147187 < baseStart_1147187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147235 : List Nat := [1, 1, 1, 5, 2, 1, 3, 4, 3]
def baseStart_1147235 : Nat := 118140960795 + 1147235 * 2 ^ 59
def prefixEnd_1147235 : Nat := 4983230072969 + 3 ^ 40 * 1147235 * 2
def baseEnd_1147235 : Nat := 261814657182632965105097

theorem tailTrace_1147235 : CollatzResearch.WordTrace tailWord_1147235 prefixEnd_1147235 261814657182632965105097 := by
  unfold tailWord_1147235
  simp only [CollatzResearch.WordTrace]
  refine ⟨41843097998771001984155159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27895398665847334656103439 41843097998771001984155159)
  ·
    refine ⟨62764646998156502976232739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41843097998771001984155159 62764646998156502976232739)
    ·
      refine ⟨94146970497234754464349109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62764646998156502976232739 94146970497234754464349109)
      ·
        refine ⟨8826278484115758231032729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94146970497234754464349109 8826278484115758231032729)
        ·
          refine ⟨6619708863086818673274547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8826278484115758231032729 6619708863086818673274547)
          ·
            refine ⟨9929563294630228009911821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6619708863086818673274547 9929563294630228009911821)
            ·
              refine ⟨3723586235486335503716933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9929563294630228009911821 3723586235486335503716933)
              ·
                refine ⟨698172419153687906946925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3723586235486335503716933 698172419153687906946925)
                ·
                  refine ⟨261814657182632965105097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698172419153687906946925 261814657182632965105097)
                  ·
                    rfl

theorem cell21_1147235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 3].length) (baseStart_1147235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147235 prefixEnd_1147235 := by exact prefixLift 1147235
  have htrace : WordTrace (prefixWord ++ tailWord_1147235) baseStart_1147235 baseEnd_1147235 := by
    simpa [prefixWord, tailWord_1147235, baseEnd_1147235] using wordTrace_append hprefix tailTrace_1147235
  have hstable : (prefixWord ++ tailWord_1147235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147235).length < 2 ^ (prefixWord ++ tailWord_1147235).sum := by decide
  have hdescent : baseEnd_1147235 < baseStart_1147235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147286 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1147286 : Nat := 118140960795 + 1147286 * 2 ^ 59
def prefixEnd_1147286 : Nat := 4983230072969 + 3 ^ 40 * 1147286 * 2
def baseEnd_1147286 : Nat := 261826296077468209754993

theorem tailTrace_1147286 : CollatzResearch.WordTrace tailWord_1147286 prefixEnd_1147286 261826296077468209754993 := by
  unfold tailWord_1147286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2615309882599139855891357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27896638747724158462841141 2615309882599139855891357)
  ·
    refine ⟨980741205974677445959259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2615309882599139855891357 980741205974677445959259)
    ·
      refine ⟨1471111808962016168938889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980741205974677445959259 1471111808962016168938889)
      ·
        refine ⟨1103333856721512126704167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1471111808962016168938889 1103333856721512126704167)
        ·
          refine ⟨1655000785082268190056251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103333856721512126704167 1655000785082268190056251)
          ·
            refine ⟨2482501177623402285084377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655000785082268190056251 2482501177623402285084377)
            ·
              refine ⟨1861875883217551713813283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2482501177623402285084377 1861875883217551713813283)
              ·
                refine ⟨2792813824826327570719925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861875883217551713813283 2792813824826327570719925)
                ·
                  refine ⟨261826296077468209754993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2792813824826327570719925 261826296077468209754993)
                  ·
                    rfl

theorem cell21_1147286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1147286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147286 prefixEnd_1147286 := by exact prefixLift 1147286
  have htrace : WordTrace (prefixWord ++ tailWord_1147286) baseStart_1147286 baseEnd_1147286 := by
    simpa [prefixWord, tailWord_1147286, baseEnd_1147286] using wordTrace_append hprefix tailTrace_1147286
  have hstable : (prefixWord ++ tailWord_1147286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147286).length < 2 ^ (prefixWord ++ tailWord_1147286).sum := by decide
  have hdescent : baseEnd_1147286 < baseStart_1147286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147404 : List Nat := [2, 2, 1, 2, 4, 1, 4, 2, 3]
def baseStart_1147404 : Nat := 118140960795 + 1147404 * 2 ^ 59
def prefixEnd_1147404 : Nat := 4983230072969 + 3 ^ 40 * 1147404 * 2
def baseEnd_1147404 : Nat := 261853225285126226788085

theorem tailTrace_1147404 : CollatzResearch.WordTrace tailWord_1147404 prefixEnd_1147404 261853225285126226788085 := by
  unfold tailWord_1147404
  simp only [CollatzResearch.WordTrace]
  refine ⟨20924630967579371923528633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27899507956772495898038177 20924630967579371923528633)
  ·
    refine ⟨15693473225684528942646475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20924630967579371923528633 15693473225684528942646475)
    ·
      refine ⟨23540209838526793413969713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15693473225684528942646475 23540209838526793413969713)
      ·
        refine ⟨17655157378895095060477285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23540209838526793413969713 17655157378895095060477285)
        ·
          refine ⟨3310342008542830323839491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17655157378895095060477285 3310342008542830323839491)
          ·
            refine ⟨4965513012814245485759237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3310342008542830323839491 4965513012814245485759237)
            ·
              refine ⟨931033689902671028579857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4965513012814245485759237 931033689902671028579857)
              ·
                refine ⟨698275267427003271434893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931033689902671028579857 698275267427003271434893)
                ·
                  refine ⟨261853225285126226788085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698275267427003271434893 261853225285126226788085)
                  ·
                    rfl

theorem cell21_1147404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_1147404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147404 prefixEnd_1147404 := by exact prefixLift 1147404
  have htrace : WordTrace (prefixWord ++ tailWord_1147404) baseStart_1147404 baseEnd_1147404 := by
    simpa [prefixWord, tailWord_1147404, baseEnd_1147404] using wordTrace_append hprefix tailTrace_1147404
  have hstable : (prefixWord ++ tailWord_1147404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147404).length < 2 ^ (prefixWord ++ tailWord_1147404).sum := by decide
  have hdescent : baseEnd_1147404 < baseStart_1147404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147429 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 7]
def baseStart_1147429 : Nat := 118140960795 + 1147429 * 2 ^ 59
def prefixEnd_1147429 : Nat := 4983230072969 + 3 ^ 40 * 1147429 * 2
def baseEnd_1147429 : Nat := 261858930625731738871367

theorem tailTrace_1147429 : CollatzResearch.WordTrace tailWord_1147429 prefixEnd_1147429 261858930625731738871367 := by
  unfold tailWord_1147429
  simp only [CollatzResearch.WordTrace]
  refine ⟨41850173760068173116717341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27900115840045448744478227 41850173760068173116717341)
  ·
    refine ⟨15693815160025564918769003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41850173760068173116717341 15693815160025564918769003)
    ·
      refine ⟨23540722740038347378153505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15693815160025564918769003 23540722740038347378153505)
      ·
        refine ⟨17655542055028760533615129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23540722740038347378153505 17655542055028760533615129)
        ·
          refine ⟨13241656541271570400211347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17655542055028760533615129 13241656541271570400211347)
          ·
            refine ⟨19862484811907355600317021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13241656541271570400211347 19862484811907355600317021)
            ·
              refine ⟨7448431804465258350118883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19862484811907355600317021 7448431804465258350118883)
              ·
                refine ⟨11172647706697887525178325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7448431804465258350118883 11172647706697887525178325)
                ·
                  refine ⟨261858930625731738871367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11172647706697887525178325 261858930625731738871367)
                  ·
                    rfl

theorem cell21_1147429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_1147429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147429 prefixEnd_1147429 := by exact prefixLift 1147429
  have htrace : WordTrace (prefixWord ++ tailWord_1147429) baseStart_1147429 baseEnd_1147429 := by
    simpa [prefixWord, tailWord_1147429, baseEnd_1147429] using wordTrace_append hprefix tailTrace_1147429
  have hstable : (prefixWord ++ tailWord_1147429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147429).length < 2 ^ (prefixWord ++ tailWord_1147429).sum := by decide
  have hdescent : baseEnd_1147429 < baseStart_1147429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147463 : List Nat := [1, 1, 4, 1, 4, 1, 2, 4, 3]
def baseStart_1147463 : Nat := 118140960795 + 1147463 * 2 ^ 59
def prefixEnd_1147463 : Nat := 4983230072969 + 3 ^ 40 * 1147463 * 2
def baseEnd_1147463 : Nat := 261866689888955235304631

theorem tailTrace_1147463 : CollatzResearch.WordTrace tailWord_1147463 prefixEnd_1147463 261866689888955235304631 := by
  unfold tailWord_1147463
  simp only [CollatzResearch.WordTrace]
  refine ⟨41851413841944996923455043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27900942561296664615636695 41851413841944996923455043)
  ·
    refine ⟨62777120762917495385182565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41851413841944996923455043 62777120762917495385182565)
    ·
      refine ⟨11770710143047030384721731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62777120762917495385182565 11770710143047030384721731)
      ·
        refine ⟨17656065214570545577082597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11770710143047030384721731 17656065214570545577082597)
        ·
          refine ⟨3310512227731977295702987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17656065214570545577082597 3310512227731977295702987)
          ·
            refine ⟨4965768341597965943554481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3310512227731977295702987 4965768341597965943554481)
            ·
              refine ⟨3724326256198474457665861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4965768341597965943554481 3724326256198474457665861)
              ·
                refine ⟨698311173037213960812349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3724326256198474457665861 698311173037213960812349)
                ·
                  refine ⟨261866689888955235304631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698311173037213960812349 261866689888955235304631)
                  ·
                    rfl

theorem cell21_1147463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 3].length) (baseStart_1147463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147463 prefixEnd_1147463 := by exact prefixLift 1147463
  have htrace : WordTrace (prefixWord ++ tailWord_1147463) baseStart_1147463 baseEnd_1147463 := by
    simpa [prefixWord, tailWord_1147463, baseEnd_1147463] using wordTrace_append hprefix tailTrace_1147463
  have hstable : (prefixWord ++ tailWord_1147463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147463).length < 2 ^ (prefixWord ++ tailWord_1147463).sum := by decide
  have hdescent : baseEnd_1147463 < baseStart_1147463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147573 : List Nat := [1, 3, 3, 3, 1, 3, 2, 2, 3]
def baseStart_1147573 : Nat := 118140960795 + 1147573 * 2 ^ 59
def prefixEnd_1147573 : Nat := 4983230072969 + 3 ^ 40 * 1147573 * 2
def baseEnd_1147573 : Nat := 261891793387619488471073

theorem tailTrace_1147573 : CollatzResearch.WordTrace tailWord_1147573 prefixEnd_1147573 261891793387619488471073 := by
  unfold tailWord_1147573
  simp only [CollatzResearch.WordTrace]
  refine ⟨41855425871546485709959373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27903617247697657139972915 41855425871546485709959373)
  ·
    refine ⟨15695784701829932141234765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41855425871546485709959373 15695784701829932141234765)
    ·
      refine ⟨5885919263186224552963037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15695784701829932141234765 5885919263186224552963037)
      ·
        refine ⟨2207219723694834207361139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5885919263186224552963037 2207219723694834207361139)
        ·
          refine ⟨3310829585542251311041709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207219723694834207361139 3310829585542251311041709)
          ·
            refine ⟨1241561094578344241640641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3310829585542251311041709 1241561094578344241640641)
            ·
              refine ⟨931170820933758181230481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1241561094578344241640641 931170820933758181230481)
              ·
                refine ⟨698378115700318635922861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931170820933758181230481 698378115700318635922861)
                ·
                  refine ⟨261891793387619488471073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698378115700318635922861 261891793387619488471073)
                  ·
                    rfl

theorem cell21_1147573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_1147573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147573 prefixEnd_1147573 := by exact prefixLift 1147573
  have htrace : WordTrace (prefixWord ++ tailWord_1147573) baseStart_1147573 baseEnd_1147573 := by
    simpa [prefixWord, tailWord_1147573, baseEnd_1147573] using wordTrace_append hprefix tailTrace_1147573
  have hstable : (prefixWord ++ tailWord_1147573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147573).length < 2 ^ (prefixWord ++ tailWord_1147573).sum := by decide
  have hdescent : baseEnd_1147573 < baseStart_1147573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147595 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 10]
def baseStart_1147595 : Nat := 118140960795 + 1147595 * 2 ^ 59
def prefixEnd_1147595 : Nat := 4983230072969 + 3 ^ 40 * 1147595 * 2
def baseEnd_1147595 : Nat := 261896814087352339104361

theorem tailTrace_1147595 : CollatzResearch.WordTrace tailWord_1147595 prefixEnd_1147595 261896814087352339104361 := by
  unfold tailWord_1147595
  simp only [CollatzResearch.WordTrace]
  refine ⟨41856228277466783467260239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27904152184977855644840159 41856228277466783467260239)
  ·
    refine ⟨62784342416200175200890359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41856228277466783467260239 62784342416200175200890359)
    ·
      refine ⟨94176513624300262801335539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62784342416200175200890359 94176513624300262801335539)
      ·
        refine ⟨141264770436450394202003309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94176513624300262801335539 141264770436450394202003309)
        ·
          refine ⟨52974288913668897825751241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141264770436450394202003309 52974288913668897825751241)
          ·
            refine ⟨39730716685251673369313431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52974288913668897825751241 39730716685251673369313431)
            ·
              refine ⟨59596075027877510053970147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39730716685251673369313431 59596075027877510053970147)
              ·
                refine ⟨89394112541816265080955221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59596075027877510053970147 89394112541816265080955221)
                ·
                  refine ⟨261896814087352339104361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89394112541816265080955221 261896814087352339104361)
                  ·
                    rfl

theorem cell21_1147595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_1147595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147595 prefixEnd_1147595 := by exact prefixLift 1147595
  have htrace : WordTrace (prefixWord ++ tailWord_1147595) baseStart_1147595 baseEnd_1147595 := by
    simpa [prefixWord, tailWord_1147595, baseEnd_1147595] using wordTrace_append hprefix tailTrace_1147595
  have hstable : (prefixWord ++ tailWord_1147595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147595).length < 2 ^ (prefixWord ++ tailWord_1147595).sum := by decide
  have hdescent : baseEnd_1147595 < baseStart_1147595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147598 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_1147598 : Nat := 118140960795 + 1147598 * 2 ^ 59
def prefixEnd_1147598 : Nat := 4983230072969 + 3 ^ 40 * 1147598 * 2
def baseEnd_1147598 : Nat := 261897498728225000554355

theorem tailTrace_1147598 : CollatzResearch.WordTrace tailWord_1147598 prefixEnd_1147598 261897498728225000554355 := by
  unfold tailWord_1147598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5232042212056989372452431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27904225130970609986412965 5232042212056989372452431)
  ·
    refine ⟨7848063318085484058678647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5232042212056989372452431 7848063318085484058678647)
    ·
      refine ⟨11772094977128226088017971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7848063318085484058678647 11772094977128226088017971)
      ·
        refine ⟨17658142465692339132026957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11772094977128226088017971 17658142465692339132026957)
        ·
          refine ⟨6621803424634627174510109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17658142465692339132026957 6621803424634627174510109)
          ·
            refine ⟨2483176284237985190441291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6621803424634627174510109 2483176284237985190441291)
            ·
              refine ⟨3724764426356977785661937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483176284237985190441291 3724764426356977785661937)
              ·
                refine ⟨2793573319767733339246453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3724764426356977785661937 2793573319767733339246453)
                ·
                  refine ⟨261897498728225000554355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2793573319767733339246453 261897498728225000554355)
                  ·
                    rfl

theorem cell21_1147598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_1147598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147598 prefixEnd_1147598 := by exact prefixLift 1147598
  have htrace : WordTrace (prefixWord ++ tailWord_1147598) baseStart_1147598 baseEnd_1147598 := by
    simpa [prefixWord, tailWord_1147598, baseEnd_1147598] using wordTrace_append hprefix tailTrace_1147598
  have hstable : (prefixWord ++ tailWord_1147598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147598).length < 2 ^ (prefixWord ++ tailWord_1147598).sum := by decide
  have hdescent : baseEnd_1147598 < baseStart_1147598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147615 : List Nat := [1, 1, 2, 3, 2, 4, 2, 3, 3]
def baseStart_1147615 : Nat := 118140960795 + 1147615 * 2 ^ 59
def prefixEnd_1147615 : Nat := 4983230072969 + 3 ^ 40 * 1147615 * 2
def baseEnd_1147615 : Nat := 261901378359836748770987

theorem tailTrace_1147615 : CollatzResearch.WordTrace tailWord_1147615 prefixEnd_1147615 261901378359836748770987 := by
  unfold tailWord_1147615
  simp only [CollatzResearch.WordTrace]
  refine ⟨41856957737394326882988299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27904638491596217921992199 41856957737394326882988299)
  ·
    refine ⟨62785436606091490324482449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41856957737394326882988299 62785436606091490324482449)
    ·
      refine ⟨47089077454568617743361837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62785436606091490324482449 47089077454568617743361837)
      ·
        refine ⟨17658404045463231653760689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47089077454568617743361837 17658404045463231653760689)
        ·
          refine ⟨13243803034097423740320517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17658404045463231653760689 13243803034097423740320517)
          ·
            refine ⟨2483213068893266951310097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13243803034097423740320517 2483213068893266951310097)
            ·
              refine ⟨1862409801669950213482573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2483213068893266951310097 1862409801669950213482573)
              ·
                refine ⟨698403675626231330055965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1862409801669950213482573 698403675626231330055965)
                ·
                  refine ⟨261901378359836748770987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698403675626231330055965 261901378359836748770987)
                  ·
                    rfl

theorem cell21_1147615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 3].length) (baseStart_1147615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147615 prefixEnd_1147615 := by exact prefixLift 1147615
  have htrace : WordTrace (prefixWord ++ tailWord_1147615) baseStart_1147615 baseEnd_1147615 := by
    simpa [prefixWord, tailWord_1147615, baseEnd_1147615] using wordTrace_append hprefix tailTrace_1147615
  have hstable : (prefixWord ++ tailWord_1147615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147615).length < 2 ^ (prefixWord ++ tailWord_1147615).sum := by decide
  have hdescent : baseEnd_1147615 < baseStart_1147615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147657 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 5]
def baseStart_1147657 : Nat := 118140960795 + 1147657 * 2 ^ 59
def prefixEnd_1147657 : Nat := 4983230072969 + 3 ^ 40 * 1147657 * 2
def baseEnd_1147657 : Nat := 261910963332054009070901

theorem tailTrace_1147657 : CollatzResearch.WordTrace tailWord_1147657 prefixEnd_1147657 261910963332054009070901 := by
  unfold tailWord_1147657
  simp only [CollatzResearch.WordTrace]
  refine ⟨41858489603242168056017225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27905659735494778704011483 41858489603242168056017225)
  ·
    refine ⟨31393867202431626042012919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41858489603242168056017225 31393867202431626042012919)
    ·
      refine ⟨47090800803647439063019379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31393867202431626042012919 47090800803647439063019379)
      ·
        refine ⟨70636201205471158594529069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47090800803647439063019379 70636201205471158594529069)
        ·
          refine ⟨26488575452051684472948401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70636201205471158594529069 26488575452051684472948401)
          ·
            refine ⟨19866431589038763354711301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26488575452051684472948401 19866431589038763354711301)
            ·
              refine ⟨3724955922944768129008369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19866431589038763354711301 3724955922944768129008369)
              ·
                refine ⟨2793716942208576096756277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3724955922944768129008369 2793716942208576096756277)
                ·
                  refine ⟨261910963332054009070901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2793716942208576096756277 261910963332054009070901)
                  ·
                    rfl

theorem cell21_1147657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_1147657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147657 prefixEnd_1147657 := by exact prefixLift 1147657
  have htrace : WordTrace (prefixWord ++ tailWord_1147657) baseStart_1147657 baseEnd_1147657 := by
    simpa [prefixWord, tailWord_1147657, baseEnd_1147657] using wordTrace_append hprefix tailTrace_1147657
  have hstable : (prefixWord ++ tailWord_1147657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147657).length < 2 ^ (prefixWord ++ tailWord_1147657).sum := by decide
  have hdescent : baseEnd_1147657 < baseStart_1147657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147666 : List Nat := [3, 2, 4, 1, 3, 1, 1, 3, 3]
def baseStart_1147666 : Nat := 118140960795 + 1147666 * 2 ^ 59
def prefixEnd_1147666 : Nat := 4983230072969 + 3 ^ 40 * 1147666 * 2
def baseEnd_1147666 : Nat := 261913017254671993420883

theorem tailTrace_1147666 : CollatzResearch.WordTrace tailWord_1147666 prefixEnd_1147666 261913017254671993420883 := by
  unfold tailWord_1147666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10464704465052390648273713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27905878573473041728729901 10464704465052390648273713)
  ·
    refine ⟨7848528348789292986205285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10464704465052390648273713 7848528348789292986205285)
    ·
      refine ⟨1471599065397992434913491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7848528348789292986205285 1471599065397992434913491)
      ·
        refine ⟨2207398598096988652370237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471599065397992434913491 2207398598096988652370237)
        ·
          refine ⟨827774474286370744638839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2207398598096988652370237 827774474286370744638839)
          ·
            refine ⟨1241661711429556116958259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827774474286370744638839 1241661711429556116958259)
            ·
              refine ⟨1862492567144334175437389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241661711429556116958259 1862492567144334175437389)
              ·
                refine ⟨698434712679125315789021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1862492567144334175437389 698434712679125315789021)
                ·
                  refine ⟨261913017254671993420883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698434712679125315789021 261913017254671993420883)
                  ·
                    rfl

theorem cell21_1147666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_1147666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147666 prefixEnd_1147666 := by exact prefixLift 1147666
  have htrace : WordTrace (prefixWord ++ tailWord_1147666) baseStart_1147666 baseEnd_1147666 := by
    simpa [prefixWord, tailWord_1147666, baseEnd_1147666] using wordTrace_append hprefix tailTrace_1147666
  have hstable : (prefixWord ++ tailWord_1147666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147666).length < 2 ^ (prefixWord ++ tailWord_1147666).sum := by decide
  have hdescent : baseEnd_1147666 < baseStart_1147666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147677 : List Nat := [1, 4, 2, 4, 2, 1, 7]
def baseStart_1147677 : Nat := 118140960795 + 1147677 * 2 ^ 59
def prefixEnd_1147677 : Nat := 4983230072969 + 3 ^ 40 * 1147677 * 2
def baseEnd_1147677 : Nat := 29101725289393157637503

theorem tailTrace_1147677 : CollatzResearch.WordTrace tailWord_1147677 prefixEnd_1147677 29101725289393157637503 := by
  unfold tailWord_1147677
  simp only [CollatzResearch.WordTrace]
  refine ⟨41859219063169711471745285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27906146042113140981163523 41859219063169711471745285)
  ·
    refine ⟨7848603574344320900952241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41859219063169711471745285 7848603574344320900952241)
    ·
      refine ⟨5886452680758240675714181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7848603574344320900952241 5886452680758240675714181)
      ·
        refine ⟨1103709877642170126696409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5886452680758240675714181 1103709877642170126696409)
        ·
          refine ⟨827782408231627595022307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103709877642170126696409 827782408231627595022307)
          ·
            refine ⟨1241673612347441392533461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827782408231627595022307 1241673612347441392533461)
            ·
              refine ⟨29101725289393157637503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1241673612347441392533461 29101725289393157637503)
              ·
                rfl

theorem cell21_1147677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 7].length) (baseStart_1147677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147677 prefixEnd_1147677 := by exact prefixLift 1147677
  have htrace : WordTrace (prefixWord ++ tailWord_1147677) baseStart_1147677 baseEnd_1147677 := by
    simpa [prefixWord, tailWord_1147677, baseEnd_1147677] using wordTrace_append hprefix tailTrace_1147677
  have hstable : (prefixWord ++ tailWord_1147677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147677).length < 2 ^ (prefixWord ++ tailWord_1147677).sum := by decide
  have hdescent : baseEnd_1147677 < baseStart_1147677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147688 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_1147688 : Nat := 118140960795 + 1147688 * 2 ^ 59
def prefixEnd_1147688 : Nat := 4983230072969 + 3 ^ 40 * 1147688 * 2
def baseEnd_1147688 : Nat := 261918037954404844054171

theorem tailTrace_1147688 : CollatzResearch.WordTrace tailWord_1147688 prefixEnd_1147688 261918037954404844054171 := by
  unfold tailWord_1147688
  simp only [CollatzResearch.WordTrace]
  refine ⟨20929810133064930175197859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27906413510753240233597145 20929810133064930175197859)
  ·
    refine ⟨31394715199597395262796789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20929810133064930175197859 31394715199597395262796789)
    ·
      refine ⟨2943254549962255805887199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31394715199597395262796789 2943254549962255805887199)
      ·
        refine ⟨4414881824943383708830799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2943254549962255805887199 4414881824943383708830799)
        ·
          refine ⟨6622322737415075563246199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4414881824943383708830799 6622322737415075563246199)
          ·
            refine ⟨9933484106122613344869299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6622322737415075563246199 9933484106122613344869299)
            ·
              refine ⟨14900226159183920017303949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9933484106122613344869299 14900226159183920017303949)
              ·
                refine ⟨5587584809693970006488981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14900226159183920017303949 5587584809693970006488981)
                ·
                  refine ⟨261918037954404844054171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5587584809693970006488981 261918037954404844054171)
                  ·
                    rfl

theorem cell21_1147688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_1147688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147688 prefixEnd_1147688 := by exact prefixLift 1147688
  have htrace : WordTrace (prefixWord ++ tailWord_1147688) baseStart_1147688 baseEnd_1147688 := by
    simpa [prefixWord, tailWord_1147688, baseEnd_1147688] using wordTrace_append hprefix tailTrace_1147688
  have hstable : (prefixWord ++ tailWord_1147688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147688).length < 2 ^ (prefixWord ++ tailWord_1147688).sum := by decide
  have hdescent : baseEnd_1147688 < baseStart_1147688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147854 : List Nat := [4, 1, 1, 1, 2, 3, 9]
def baseStart_1147854 : Nat := 118140960795 + 1147854 * 2 ^ 59
def prefixEnd_1147854 : Nat := 4983230072969 + 3 ^ 40 * 1147854 * 2
def baseEnd_1147854 : Nat := 29106213490669493809685

theorem tailTrace_1147854 : CollatzResearch.WordTrace tailWord_1147854 prefixEnd_1147854 29106213490669493809685 := by
  unfold tailWord_1147854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5233209347941058837617327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27910449855685647133959077 5233209347941058837617327)
  ·
    refine ⟨7849814021911588256425991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5233209347941058837617327 7849814021911588256425991)
    ·
      refine ⟨11774721032867382384638987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7849814021911588256425991 11774721032867382384638987)
      ·
        refine ⟨17662081549301073576958481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11774721032867382384638987 17662081549301073576958481)
        ·
          refine ⟨13246561161975805182718861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17662081549301073576958481 13246561161975805182718861)
          ·
            refine ⟨4967460435740926943519573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13246561161975805182718861 4967460435740926943519573)
            ·
              refine ⟨29106213490669493809685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4967460435740926943519573 29106213490669493809685)
              ·
                rfl

theorem cell21_1147854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 9].length) (baseStart_1147854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147854 prefixEnd_1147854 := by exact prefixLift 1147854
  have htrace : WordTrace (prefixWord ++ tailWord_1147854) baseStart_1147854 baseEnd_1147854 := by
    simpa [prefixWord, tailWord_1147854, baseEnd_1147854] using wordTrace_append hprefix tailTrace_1147854
  have hstable : (prefixWord ++ tailWord_1147854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147854).length < 2 ^ (prefixWord ++ tailWord_1147854).sum := by decide
  have hdescent : baseEnd_1147854 < baseStart_1147854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147860 : List Nat := [2, 4, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1147860 : Nat := 118140960795 + 1147860 * 2 ^ 59
def prefixEnd_1147860 : Nat := 4983230072969 + 3 ^ 40 * 1147860 * 2
def baseEnd_1147860 : Nat := 261957290697770767187153

theorem tailTrace_1147860 : CollatzResearch.WordTrace tailWord_1147860 prefixEnd_1147860 261957290697770767187153 := by
  unfold tailWord_1147860
  simp only [CollatzResearch.WordTrace]
  refine ⟨20932946810753366862828517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27910595747671155817104689 20932946810753366862828517)
  ·
    refine ⟨3924927527016256286780347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20932946810753366862828517 3924927527016256286780347)
    ·
      refine ⟨5887391290524384430170521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3924927527016256286780347 5887391290524384430170521)
      ·
        refine ⟨4415543467893288322627891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5887391290524384430170521 4415543467893288322627891)
        ·
          refine ⟨6623315201839932483941837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4415543467893288322627891 6623315201839932483941837)
          ·
            refine ⟨2483743200689974681478189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6623315201839932483941837 2483743200689974681478189)
            ·
              refine ⟨931403700258740505554321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2483743200689974681478189 931403700258740505554321)
              ·
                refine ⟨698552775194055379165741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931403700258740505554321 698552775194055379165741)
                ·
                  refine ⟨261957290697770767187153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698552775194055379165741 261957290697770767187153)
                  ·
                    rfl

theorem cell21_1147860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1147860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147860 prefixEnd_1147860 := by exact prefixLift 1147860
  have htrace : WordTrace (prefixWord ++ tailWord_1147860) baseStart_1147860 baseEnd_1147860 := by
    simpa [prefixWord, tailWord_1147860, baseEnd_1147860] using wordTrace_append hprefix tailTrace_1147860
  have hstable : (prefixWord ++ tailWord_1147860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147860).length < 2 ^ (prefixWord ++ tailWord_1147860).sum := by decide
  have hdescent : baseEnd_1147860 < baseStart_1147860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147871 : List Nat := [1, 1, 2, 3, 5, 1, 2, 6]
def baseStart_1147871 : Nat := 118140960795 + 1147871 * 2 ^ 59
def prefixEnd_1147871 : Nat := 4983230072969 + 3 ^ 40 * 1147871 * 2
def baseEnd_1147871 : Nat := 87319933682545730834599

theorem tailTrace_1147871 : CollatzResearch.WordTrace tailWord_1147871 prefixEnd_1147871 87319933682545730834599 := by
  unfold tailWord_1147871
  simp only [CollatzResearch.WordTrace]
  refine ⟨41866294824466882604307467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27910863216311255069538311 41866294824466882604307467)
  ·
    refine ⟨62799442236700323906461201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41866294824466882604307467 62799442236700323906461201)
    ·
      refine ⟨47099581677525242929845901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62799442236700323906461201 47099581677525242929845901)
      ·
        refine ⟨17662343129071966098692213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47099581677525242929845901 17662343129071966098692213)
        ·
          refine ⟨1655844668350496821752395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17662343129071966098692213 1655844668350496821752395)
          ·
            refine ⟨2483767002525745232628593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655844668350496821752395 2483767002525745232628593)
            ·
              refine ⟨1862825251894308924471445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2483767002525745232628593 1862825251894308924471445)
              ·
                refine ⟨87319933682545730834599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1862825251894308924471445 87319933682545730834599)
                ·
                  rfl

theorem cell21_1147871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 6].length) (baseStart_1147871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147871 prefixEnd_1147871 := by exact prefixLift 1147871
  have htrace : WordTrace (prefixWord ++ tailWord_1147871) baseStart_1147871 baseEnd_1147871 := by
    simpa [prefixWord, tailWord_1147871, baseEnd_1147871] using wordTrace_append hprefix tailTrace_1147871
  have hstable : (prefixWord ++ tailWord_1147871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147871).length < 2 ^ (prefixWord ++ tailWord_1147871).sum := by decide
  have hdescent : baseEnd_1147871 < baseStart_1147871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147874 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1147874 : Nat := 118140960795 + 1147874 * 2 ^ 59
def prefixEnd_1147874 : Nat := 4983230072969 + 3 ^ 40 * 1147874 * 2
def baseEnd_1147874 : Nat := 261960485688509853953791

theorem tailTrace_1147874 : CollatzResearch.WordTrace tailWord_1147874 prefixEnd_1147874 261960485688509853953791 := by
  unfold tailWord_1147874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466601060864003529166669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27910936162304009411111117 10466601060864003529166669)
  ·
    refine ⟨3924975397824001323437501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10466601060864003529166669 3924975397824001323437501)
    ·
      refine ⟨1471865774184000496289063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3924975397824001323437501 1471865774184000496289063)
      ·
        refine ⟨2207798661276000744433595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471865774184000496289063 2207798661276000744433595)
        ·
          refine ⟨3311697991914001116650393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207798661276000744433595 3311697991914001116650393)
          ·
            refine ⟨2483773493935500837487795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3311697991914001116650393 2483773493935500837487795)
            ·
              refine ⟨3725660240903251256231693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483773493935500837487795 3725660240903251256231693)
              ·
                refine ⟨1397122590338719221086885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3725660240903251256231693 1397122590338719221086885)
                ·
                  refine ⟨261960485688509853953791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1397122590338719221086885 261960485688509853953791)
                  ·
                    rfl

theorem cell21_1147874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1147874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147874 prefixEnd_1147874 := by exact prefixLift 1147874
  have htrace : WordTrace (prefixWord ++ tailWord_1147874) baseStart_1147874 baseEnd_1147874 := by
    simpa [prefixWord, tailWord_1147874, baseEnd_1147874] using wordTrace_append hprefix tailTrace_1147874
  have hstable : (prefixWord ++ tailWord_1147874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147874).length < 2 ^ (prefixWord ++ tailWord_1147874).sum := by decide
  have hdescent : baseEnd_1147874 < baseStart_1147874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147916 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_1147916 : Nat := 118140960795 + 1147916 * 2 ^ 59
def prefixEnd_1147916 : Nat := 4983230072969 + 3 ^ 40 * 1147916 * 2
def baseEnd_1147916 : Nat := 261970070660727114253705

theorem tailTrace_1147916 : CollatzResearch.WordTrace tailWord_1147916 prefixEnd_1147916 261970070660727114253705 := by
  unfold tailWord_1147916
  simp only [CollatzResearch.WordTrace]
  refine ⟨20933968054651927644847801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27911957406202570193130401 20933968054651927644847801)
  ·
    refine ⟨15700476040988945733635851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20933968054651927644847801 15700476040988945733635851)
    ·
      refine ⟨23550714061483418600453777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15700476040988945733635851 23550714061483418600453777)
      ·
        refine ⟨17663035546112563950340333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23550714061483418600453777 17663035546112563950340333)
        ·
          refine ⟨6623638329792211481377625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17663035546112563950340333 6623638329792211481377625)
          ·
            refine ⟨4967728747344158611033219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6623638329792211481377625 4967728747344158611033219)
            ·
              refine ⟨7451593121016237916549829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967728747344158611033219 7451593121016237916549829)
              ·
                refine ⟨1397173710190544609353093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7451593121016237916549829 1397173710190544609353093)
                ·
                  refine ⟨261970070660727114253705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1397173710190544609353093 261970070660727114253705)
                  ·
                    rfl

theorem cell21_1147916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_1147916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147916 prefixEnd_1147916 := by exact prefixLift 1147916
  have htrace : WordTrace (prefixWord ++ tailWord_1147916) baseStart_1147916 baseEnd_1147916 := by
    simpa [prefixWord, tailWord_1147916, baseEnd_1147916] using wordTrace_append hprefix tailTrace_1147916
  have hstable : (prefixWord ++ tailWord_1147916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147916).length < 2 ^ (prefixWord ++ tailWord_1147916).sum := by decide
  have hdescent : baseEnd_1147916 < baseStart_1147916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147922 : List Nat := [3, 2, 5, 1, 1, 2, 1, 6]
def baseStart_1147922 : Nat := 118140960795 + 1147922 * 2 ^ 59
def prefixEnd_1147922 : Nat := 4983230072969 + 3 ^ 40 * 1147922 * 2
def baseEnd_1147922 : Nat := 87323813314157479051231

theorem tailTrace_1147922 : CollatzResearch.WordTrace tailWord_1147922 prefixEnd_1147922 87323813314157479051231 := by
  unfold tailWord_1147922
  simp only [CollatzResearch.WordTrace]
  refine ⟨10467038736820529578603505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27912103298188078876276013 10467038736820529578603505)
  ·
    refine ⟨7850279052615397183952629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10467038736820529578603505 7850279052615397183952629)
    ·
      refine ⟨735963661182693485995559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7850279052615397183952629 735963661182693485995559)
      ·
        refine ⟨1103945491774040228993339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735963661182693485995559 1103945491774040228993339)
        ·
          refine ⟨1655918237661060343490009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103945491774040228993339 1655918237661060343490009)
          ·
            refine ⟨1241938678245795257617507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1655918237661060343490009 1241938678245795257617507)
            ·
              refine ⟨1862908017368692886426261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241938678245795257617507 1862908017368692886426261)
              ·
                refine ⟨87323813314157479051231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1862908017368692886426261 87323813314157479051231)
                ·
                  rfl

theorem cell21_1147922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_1147922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147922 prefixEnd_1147922 := by exact prefixLift 1147922
  have htrace : WordTrace (prefixWord ++ tailWord_1147922) baseStart_1147922 baseEnd_1147922 := by
    simpa [prefixWord, tailWord_1147922, baseEnd_1147922] using wordTrace_append hprefix tailTrace_1147922
  have hstable : (prefixWord ++ tailWord_1147922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147922).length < 2 ^ (prefixWord ++ tailWord_1147922).sum := by decide
  have hdescent : baseEnd_1147922 < baseStart_1147922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147978 : List Nat := [3, 1, 2, 1, 1, 2, 4, 4, 3]
def baseStart_1147978 : Nat := 118140960795 + 1147978 * 2 ^ 59
def prefixEnd_1147978 : Nat := 4983230072969 + 3 ^ 40 * 1147978 * 2
def baseEnd_1147978 : Nat := 261984219905428784220245

theorem tailTrace_1147978 : CollatzResearch.WordTrace tailWord_1147978 prefixEnd_1147978 261984219905428784220245 := by
  unfold tailWord_1147978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10467549358769809969613147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27913464956719493252301725 10467549358769809969613147)
  ·
    refine ⟨15701324038154714954419721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10467549358769809969613147 15701324038154714954419721)
    ·
      refine ⟨11775993028616036215814791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15701324038154714954419721 11775993028616036215814791)
      ·
        refine ⟨17663989542924054323722187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11775993028616036215814791 17663989542924054323722187)
        ·
          refine ⟨26495984314386081485583281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17663989542924054323722187 26495984314386081485583281)
          ·
            refine ⟨19871988235789561114187461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26495984314386081485583281 19871988235789561114187461)
            ·
              refine ⟨3725997794210542708910149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19871988235789561114187461 3725997794210542708910149)
              ·
                refine ⟨698624586414476757920653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3725997794210542708910149 698624586414476757920653)
                ·
                  refine ⟨261984219905428784220245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698624586414476757920653 261984219905428784220245)
                  ·
                    rfl

theorem cell21_1147978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_1147978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147978 prefixEnd_1147978 := by exact prefixLift 1147978
  have htrace : WordTrace (prefixWord ++ tailWord_1147978) baseStart_1147978 baseEnd_1147978 := by
    simpa [prefixWord, tailWord_1147978, baseEnd_1147978] using wordTrace_append hprefix tailTrace_1147978
  have hstable : (prefixWord ++ tailWord_1147978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147978).length < 2 ^ (prefixWord ++ tailWord_1147978).sum := by decide
  have hdescent : baseEnd_1147978 < baseStart_1147978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147998 : List Nat := [4, 4, 1, 1, 1, 3, 2, 5]
def baseStart_1147998 : Nat := 118140960795 + 1147998 * 2 ^ 59
def prefixEnd_1147998 : Nat := 4983230072969 + 3 ^ 40 * 1147998 * 2
def baseEnd_1147998 : Nat := 87329594725971064628957

theorem tailTrace_1147998 : CollatzResearch.WordTrace tailWord_1147998 prefixEnd_1147998 87329594725971064628957 := by
  unfold tailWord_1147998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5233865861875847911772581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27913951263337855529453765 5233865861875847911772581)
  ·
    refine ⟨981349849101721483457359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5233865861875847911772581 981349849101721483457359)
    ·
      refine ⟨1472024773652582225186039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 981349849101721483457359 1472024773652582225186039)
      ·
        refine ⟨2208037160478873337779059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472024773652582225186039 2208037160478873337779059)
        ·
          refine ⟨3312055740718310006668589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208037160478873337779059 3312055740718310006668589)
          ·
            refine ⟨1242020902769366252500721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3312055740718310006668589 1242020902769366252500721)
            ·
              refine ⟨931515677077024689375541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1242020902769366252500721 931515677077024689375541)
              ·
                refine ⟨87329594725971064628957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 931515677077024689375541 87329594725971064628957)
                ·
                  rfl

theorem cell21_1147998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_1147998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1147998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1147998 prefixEnd_1147998 := by exact prefixLift 1147998
  have htrace : WordTrace (prefixWord ++ tailWord_1147998) baseStart_1147998 baseEnd_1147998 := by
    simpa [prefixWord, tailWord_1147998, baseEnd_1147998] using wordTrace_append hprefix tailTrace_1147998
  have hstable : (prefixWord ++ tailWord_1147998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147998).length < 2 ^ (prefixWord ++ tailWord_1147998).sum := by decide
  have hdescent : baseEnd_1147998 < baseStart_1147998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148161 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 4]
def baseStart_1148161 : Nat := 118140960795 + 1148161 * 2 ^ 59
def prefixEnd_1148161 : Nat := 4983230072969 + 3 ^ 40 * 1148161 * 2
def baseEnd_1148161 : Nat := 262025982998661132669871

theorem tailTrace_1148161 : CollatzResearch.WordTrace tailWord_1148161 prefixEnd_1148161 262025982998661132669871 := by
  unfold tailWord_1148161
  simp only [CollatzResearch.WordTrace]
  refine ⟨41876871993416262132364337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27917914662277508088242891 41876871993416262132364337)
  ·
    refine ⟨31407653995062196599273253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41876871993416262132364337 31407653995062196599273253)
    ·
      refine ⟨5888935124074161862363735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31407653995062196599273253 5888935124074161862363735)
      ·
        refine ⟨8833402686111242793545603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5888935124074161862363735 8833402686111242793545603)
        ·
          refine ⟨13250104029166864190318405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8833402686111242793545603 13250104029166864190318405)
          ·
            refine ⟨2484394505468787035684701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13250104029166864190318405 2484394505468787035684701)
            ·
              refine ⟨931647939550795138381763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2484394505468787035684701 931647939550795138381763)
              ·
                refine ⟨1397471909326192707572645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931647939550795138381763 1397471909326192707572645)
                ·
                  refine ⟨262025982998661132669871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1397471909326192707572645 262025982998661132669871)
                  ·
                    rfl

theorem cell21_1148161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_1148161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148161 prefixEnd_1148161 := by exact prefixLift 1148161
  have htrace : WordTrace (prefixWord ++ tailWord_1148161) baseStart_1148161 baseEnd_1148161 := by
    simpa [prefixWord, tailWord_1148161, baseEnd_1148161] using wordTrace_append hprefix tailTrace_1148161
  have hstable : (prefixWord ++ tailWord_1148161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148161).length < 2 ^ (prefixWord ++ tailWord_1148161).sum := by decide
  have hdescent : baseEnd_1148161 < baseStart_1148161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148220 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_1148220 : Nat := 118140960795 + 1148220 * 2 ^ 59
def prefixEnd_1148220 : Nat := 4983230072969 + 3 ^ 40 * 1148220 * 2
def baseEnd_1148220 : Nat := 262039447602490141186417

theorem tailTrace_1148220 : CollatzResearch.WordTrace tailWord_1148220 prefixEnd_1148220 262039447602490141186417 := by
  unfold tailWord_1148220
  simp only [CollatzResearch.WordTrace]
  refine ⟨20939511950101257604381057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27919349266801676805841409 20939511950101257604381057)
  ·
    refine ⟨15704633962575943203285793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20939511950101257604381057 15704633962575943203285793)
    ·
      refine ⟨11778475471931957402464345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15704633962575943203285793 11778475471931957402464345)
      ·
        refine ⟨8833856603948968051848259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11778475471931957402464345 8833856603948968051848259)
        ·
          refine ⟨13250784905923452077772389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8833856603948968051848259 13250784905923452077772389)
          ·
            refine ⟨2484522169860647264582323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13250784905923452077772389 2484522169860647264582323)
            ·
              refine ⟨3726783254790970896873485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2484522169860647264582323 3726783254790970896873485)
              ·
                refine ⟨1397543720546614086327557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3726783254790970896873485 1397543720546614086327557)
                ·
                  refine ⟨262039447602490141186417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1397543720546614086327557 262039447602490141186417)
                  ·
                    rfl

theorem cell21_1148220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_1148220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148220 prefixEnd_1148220 := by exact prefixLift 1148220
  have htrace : WordTrace (prefixWord ++ tailWord_1148220) baseStart_1148220 baseEnd_1148220 := by
    simpa [prefixWord, tailWord_1148220, baseEnd_1148220] using wordTrace_append hprefix tailTrace_1148220
  have hstable : (prefixWord ++ tailWord_1148220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148220).length < 2 ^ (prefixWord ++ tailWord_1148220).sum := by decide
  have hdescent : baseEnd_1148220 < baseStart_1148220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148279 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 4]
def baseStart_1148279 : Nat := 118140960795 + 1148279 * 2 ^ 59
def prefixEnd_1148279 : Nat := 4983230072969 + 3 ^ 40 * 1148279 * 2
def baseEnd_1148279 : Nat := 262052912206319149702963

theorem tailTrace_1148279 : CollatzResearch.WordTrace tailWord_1148279 prefixEnd_1148279 262052912206319149702963 := by
  unfold tailWord_1148279
  simp only [CollatzResearch.WordTrace]
  refine ⟨41881175806988768285159891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27920783871325845523439927 41881175806988768285159891)
  ·
    refine ⟨62821763710483152427739837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41881175806988768285159891 62821763710483152427739837)
    ·
      refine ⟨23558161391431182160402439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62821763710483152427739837 23558161391431182160402439)
      ·
        refine ⟨35337242087146773240603659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23558161391431182160402439 35337242087146773240603659)
        ·
          refine ⟨53005863130720159860905489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35337242087146773240603659 53005863130720159860905489)
          ·
            refine ⟨39754397348040119895679117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53005863130720159860905489 39754397348040119895679117)
            ·
              refine ⟨14907899005515044960879669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39754397348040119895679117 14907899005515044960879669)
              ·
                refine ⟨1397615531767035465082469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14907899005515044960879669 1397615531767035465082469)
                ·
                  refine ⟨262052912206319149702963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1397615531767035465082469 262052912206319149702963)
                  ·
                    rfl

theorem cell21_1148279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 4].length) (baseStart_1148279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148279 prefixEnd_1148279 := by exact prefixLift 1148279
  have htrace : WordTrace (prefixWord ++ tailWord_1148279) baseStart_1148279 baseEnd_1148279 := by
    simpa [prefixWord, tailWord_1148279, baseEnd_1148279] using wordTrace_append hprefix tailTrace_1148279
  have hstable : (prefixWord ++ tailWord_1148279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148279).length < 2 ^ (prefixWord ++ tailWord_1148279).sum := by decide
  have hdescent : baseEnd_1148279 < baseStart_1148279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148293 : List Nat := [1, 3, 1, 1, 3, 1, 2, 9]
def baseStart_1148293 : Nat := 118140960795 + 1148293 * 2 ^ 59
def prefixEnd_1148293 : Nat := 4983230072969 + 3 ^ 40 * 1148293 * 2
def baseEnd_1148293 : Nat := 87352035732352745489867

theorem tailTrace_1148293 : CollatzResearch.WordTrace tailWord_1148293 prefixEnd_1148293 87352035732352745489867 := by
  unfold tailWord_1148293
  simp only [CollatzResearch.WordTrace]
  refine ⟨41881686428938048676169533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27921124285958699117446355 41881686428938048676169533)
  ·
    refine ⟨15705632410851768253563575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41881686428938048676169533 15705632410851768253563575)
    ·
      refine ⟨23558448616277652380345363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15705632410851768253563575 23558448616277652380345363)
      ·
        refine ⟨35337672924416478570518045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23558448616277652380345363 35337672924416478570518045)
        ·
          refine ⟨13251627346656179463944267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35337672924416478570518045 13251627346656179463944267)
          ·
            refine ⟨19877441019984269195916401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13251627346656179463944267 19877441019984269195916401)
            ·
              refine ⟨14908080764988201896937301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19877441019984269195916401 14908080764988201896937301)
              ·
                refine ⟨87352035732352745489867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14908080764988201896937301 87352035732352745489867)
                ·
                  rfl

theorem cell21_1148293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 9].length) (baseStart_1148293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148293 prefixEnd_1148293 := by exact prefixLift 1148293
  have htrace : WordTrace (prefixWord ++ tailWord_1148293) baseStart_1148293 baseEnd_1148293 := by
    simpa [prefixWord, tailWord_1148293, baseEnd_1148293] using wordTrace_append hprefix tailTrace_1148293
  have hstable : (prefixWord ++ tailWord_1148293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148293).length < 2 ^ (prefixWord ++ tailWord_1148293).sum := by decide
  have hdescent : baseEnd_1148293 < baseStart_1148293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148341 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 5]
def baseStart_1148341 : Nat := 118140960795 + 1148341 * 2 ^ 59
def prefixEnd_1148341 : Nat := 4983230072969 + 3 ^ 40 * 1148341 * 2
def baseEnd_1148341 : Nat := 262067061451020819669503

theorem tailTrace_1148341 : CollatzResearch.WordTrace tailWord_1148341 prefixEnd_1148341 262067061451020819669503 := by
  unfold tailWord_1148341
  simp only [CollatzResearch.WordTrace]
  refine ⟨41883437132764152873916877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27922291421842768582611251 41883437132764152873916877)
  ·
    refine ⟨15706288924786557327718829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41883437132764152873916877 15706288924786557327718829)
    ·
      refine ⟨5889858346794958997894561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15706288924786557327718829 5889858346794958997894561)
      ·
        refine ⟨4417393760096219248420921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5889858346794958997894561 4417393760096219248420921)
        ·
          refine ⟨3313045320072164436315691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4417393760096219248420921 3313045320072164436315691)
          ·
            refine ⟨4969567980108246654473537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313045320072164436315691 4969567980108246654473537)
            ·
              refine ⟨3727175985081184990855153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4969567980108246654473537 3727175985081184990855153)
              ·
                refine ⟨2795381988810888743141365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3727175985081184990855153 2795381988810888743141365)
                ·
                  refine ⟨262067061451020819669503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2795381988810888743141365 262067061451020819669503)
                  ·
                    rfl

theorem cell21_1148341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_1148341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148341 prefixEnd_1148341 := by exact prefixLift 1148341
  have htrace : WordTrace (prefixWord ++ tailWord_1148341) baseStart_1148341 baseEnd_1148341 := by
    simpa [prefixWord, tailWord_1148341, baseEnd_1148341] using wordTrace_append hprefix tailTrace_1148341
  have hstable : (prefixWord ++ tailWord_1148341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148341).length < 2 ^ (prefixWord ++ tailWord_1148341).sum := by decide
  have hdescent : baseEnd_1148341 < baseStart_1148341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148389 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 4]
def baseStart_1148389 : Nat := 118140960795 + 1148389 * 2 ^ 59
def prefixEnd_1148389 : Nat := 4983230072969 + 3 ^ 40 * 1148389 * 2
def baseEnd_1148389 : Nat := 262078015704983402869405

theorem tailTrace_1148389 : CollatzResearch.WordTrace tailWord_1148389 prefixEnd_1148389 262078015704983402869405 := by
  unfold tailWord_1148389
  simp only [CollatzResearch.WordTrace]
  refine ⟨41885187836590257071664221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27923458557726838047776147 41885187836590257071664221)
  ·
    refine ⟨15706945438721346401874083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41885187836590257071664221 15706945438721346401874083)
    ·
      refine ⟨23560418158082019602811125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15706945438721346401874083 23560418158082019602811125)
      ·
        refine ⟨2208789202320189337763543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23560418158082019602811125 2208789202320189337763543)
        ·
          refine ⟨3313183803480284006645315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208789202320189337763543 3313183803480284006645315)
          ·
            refine ⟨4969775705220426009967973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313183803480284006645315 4969775705220426009967973)
            ·
              refine ⟨931832944728829876868995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4969775705220426009967973 931832944728829876868995)
              ·
                refine ⟨1397749417093244815303493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931832944728829876868995 1397749417093244815303493)
                ·
                  refine ⟨262078015704983402869405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1397749417093244815303493 262078015704983402869405)
                  ·
                    rfl

theorem cell21_1148389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_1148389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148389 prefixEnd_1148389 := by exact prefixLift 1148389
  have htrace : WordTrace (prefixWord ++ tailWord_1148389) baseStart_1148389 baseEnd_1148389 := by
    simpa [prefixWord, tailWord_1148389, baseEnd_1148389] using wordTrace_append hprefix tailTrace_1148389
  have hstable : (prefixWord ++ tailWord_1148389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148389).length < 2 ^ (prefixWord ++ tailWord_1148389).sum := by decide
  have hdescent : baseEnd_1148389 < baseStart_1148389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148448 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_1148448 : Nat := 118140960795 + 1148448 * 2 ^ 59
def prefixEnd_1148448 : Nat := 4983230072969 + 3 ^ 40 * 1148448 * 2
def baseEnd_1148448 : Nat := 262091480308812411385951

theorem tailTrace_1148448 : CollatzResearch.WordTrace tailWord_1148448 prefixEnd_1148448 262091480308812411385951 := by
  unfold tailWord_1148448
  simp only [CollatzResearch.WordTrace]
  refine ⟨20943669871688255074030999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27924893162251006765374665 20943669871688255074030999)
  ·
    refine ⟨31415504807532382611046499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20943669871688255074030999 31415504807532382611046499)
    ·
      refine ⟨47123257211298573916569749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31415504807532382611046499 47123257211298573916569749)
      ·
        refine ⟨2208902681779620652339207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47123257211298573916569749 2208902681779620652339207)
        ·
          refine ⟨3313354022669430978508811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208902681779620652339207 3313354022669430978508811)
          ·
            refine ⟨4970031034004146467763217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313354022669430978508811 4970031034004146467763217)
            ·
              refine ⟨3727523275503109850822413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4970031034004146467763217 3727523275503109850822413)
              ·
                refine ⟨1397821228313666194058405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3727523275503109850822413 1397821228313666194058405)
                ·
                  refine ⟨262091480308812411385951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1397821228313666194058405 262091480308812411385951)
                  ·
                    rfl

theorem cell21_1148448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_1148448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148448 prefixEnd_1148448 := by exact prefixLift 1148448
  have htrace : WordTrace (prefixWord ++ tailWord_1148448) baseStart_1148448 baseEnd_1148448 := by
    simpa [prefixWord, tailWord_1148448, baseEnd_1148448] using wordTrace_append hprefix tailTrace_1148448
  have hstable : (prefixWord ++ tailWord_1148448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148448).length < 2 ^ (prefixWord ++ tailWord_1148448).sum := by decide
  have hdescent : baseEnd_1148448 < baseStart_1148448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148597 : List Nat := [1, 3, 3, 3, 11]
def baseStart_1148597 : Nat := 118140960795 + 1148597 * 2 ^ 59
def prefixEnd_1148597 : Nat := 4983230072969 + 3 ^ 40 * 1148597 * 2
def baseEnd_1148597 : Nat := 3236117088133595844473

theorem tailTrace_1148597 : CollatzResearch.WordTrace tailWord_1148597 prefixEnd_1148597 3236117088133595844473 := by
  unfold tailWord_1148597
  simp only [CollatzResearch.WordTrace]
  refine ⟨41892774219836708595236045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27928516146557805730157363 41892774219836708595236045)
  ·
    refine ⟨15709790332438765723213517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41892774219836708595236045 15709790332438765723213517)
    ·
      refine ⟨5891171374664537146205069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15709790332438765723213517 5891171374664537146205069)
      ·
        refine ⟨2209189265499201429826901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5891171374664537146205069 2209189265499201429826901)
        ·
          refine ⟨3236117088133595844473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2209189265499201429826901 3236117088133595844473)
          ·
            rfl

theorem cell21_1148597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 11].length) (baseStart_1148597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148597 prefixEnd_1148597 := by exact prefixLift 1148597
  have htrace : WordTrace (prefixWord ++ tailWord_1148597) baseStart_1148597 baseEnd_1148597 := by
    simpa [prefixWord, tailWord_1148597, baseEnd_1148597] using wordTrace_append hprefix tailTrace_1148597
  have hstable : (prefixWord ++ tailWord_1148597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148597).length < 2 ^ (prefixWord ++ tailWord_1148597).sum := by decide
  have hdescent : baseEnd_1148597 < baseStart_1148597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148611 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 11]
def baseStart_1148611 : Nat := 118140960795 + 1148611 * 2 ^ 59
def prefixEnd_1148611 : Nat := 4983230072969 + 3 ^ 40 * 1148611 * 2
def baseEnd_1148611 : Nat := 262128679129560350168951

theorem tailTrace_1148611 : CollatzResearch.WordTrace tailWord_1148611 prefixEnd_1148611 262128679129560350168951 := by
  unfold tailWord_1148611
  simp only [CollatzResearch.WordTrace]
  refine ⟨41893284841785988986245687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27928856561190659324163791 41893284841785988986245687)
  ·
    refine ⟨62839927262678983479368531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41893284841785988986245687 62839927262678983479368531)
    ·
      refine ⟨94259890894018475219052797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62839927262678983479368531 94259890894018475219052797)
      ·
        refine ⟨35347459085256928207144799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94259890894018475219052797 35347459085256928207144799)
        ·
          refine ⟨53021188627885392310717199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35347459085256928207144799 53021188627885392310717199)
          ·
            refine ⟨79531782941828088466075799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53021188627885392310717199 79531782941828088466075799)
            ·
              refine ⟨119297674412742132699113699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79531782941828088466075799 119297674412742132699113699)
              ·
                refine ⟨178946511619113199048670549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119297674412742132699113699 178946511619113199048670549)
                ·
                  refine ⟨262128679129560350168951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 178946511619113199048670549 262128679129560350168951)
                  ·
                    rfl

theorem cell21_1148611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_1148611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148611 prefixEnd_1148611 := by exact prefixLift 1148611
  have htrace : WordTrace (prefixWord ++ tailWord_1148611) baseStart_1148611 baseEnd_1148611 := by
    simpa [prefixWord, tailWord_1148611, baseEnd_1148611] using wordTrace_append hprefix tailTrace_1148611
  have hstable : (prefixWord ++ tailWord_1148611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148611).length < 2 ^ (prefixWord ++ tailWord_1148611).sum := by decide
  have hdescent : baseEnd_1148611 < baseStart_1148611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148659 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 4]
def baseStart_1148659 : Nat := 118140960795 + 1148659 * 2 ^ 59
def prefixEnd_1148659 : Nat := 4983230072969 + 3 ^ 40 * 1148659 * 2
def baseEnd_1148659 : Nat := 262139633383522933368853

theorem tailTrace_1148659 : CollatzResearch.WordTrace tailWord_1148659 prefixEnd_1148659 262139633383522933368853 := by
  unfold tailWord_1148659
  simp only [CollatzResearch.WordTrace]
  refine ⟨41895035545612093183993031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27930023697074728789328687 41895035545612093183993031)
  ·
    refine ⟨62842553318418139775989547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41895035545612093183993031 62842553318418139775989547)
    ·
      refine ⟨94263829977627209663984321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62842553318418139775989547 94263829977627209663984321)
      ·
        refine ⟨70697872483220407247988241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94263829977627209663984321 70697872483220407247988241)
        ·
          refine ⟨53023404362415305435991181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70697872483220407247988241 53023404362415305435991181)
          ·
            refine ⟨19883776635905739538496693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53023404362415305435991181 19883776635905739538496693)
            ·
              refine ⟨1864104059616163081734065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19883776635905739538496693 1864104059616163081734065)
              ·
                refine ⟨1398078044712122311300549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864104059616163081734065 1398078044712122311300549)
                ·
                  refine ⟨262139633383522933368853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398078044712122311300549 262139633383522933368853)
                  ·
                    rfl

theorem cell21_1148659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 4].length) (baseStart_1148659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148659 prefixEnd_1148659 := by exact prefixLift 1148659
  have htrace : WordTrace (prefixWord ++ tailWord_1148659) baseStart_1148659 baseEnd_1148659 := by
    simpa [prefixWord, tailWord_1148659, baseEnd_1148659] using wordTrace_append hprefix tailTrace_1148659
  have hstable : (prefixWord ++ tailWord_1148659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148659).length < 2 ^ (prefixWord ++ tailWord_1148659).sum := by decide
  have hdescent : baseEnd_1148659 < baseStart_1148659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148662 : List Nat := [5, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_1148662 : Nat := 118140960795 + 1148662 * 2 ^ 59
def prefixEnd_1148662 : Nat := 4983230072969 + 3 ^ 40 * 1148662 * 2
def baseEnd_1148662 : Nat := 262140318024395594818847

theorem tailTrace_1148662 : CollatzResearch.WordTrace tailWord_1148662 prefixEnd_1148662 262140318024395594818847 := by
  unfold tailWord_1148662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618446560287576543522015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27930096643067483130901493 2618446560287576543522015)
  ·
    refine ⟨3927669840431364815283023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2618446560287576543522015 3927669840431364815283023)
    ·
      refine ⟨5891504760647047222924535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3927669840431364815283023 5891504760647047222924535)
      ·
        refine ⟨8837257140970570834386803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5891504760647047222924535 8837257140970570834386803)
        ·
          refine ⟨13255885711455856251580205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8837257140970570834386803 13255885711455856251580205)
          ·
            refine ⟨4970957141795946094342577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13255885711455856251580205 4970957141795946094342577)
            ·
              refine ⟨3728217856346959570756933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4970957141795946094342577 3728217856346959570756933)
              ·
                refine ⟨699040848065054919516925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3728217856346959570756933 699040848065054919516925)
                ·
                  refine ⟨262140318024395594818847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 699040848065054919516925 262140318024395594818847)
                  ·
                    rfl

theorem cell21_1148662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_1148662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148662 prefixEnd_1148662 := by exact prefixLift 1148662
  have htrace : WordTrace (prefixWord ++ tailWord_1148662) baseStart_1148662 baseEnd_1148662 := by
    simpa [prefixWord, tailWord_1148662, baseEnd_1148662] using wordTrace_append hprefix tailTrace_1148662
  have hstable : (prefixWord ++ tailWord_1148662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148662).length < 2 ^ (prefixWord ++ tailWord_1148662).sum := by decide
  have hdescent : baseEnd_1148662 < baseStart_1148662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148687 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 7]
def baseStart_1148687 : Nat := 118140960795 + 1148687 * 2 ^ 59
def prefixEnd_1148687 : Nat := 4983230072969 + 3 ^ 40 * 1148687 * 2
def baseEnd_1148687 : Nat := 262146023365001106902129

theorem tailTrace_1148687 : CollatzResearch.WordTrace tailWord_1148687 prefixEnd_1148687 262146023365001106902129 := by
  unfold tailWord_1148687
  simp only [CollatzResearch.WordTrace]
  refine ⟨41896056789510653966012315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27930704526340435977341543 41896056789510653966012315)
  ·
    refine ⟨62844085184265980949018473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41896056789510653966012315 62844085184265980949018473)
    ·
      refine ⟨47133063888199485711763855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62844085184265980949018473 47133063888199485711763855)
      ·
        refine ⟨70699595832299228567645783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47133063888199485711763855 70699595832299228567645783)
        ·
          refine ⟨106049393748448842851468675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70699595832299228567645783 106049393748448842851468675)
          ·
            refine ⟨159074090622673264277203013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106049393748448842851468675 159074090622673264277203013)
            ·
              refine ⟨29826391991751237051975565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159074090622673264277203013 29826391991751237051975565)
              ·
                refine ⟨11184896996906713894490837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29826391991751237051975565 11184896996906713894490837)
                ·
                  refine ⟨262146023365001106902129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11184896996906713894490837 262146023365001106902129)
                  ·
                    rfl

theorem cell21_1148687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_1148687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148687 prefixEnd_1148687 := by exact prefixLift 1148687
  have htrace : WordTrace (prefixWord ++ tailWord_1148687) baseStart_1148687 baseEnd_1148687 := by
    simpa [prefixWord, tailWord_1148687, baseEnd_1148687] using wordTrace_append hprefix tailTrace_1148687
  have hstable : (prefixWord ++ tailWord_1148687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148687).length < 2 ^ (prefixWord ++ tailWord_1148687).sum := by decide
  have hdescent : baseEnd_1148687 < baseStart_1148687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148721 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 5]
def baseStart_1148721 : Nat := 118140960795 + 1148721 * 2 ^ 59
def prefixEnd_1148721 : Nat := 4983230072969 + 3 ^ 40 * 1148721 * 2
def baseEnd_1148721 : Nat := 262153782628224603335393

theorem tailTrace_1148721 : CollatzResearch.WordTrace tailWord_1148721 prefixEnd_1148721 262153782628224603335393 := by
  unfold tailWord_1148721
  simp only [CollatzResearch.WordTrace]
  refine ⟨41897296871387477772750017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27931531247591651848500011 41897296871387477772750017)
  ·
    refine ⟨31422972653540608329562513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41897296871387477772750017 31422972653540608329562513)
    ·
      refine ⟨23567229490155456247171885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31422972653540608329562513 23567229490155456247171885)
      ·
        refine ⟨8837711058808296092689457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23567229490155456247171885 8837711058808296092689457)
        ·
          refine ⟨6628283294106222069517093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8837711058808296092689457 6628283294106222069517093)
          ·
            refine ⟨1242803117644916638034455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6628283294106222069517093 1242803117644916638034455)
            ·
              refine ⟨1864204676467374957051683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242803117644916638034455 1864204676467374957051683)
              ·
                refine ⟨2796307014701062435577525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864204676467374957051683 2796307014701062435577525)
                ·
                  refine ⟨262153782628224603335393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2796307014701062435577525 262153782628224603335393)
                  ·
                    rfl

theorem cell21_1148721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_1148721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148721 prefixEnd_1148721 := by exact prefixLift 1148721
  have htrace : WordTrace (prefixWord ++ tailWord_1148721) baseStart_1148721 baseEnd_1148721 := by
    simpa [prefixWord, tailWord_1148721, baseEnd_1148721] using wordTrace_append hprefix tailTrace_1148721
  have hstable : (prefixWord ++ tailWord_1148721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148721).length < 2 ^ (prefixWord ++ tailWord_1148721).sum := by decide
  have hdescent : baseEnd_1148721 < baseStart_1148721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148772 : List Nat := [2, 3, 1, 1, 6, 1, 2, 2, 3]
def baseStart_1148772 : Nat := 118140960795 + 1148772 * 2 ^ 59
def prefixEnd_1148772 : Nat := 4983230072969 + 3 ^ 40 * 1148772 * 2
def baseEnd_1148772 : Nat := 262165421523059847985289

theorem tailTrace_1148772 : CollatzResearch.WordTrace tailWord_1148772 prefixEnd_1148772 262165421523059847985289 := by
  unfold tailWord_1148772
  simp only [CollatzResearch.WordTrace]
  refine ⟨20949578497101356741428285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27932771329468475655237713 20949578497101356741428285)
  ·
    refine ⟨7856091936413008778035607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20949578497101356741428285 7856091936413008778035607)
    ·
      refine ⟨11784137904619513167053411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7856091936413008778035607 11784137904619513167053411)
      ·
        refine ⟨17676206856929269750580117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11784137904619513167053411 17676206856929269750580117)
        ·
          refine ⟨828572196418559519558443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17676206856929269750580117 828572196418559519558443)
          ·
            refine ⟨1242858294627839279337665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828572196418559519558443 1242858294627839279337665)
            ·
              refine ⟨932143720970879459503249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1242858294627839279337665 932143720970879459503249)
              ·
                refine ⟨699107790728159594627437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932143720970879459503249 699107790728159594627437)
                ·
                  refine ⟨262165421523059847985289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 699107790728159594627437 262165421523059847985289)
                  ·
                    rfl

theorem cell21_1148772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_1148772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148772 prefixEnd_1148772 := by exact prefixLift 1148772
  have htrace : WordTrace (prefixWord ++ tailWord_1148772) baseStart_1148772 baseEnd_1148772 := by
    simpa [prefixWord, tailWord_1148772, baseEnd_1148772] using wordTrace_append hprefix tailTrace_1148772
  have hstable : (prefixWord ++ tailWord_1148772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148772).length < 2 ^ (prefixWord ++ tailWord_1148772).sum := by decide
  have hdescent : baseEnd_1148772 < baseStart_1148772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148828 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_1148828 : Nat := 118140960795 + 1148828 * 2 ^ 59
def prefixEnd_1148828 : Nat := 4983230072969 + 3 ^ 40 * 1148828 * 2
def baseEnd_1148828 : Nat := 262178201486016195051841

theorem tailTrace_1148828 : CollatzResearch.WordTrace tailWord_1148828 prefixEnd_1148828 262178201486016195051841 := by
  unfold tailWord_1148828
  simp only [CollatzResearch.WordTrace]
  refine ⟨20950599740999917523447569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27934132987999890031263425 20950599740999917523447569)
  ·
    refine ⟨15712949805749938142585677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20950599740999917523447569 15712949805749938142585677)
    ·
      refine ⟨5892356177156226803469629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15712949805749938142585677 5892356177156226803469629)
      ·
        refine ⟨2209633566433585051301111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5892356177156226803469629 2209633566433585051301111)
        ·
          refine ⟨3314450349650377576951667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2209633566433585051301111 3314450349650377576951667)
          ·
            refine ⟨4971675524475566365427501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3314450349650377576951667 4971675524475566365427501)
            ·
              refine ⟨1864378321678337387035313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4971675524475566365427501 1864378321678337387035313)
              ·
                refine ⟨1398283741258753040276485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864378321678337387035313 1398283741258753040276485)
                ·
                  refine ⟨262178201486016195051841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398283741258753040276485 262178201486016195051841)
                  ·
                    rfl

theorem cell21_1148828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_1148828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148828 prefixEnd_1148828 := by exact prefixLift 1148828
  have htrace : WordTrace (prefixWord ++ tailWord_1148828) baseStart_1148828 baseEnd_1148828 := by
    simpa [prefixWord, tailWord_1148828, baseEnd_1148828] using wordTrace_append hprefix tailTrace_1148828
  have hstable : (prefixWord ++ tailWord_1148828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148828).length < 2 ^ (prefixWord ++ tailWord_1148828).sum := by decide
  have hdescent : baseEnd_1148828 < baseStart_1148828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148890 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 5]
def baseStart_1148890 : Nat := 118140960795 + 1148890 * 2 ^ 59
def prefixEnd_1148890 : Nat := 4983230072969 + 3 ^ 40 * 1148890 * 2
def baseEnd_1148890 : Nat := 262192350730717865018381

theorem tailTrace_1148890 : CollatzResearch.WordTrace tailWord_1148890 prefixEnd_1148890 262192350730717865018381 := by
  unfold tailWord_1148890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475865201943804908913031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27935640538516813090434749 10475865201943804908913031)
  ·
    refine ⟨15713797802915707363369547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10475865201943804908913031 15713797802915707363369547)
    ·
      refine ⟨23570696704373561045054321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15713797802915707363369547 23570696704373561045054321)
      ·
        refine ⟨17678022528280170783790741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23570696704373561045054321 17678022528280170783790741)
        ·
          refine ⟨828657306013133005490191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17678022528280170783790741 828657306013133005490191)
          ·
            refine ⟨1242985959019699508235287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828657306013133005490191 1242985959019699508235287)
            ·
              refine ⟨1864478938529549262352931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242985959019699508235287 1864478938529549262352931)
              ·
                refine ⟨2796718407794323893529397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864478938529549262352931 2796718407794323893529397)
                ·
                  refine ⟨262192350730717865018381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2796718407794323893529397 262192350730717865018381)
                  ·
                    rfl

theorem cell21_1148890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_1148890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148890 prefixEnd_1148890 := by exact prefixLift 1148890
  have htrace : WordTrace (prefixWord ++ tailWord_1148890) baseStart_1148890 baseEnd_1148890 := by
    simpa [prefixWord, tailWord_1148890, baseEnd_1148890] using wordTrace_append hprefix tailTrace_1148890
  have hstable : (prefixWord ++ tailWord_1148890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148890).length < 2 ^ (prefixWord ++ tailWord_1148890).sum := by decide
  have hdescent : baseEnd_1148890 < baseStart_1148890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148915 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 5]
def baseStart_1148915 : Nat := 118140960795 + 1148915 * 2 ^ 59
def prefixEnd_1148915 : Nat := 4983230072969 + 3 ^ 40 * 1148915 * 2
def baseEnd_1148915 : Nat := 262198056071323377101663

theorem tailTrace_1148915 : CollatzResearch.WordTrace tailWord_1148915 prefixEnd_1148915 262198056071323377101663 := by
  unfold tailWord_1148915
  simp only [CollatzResearch.WordTrace]
  refine ⟨41904372632684648905312199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27936248421789765936874799 41904372632684648905312199)
  ·
    refine ⟨62856558949026973357968299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41904372632684648905312199 62856558949026973357968299)
    ·
      refine ⟨94284838423540460036952449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62856558949026973357968299 94284838423540460036952449)
      ·
        refine ⟨70713628817655345027714337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94284838423540460036952449 70713628817655345027714337)
        ·
          refine ⟨53035221613241508770785753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70713628817655345027714337 53035221613241508770785753)
          ·
            refine ⟨39776416209931131578089315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53035221613241508770785753 39776416209931131578089315)
            ·
              refine ⟨59664624314896697367133973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39776416209931131578089315 59664624314896697367133973)
              ·
                refine ⟨2796779264760782689084405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59664624314896697367133973 2796779264760782689084405)
                ·
                  refine ⟨262198056071323377101663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2796779264760782689084405 262198056071323377101663)
                  ·
                    rfl

theorem cell21_1148915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_1148915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1148915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1148915 prefixEnd_1148915 := by exact prefixLift 1148915
  have htrace : WordTrace (prefixWord ++ tailWord_1148915) baseStart_1148915 baseEnd_1148915 := by
    simpa [prefixWord, tailWord_1148915, baseEnd_1148915] using wordTrace_append hprefix tailTrace_1148915
  have hstable : (prefixWord ++ tailWord_1148915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148915).length < 2 ^ (prefixWord ++ tailWord_1148915).sum := by decide
  have hdescent : baseEnd_1148915 < baseStart_1148915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149014 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1149014 : Nat := 118140960795 + 1149014 * 2 ^ 59
def prefixEnd_1149014 : Nat := 4983230072969 + 3 ^ 40 * 1149014 * 2
def baseEnd_1149014 : Nat := 262220649220121204951461

theorem tailTrace_1149014 : CollatzResearch.WordTrace tailWord_1149014 prefixEnd_1149014 262220649220121204951461 := by
  unfold tailWord_1149014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2619248966207874300822881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27938655639550659208777397 2619248966207874300822881)
  ·
    refine ⟨1964436724655905725617161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2619248966207874300822881 1964436724655905725617161)
    ·
      refine ⟨1473327543491929294212871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1964436724655905725617161 1473327543491929294212871)
      ·
        refine ⟨2209991315237893941319307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1473327543491929294212871 2209991315237893941319307)
        ·
          refine ⟨3314986972856840911978961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2209991315237893941319307 3314986972856840911978961)
          ·
            refine ⟨2486240229642630683984221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3314986972856840911978961 2486240229642630683984221)
            ·
              refine ⟨932340086115986506494083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2486240229642630683984221 932340086115986506494083)
              ·
                refine ⟨1398510129173979759741125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932340086115986506494083 1398510129173979759741125)
                ·
                  refine ⟨262220649220121204951461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398510129173979759741125 262220649220121204951461)
                  ·
                    rfl

theorem cell21_1149014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1149014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149014 prefixEnd_1149014 := by exact prefixLift 1149014
  have htrace : WordTrace (prefixWord ++ tailWord_1149014) baseStart_1149014 baseEnd_1149014 := by
    simpa [prefixWord, tailWord_1149014, baseEnd_1149014] using wordTrace_append hprefix tailTrace_1149014
  have hstable : (prefixWord ++ tailWord_1149014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149014).length < 2 ^ (prefixWord ++ tailWord_1149014).sum := by decide
  have hdescent : baseEnd_1149014 < baseStart_1149014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149042 : List Nat := [3, 2, 1, 2, 2, 4, 1, 3, 3]
def baseStart_1149042 : Nat := 118140960795 + 1149042 * 2 ^ 59
def prefixEnd_1149042 : Nat := 4983230072969 + 3 ^ 40 * 1149042 * 2
def baseEnd_1149042 : Nat := 262227039201599378484737

theorem tailTrace_1149042 : CollatzResearch.WordTrace tailWord_1149042 prefixEnd_1149042 262227039201599378484737 := by
  unfold tailWord_1149042
  simp only [CollatzResearch.WordTrace]
  refine ⟨10477251175806137398796345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27939336468816366396790253 10477251175806137398796345)
  ·
    refine ⟨7857938381854603049097259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10477251175806137398796345 7857938381854603049097259)
    ·
      refine ⟨11786907572781904573645889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7857938381854603049097259 11786907572781904573645889)
      ·
        refine ⟨8840180679586428430234417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11786907572781904573645889 8840180679586428430234417)
        ·
          refine ⟨6630135509689821322675813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8840180679586428430234417 6630135509689821322675813)
          ·
            refine ⟨1243150408066841498001715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6630135509689821322675813 1243150408066841498001715)
            ·
              refine ⟨1864725612100262247002573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243150408066841498001715 1864725612100262247002573)
              ·
                refine ⟨699272104537598342625965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1864725612100262247002573 699272104537598342625965)
                ·
                  refine ⟨262227039201599378484737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 699272104537598342625965 262227039201599378484737)
                  ·
                    rfl

theorem cell21_1149042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_1149042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149042 prefixEnd_1149042 := by exact prefixLift 1149042
  have htrace : WordTrace (prefixWord ++ tailWord_1149042) baseStart_1149042 baseEnd_1149042 := by
    simpa [prefixWord, tailWord_1149042, baseEnd_1149042] using wordTrace_append hprefix tailTrace_1149042
  have hstable : (prefixWord ++ tailWord_1149042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149042).length < 2 ^ (prefixWord ++ tailWord_1149042).sum := by decide
  have hdescent : baseEnd_1149042 < baseStart_1149042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149053 : List Nat := [1, 4, 1, 1, 3, 4, 7]
def baseStart_1149053 : Nat := 118140960795 + 1149053 * 2 ^ 59
def prefixEnd_1149053 : Nat := 4983230072969 + 3 ^ 40 * 1149053 * 2
def baseEnd_1149053 : Nat := 29136616616829533755709

theorem tailTrace_1149053 : CollatzResearch.WordTrace tailWord_1149053 prefixEnd_1149053 29136616616829533755709 := by
  unfold tailWord_1149053
  simp only [CollatzResearch.WordTrace]
  refine ⟨41909405906184698473835813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27939603937456465649223875 41909405906184698473835813)
  ·
    refine ⟨7858013607409630963844215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41909405906184698473835813 7858013607409630963844215)
    ·
      refine ⟨11787020411114446445766323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7858013607409630963844215 11787020411114446445766323)
      ·
        refine ⟨17680530616671669668649485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11787020411114446445766323 17680530616671669668649485)
        ·
          refine ⟨6630198981251876125743557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17680530616671669668649485 6630198981251876125743557)
          ·
            refine ⟨1243162308984726773576917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6630198981251876125743557 1243162308984726773576917)
            ·
              refine ⟨29136616616829533755709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1243162308984726773576917 29136616616829533755709)
              ·
                rfl

theorem cell21_1149053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 7].length) (baseStart_1149053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149053 prefixEnd_1149053 := by exact prefixLift 1149053
  have htrace : WordTrace (prefixWord ++ tailWord_1149053) baseStart_1149053 baseEnd_1149053 := by
    simpa [prefixWord, tailWord_1149053, baseEnd_1149053] using wordTrace_append hprefix tailTrace_1149053
  have hstable : (prefixWord ++ tailWord_1149053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149053).length < 2 ^ (prefixWord ++ tailWord_1149053).sum := by decide
  have hdescent : baseEnd_1149053 < baseStart_1149053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149070 : List Nat := [4, 1, 1, 3, 3, 1, 2, 6]
def baseStart_1149070 : Nat := 118140960795 + 1149070 * 2 ^ 59
def prefixEnd_1149070 : Nat := 4983230072969 + 3 ^ 40 * 1149070 * 2
def baseEnd_1149070 : Nat := 87411143061025850672671

theorem tailTrace_1149070 : CollatzResearch.WordTrace tailWord_1149070 prefixEnd_1149070 87411143061025850672671 := by
  unfold tailWord_1149070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5238753243390388797150583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27940017298082073584803109 5238753243390388797150583)
  ·
    refine ⟨7858129865085583195725875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5238753243390388797150583 7858129865085583195725875)
    ·
      refine ⟨11787194797628374793588813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7858129865085583195725875 11787194797628374793588813)
      ·
        refine ⟨4420198049110640547595805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11787194797628374793588813 4420198049110640547595805)
        ·
          refine ⟨1657574268416490205348427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4420198049110640547595805 1657574268416490205348427)
          ·
            refine ⟨2486361402624735308022641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657574268416490205348427 2486361402624735308022641)
            ·
              refine ⟨1864771051968551481016981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486361402624735308022641 1864771051968551481016981)
              ·
                refine ⟨87411143061025850672671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1864771051968551481016981 87411143061025850672671)
                ·
                  rfl

theorem cell21_1149070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_1149070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149070 prefixEnd_1149070 := by exact prefixLift 1149070
  have htrace : WordTrace (prefixWord ++ tailWord_1149070) baseStart_1149070 baseEnd_1149070 := by
    simpa [prefixWord, tailWord_1149070, baseEnd_1149070] using wordTrace_append hprefix tailTrace_1149070
  have hstable : (prefixWord ++ tailWord_1149070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149070).length < 2 ^ (prefixWord ++ tailWord_1149070).sum := by decide
  have hdescent : baseEnd_1149070 < baseStart_1149070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149118 : List Nat := [4, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_1149118 : Nat := 118140960795 + 1149118 * 2 ^ 59
def prefixEnd_1149118 : Nat := 4983230072969 + 3 ^ 40 * 1149118 * 2
def baseEnd_1149118 : Nat := 262244383437040135217915

theorem tailTrace_1149118 : CollatzResearch.WordTrace tailWord_1149118 prefixEnd_1149118 262244383437040135217915 := by
  unfold tailWord_1149118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5238972081368651821869001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27941184433966143049968005 5238972081368651821869001)
  ·
    refine ⟨3929229061026488866401751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5238972081368651821869001 3929229061026488866401751)
    ·
      refine ⟨5893843591539733299602627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3929229061026488866401751 5893843591539733299602627)
      ·
        refine ⟨8840765387309599949403941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5893843591539733299602627 8840765387309599949403941)
        ·
          refine ⟨1657643510120549990513239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8840765387309599949403941 1657643510120549990513239)
          ·
            refine ⟨2486465265180824985769859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657643510120549990513239 2486465265180824985769859)
            ·
              refine ⟨3729697897771237478654789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486465265180824985769859 3729697897771237478654789)
              ·
                refine ⟨699318355832107027247773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3729697897771237478654789 699318355832107027247773)
                ·
                  refine ⟨262244383437040135217915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 699318355832107027247773 262244383437040135217915)
                  ·
                    rfl

theorem cell21_1149118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_1149118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149118 prefixEnd_1149118 := by exact prefixLift 1149118
  have htrace : WordTrace (prefixWord ++ tailWord_1149118) baseStart_1149118 baseEnd_1149118 := by
    simpa [prefixWord, tailWord_1149118, baseEnd_1149118] using wordTrace_append hprefix tailTrace_1149118
  have hstable : (prefixWord ++ tailWord_1149118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149118).length < 2 ^ (prefixWord ++ tailWord_1149118).sum := by decide
  have hdescent : baseEnd_1149118 < baseStart_1149118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149205 : List Nat := [1, 3, 2, 1, 2, 1, 6, 5]
def baseStart_1149205 : Nat := 118140960795 + 1149205 * 2 ^ 59
def prefixEnd_1149205 : Nat := 4983230072969 + 3 ^ 40 * 1149205 * 2
def baseEnd_1149205 : Nat := 87421412674115772422579

theorem tailTrace_1149205 : CollatzResearch.WordTrace tailWord_1149205 prefixEnd_1149205 87421412674115772422579 := by
  unfold tailWord_1149205
  simp only [CollatzResearch.WordTrace]
  refine ⟨41914949801634028433369069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27943299867756018955579379 41914949801634028433369069)
  ·
    refine ⟨15718106175612760662513401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41914949801634028433369069 15718106175612760662513401)
    ·
      refine ⟨11788579631709570496885051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15718106175612760662513401 11788579631709570496885051)
      ·
        refine ⟨17682869447564355745327577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11788579631709570496885051 17682869447564355745327577)
        ·
          refine ⟨13262152085673266808995683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17682869447564355745327577 13262152085673266808995683)
          ·
            refine ⟨19893228128509900213493525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13262152085673266808995683 19893228128509900213493525)
            ·
              refine ⟨932495068523901572507509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19893228128509900213493525 932495068523901572507509)
              ·
                refine ⟨87421412674115772422579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 932495068523901572507509 87421412674115772422579)
                ·
                  rfl

theorem cell21_1149205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 5].length) (baseStart_1149205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149205 prefixEnd_1149205 := by exact prefixLift 1149205
  have htrace : WordTrace (prefixWord ++ tailWord_1149205) baseStart_1149205 baseEnd_1149205 := by
    simpa [prefixWord, tailWord_1149205, baseEnd_1149205] using wordTrace_append hprefix tailTrace_1149205
  have hstable : (prefixWord ++ tailWord_1149205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149205).length < 2 ^ (prefixWord ++ tailWord_1149205).sum := by decide
  have hdescent : baseEnd_1149205 < baseStart_1149205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149264 : List Nat := [2, 1, 1, 1, 1, 6, 2, 7]
def baseStart_1149264 : Nat := 118140960795 + 1149264 * 2 ^ 59
def prefixEnd_1149264 : Nat := 4983230072969 + 3 ^ 40 * 1149264 * 2
def baseEnd_1149264 : Nat := 87425900875392108594761

theorem tailTrace_1149264 : CollatzResearch.WordTrace tailWord_1149264 prefixEnd_1149264 87425900875392108594761 := by
  unfold tailWord_1149264
  simp only [CollatzResearch.WordTrace]
  refine ⟨20958550854210140754883423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27944734472280187673177897 20958550854210140754883423)
  ·
    refine ⟨31437826281315211132325135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20958550854210140754883423 31437826281315211132325135)
    ·
      refine ⟨47156739421972816698487703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31437826281315211132325135 47156739421972816698487703)
      ·
        refine ⟨70735109132959225047731555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47156739421972816698487703 70735109132959225047731555)
        ·
          refine ⟨106102663699438837571597333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70735109132959225047731555 106102663699438837571597333)
          ·
            refine ⟨4973562360911195511168625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106102663699438837571597333 4973562360911195511168625)
            ·
              refine ⟨3730171770683396633376469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4973562360911195511168625 3730171770683396633376469)
              ·
                refine ⟨87425900875392108594761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3730171770683396633376469 87425900875392108594761)
                ·
                  rfl

theorem cell21_1149264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_1149264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149264 prefixEnd_1149264 := by exact prefixLift 1149264
  have htrace : WordTrace (prefixWord ++ tailWord_1149264) baseStart_1149264 baseEnd_1149264 := by
    simpa [prefixWord, tailWord_1149264, baseEnd_1149264] using wordTrace_append hprefix tailTrace_1149264
  have hstable : (prefixWord ++ tailWord_1149264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149264).length < 2 ^ (prefixWord ++ tailWord_1149264).sum := by decide
  have hdescent : baseEnd_1149264 < baseStart_1149264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149385 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 6]
def baseStart_1149385 : Nat := 118140960795 + 1149385 * 2 ^ 59
def prefixEnd_1149385 : Nat := 4983230072969 + 3 ^ 40 * 1149385 * 2
def baseEnd_1149385 : Nat := 262305316474707004267369

theorem tailTrace_1149385 : CollatzResearch.WordTrace tailWord_1149385 prefixEnd_1149385 262305316474707004267369 := by
  unfold tailWord_1149385
  simp only [CollatzResearch.WordTrace]
  refine ⟨41921514940981919174921609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27947676627321279449947739 41921514940981919174921609)
  ·
    refine ⟨31441136205736439381191207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41921514940981919174921609 31441136205736439381191207)
    ·
      refine ⟨47161704308604659071786811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31441136205736439381191207 47161704308604659071786811)
      ·
        refine ⟨70742556462906988607680217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47161704308604659071786811 70742556462906988607680217)
        ·
          refine ⟨53056917347180241455760163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70742556462906988607680217 53056917347180241455760163)
          ·
            refine ⟨79585376020770362183640245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53056917347180241455760163 79585376020770362183640245)
            ·
              refine ⟨7461129001947221454716273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79585376020770362183640245 7461129001947221454716273)
              ·
                refine ⟨5595846751460416091037205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7461129001947221454716273 5595846751460416091037205)
                ·
                  refine ⟨262305316474707004267369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5595846751460416091037205 262305316474707004267369)
                  ·
                    rfl

theorem cell21_1149385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_1149385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149385 prefixEnd_1149385 := by exact prefixLift 1149385
  have htrace : WordTrace (prefixWord ++ tailWord_1149385) baseStart_1149385 baseEnd_1149385 := by
    simpa [prefixWord, tailWord_1149385, baseEnd_1149385] using wordTrace_append hprefix tailTrace_1149385
  have hstable : (prefixWord ++ tailWord_1149385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149385).length < 2 ^ (prefixWord ++ tailWord_1149385).sum := by decide
  have hdescent : baseEnd_1149385 < baseStart_1149385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149402 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_1149402 : Nat := 118140960795 + 1149402 * 2 ^ 59
def prefixEnd_1149402 : Nat := 4983230072969 + 3 ^ 40 * 1149402 * 2
def baseEnd_1149402 : Nat := 262309196106318752484001

theorem tailTrace_1149402 : CollatzResearch.WordTrace tailWord_1149402 prefixEnd_1149402 262309196106318752484001 := by
  unfold tailWord_1149402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10480533745480082769572615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27948089987946887385526973 10480533745480082769572615)
  ·
    refine ⟨15720800618220124154358923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10480533745480082769572615 15720800618220124154358923)
    ·
      refine ⟨23581200927330186231538385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15720800618220124154358923 23581200927330186231538385)
      ·
        refine ⟨17685900695497639673653789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23581200927330186231538385 17685900695497639673653789)
        ·
          refine ⟨6632212760811614877620171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17685900695497639673653789 6632212760811614877620171)
          ·
            refine ⟨9948319141217422316430257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6632212760811614877620171 9948319141217422316430257)
            ·
              refine ⟨7461239355913066737322693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9948319141217422316430257 7461239355913066737322693)
              ·
                refine ⟨1398982379233700013248005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7461239355913066737322693 1398982379233700013248005)
                ·
                  refine ⟨262309196106318752484001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398982379233700013248005 262309196106318752484001)
                  ·
                    rfl

theorem cell21_1149402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_1149402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149402 prefixEnd_1149402 := by exact prefixLift 1149402
  have htrace : WordTrace (prefixWord ++ tailWord_1149402) baseStart_1149402 baseEnd_1149402 := by
    simpa [prefixWord, tailWord_1149402, baseEnd_1149402] using wordTrace_append hprefix tailTrace_1149402
  have hstable : (prefixWord ++ tailWord_1149402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149402).length < 2 ^ (prefixWord ++ tailWord_1149402).sum := by decide
  have hdescent : baseEnd_1149402 < baseStart_1149402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149416 : List Nat := [2, 1, 4, 1, 1, 3, 1, 8]
def baseStart_1149416 : Nat := 118140960795 + 1149416 * 2 ^ 59
def prefixEnd_1149416 : Nat := 4983230072969 + 3 ^ 40 * 1149416 * 2
def baseEnd_1149416 : Nat := 87437463699019279750213

theorem tailTrace_1149416 : CollatzResearch.WordTrace tailWord_1149416 prefixEnd_1149416 87437463699019279750213 := by
  unfold tailWord_1149416
  simp only [CollatzResearch.WordTrace]
  refine ⟨20961322801934805734650051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27948430402579740979533401 20961322801934805734650051)
  ·
    refine ⟨31441984202902208601975077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20961322801934805734650051 31441984202902208601975077)
    ·
      refine ⟨5895372038044164112870327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31441984202902208601975077 5895372038044164112870327)
      ·
        refine ⟨8843058057066246169305491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5895372038044164112870327 8843058057066246169305491)
        ·
          refine ⟨13264587085599369253958237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8843058057066246169305491 13264587085599369253958237)
          ·
            refine ⟨4974220157099763470234339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13264587085599369253958237 4974220157099763470234339)
            ·
              refine ⟨7461330235649645205351509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4974220157099763470234339 7461330235649645205351509)
              ·
                refine ⟨87437463699019279750213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7461330235649645205351509 87437463699019279750213)
                ·
                  rfl

theorem cell21_1149416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_1149416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149416 prefixEnd_1149416 := by exact prefixLift 1149416
  have htrace : WordTrace (prefixWord ++ tailWord_1149416) baseStart_1149416 baseEnd_1149416 := by
    simpa [prefixWord, tailWord_1149416, baseEnd_1149416] using wordTrace_append hprefix tailTrace_1149416
  have hstable : (prefixWord ++ tailWord_1149416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149416).length < 2 ^ (prefixWord ++ tailWord_1149416).sum := by decide
  have hdescent : baseEnd_1149416 < baseStart_1149416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149453 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1149453 : Nat := 118140960795 + 1149453 * 2 ^ 59
def prefixEnd_1149453 : Nat := 4983230072969 + 3 ^ 40 * 1149453 * 2
def baseEnd_1149453 : Nat := 262320835001153997133897

theorem tailTrace_1149453 : CollatzResearch.WordTrace tailWord_1149453 prefixEnd_1149453 262320835001153997133897 := by
  unfold tailWord_1149453
  simp only [CollatzResearch.WordTrace]
  refine ⟨41923995104735566788397013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27949330069823711192264675 41923995104735566788397013)
  ·
    refine ⟨982593635267239846603055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 41923995104735566788397013 982593635267239846603055)
    ·
      refine ⟨1473890452900859769904583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982593635267239846603055 1473890452900859769904583)
      ·
        refine ⟨2210835679351289654856875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1473890452900859769904583 2210835679351289654856875)
        ·
          refine ⟨3316253519026934482285313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2210835679351289654856875 3316253519026934482285313)
          ·
            refine ⟨2487190139270200861713985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3316253519026934482285313 2487190139270200861713985)
            ·
              refine ⟨1865392604452650646285489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2487190139270200861713985 1865392604452650646285489)
              ·
                refine ⟨1399044453339487984714117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1865392604452650646285489 1399044453339487984714117)
                ·
                  refine ⟨262320835001153997133897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399044453339487984714117 262320835001153997133897)
                  ·
                    rfl

theorem cell21_1149453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1149453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149453 prefixEnd_1149453 := by exact prefixLift 1149453
  have htrace : WordTrace (prefixWord ++ tailWord_1149453) baseStart_1149453 baseEnd_1149453 := by
    simpa [prefixWord, tailWord_1149453, baseEnd_1149453] using wordTrace_append hprefix tailTrace_1149453
  have hstable : (prefixWord ++ tailWord_1149453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149453).length < 2 ^ (prefixWord ++ tailWord_1149453).sum := by decide
  have hdescent : baseEnd_1149453 < baseStart_1149453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149568 : List Nat := [2, 1, 1, 2, 1, 7, 7]
def baseStart_1149568 : Nat := 118140960795 + 1149568 * 2 ^ 59
def prefixEnd_1149568 : Nat := 4983230072969 + 3 ^ 40 * 1149568 * 2
def baseEnd_1149568 : Nat := 29149675507548816968555

theorem tailTrace_1149568 : CollatzResearch.WordTrace tailWord_1149568 prefixEnd_1149568 29149675507548816968555 := by
  unfold tailWord_1149568
  simp only [CollatzResearch.WordTrace]
  refine ⟨20964094749659470714416679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27952126332879294285888905 20964094749659470714416679)
  ·
    refine ⟨31446142124489206071625019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20964094749659470714416679 31446142124489206071625019)
    ·
      refine ⟨47169213186733809107437529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31446142124489206071625019 47169213186733809107437529)
      ·
        refine ⟨35376909890050356830578147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47169213186733809107437529 35376909890050356830578147)
        ·
          refine ⟨53065364835075535245867221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35376909890050356830578147 53065364835075535245867221)
          ·
            refine ⟨1243719488322082857325013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53065364835075535245867221 1243719488322082857325013)
            ·
              refine ⟨29149675507548816968555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1243719488322082857325013 29149675507548816968555)
              ·
                rfl

theorem cell21_1149568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 7].length) (baseStart_1149568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149568 prefixEnd_1149568 := by exact prefixLift 1149568
  have htrace : WordTrace (prefixWord ++ tailWord_1149568) baseStart_1149568 baseEnd_1149568 := by
    simpa [prefixWord, tailWord_1149568, baseEnd_1149568] using wordTrace_append hprefix tailTrace_1149568
  have hstable : (prefixWord ++ tailWord_1149568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149568).length < 2 ^ (prefixWord ++ tailWord_1149568).sum := by decide
  have hdescent : baseEnd_1149568 < baseStart_1149568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149588 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1149588 : Nat := 118140960795 + 1149588 * 2 ^ 59
def prefixEnd_1149588 : Nat := 4983230072969 + 3 ^ 40 * 1149588 * 2
def baseEnd_1149588 : Nat := 262351643840423762383621

theorem tailTrace_1149588 : CollatzResearch.WordTrace tailWord_1149588 prefixEnd_1149588 262351643840423762383621 := by
  unfold tailWord_1149588
  simp only [CollatzResearch.WordTrace]
  refine ⟨20964459479623242422280709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27952612639497656563040945 20964459479623242422280709)
  ·
    refine ⟨3930836152429357954177633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20964459479623242422280709 3930836152429357954177633)
    ·
      refine ⟨2948127114322018465633225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3930836152429357954177633 2948127114322018465633225)
      ·
        refine ⟨2211095335741513849224919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2948127114322018465633225 2211095335741513849224919)
        ·
          refine ⟨3316643003612270773837379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2211095335741513849224919 3316643003612270773837379)
          ·
            refine ⟨4974964505418406160756069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316643003612270773837379 4974964505418406160756069)
            ·
              refine ⟨932805844765951155141763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4974964505418406160756069 932805844765951155141763)
              ·
                refine ⟨1399208767148926732712645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932805844765951155141763 1399208767148926732712645)
                ·
                  refine ⟨262351643840423762383621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399208767148926732712645 262351643840423762383621)
                  ·
                    rfl

theorem cell21_1149588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1149588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149588 prefixEnd_1149588 := by exact prefixLift 1149588
  have htrace : WordTrace (prefixWord ++ tailWord_1149588) baseStart_1149588 baseEnd_1149588 := by
    simpa [prefixWord, tailWord_1149588, baseEnd_1149588] using wordTrace_append hprefix tailTrace_1149588
  have hstable : (prefixWord ++ tailWord_1149588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149588).length < 2 ^ (prefixWord ++ tailWord_1149588).sum := by decide
  have hdescent : baseEnd_1149588 < baseStart_1149588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149692 : List Nat := [2, 2, 2, 1, 3, 2, 2, 4, 3]
def baseStart_1149692 : Nat := 118140960795 + 1149692 * 2 ^ 59
def prefixEnd_1149692 : Nat := 4983230072969 + 3 ^ 40 * 1149692 * 2
def baseEnd_1149692 : Nat := 262375378057342692650075

theorem tailTrace_1149692 : CollatzResearch.WordTrace tailWord_1149692 prefixEnd_1149692 262375378057342692650075 := by
  unfold tailWord_1149692
  simp only [CollatzResearch.WordTrace]
  refine ⟨20966356075434855303173665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27955141433913140404231553 20966356075434855303173665)
  ·
    refine ⟨15724767056576141477380249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20966356075434855303173665 15724767056576141477380249)
    ·
      refine ⟨11793575292432106108035187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15724767056576141477380249 11793575292432106108035187)
      ·
        refine ⟨17690362938648159162052781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11793575292432106108035187 17690362938648159162052781)
        ·
          refine ⟨6633886101993059685769793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17690362938648159162052781 6633886101993059685769793)
          ·
            refine ⟨4975414576494794764327345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6633886101993059685769793 4975414576494794764327345)
            ·
              refine ⟨3731560932371096073245509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4975414576494794764327345 3731560932371096073245509)
              ·
                refine ⟨699667674819580513733533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3731560932371096073245509 699667674819580513733533)
                ·
                  refine ⟨262375378057342692650075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 699667674819580513733533 262375378057342692650075)
                  ·
                    rfl

theorem cell21_1149692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_1149692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149692 prefixEnd_1149692 := by exact prefixLift 1149692
  have htrace : WordTrace (prefixWord ++ tailWord_1149692) baseStart_1149692 baseEnd_1149692 := by
    simpa [prefixWord, tailWord_1149692, baseEnd_1149692] using wordTrace_append hprefix tailTrace_1149692
  have hstable : (prefixWord ++ tailWord_1149692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149692).length < 2 ^ (prefixWord ++ tailWord_1149692).sum := by decide
  have hdescent : baseEnd_1149692 < baseStart_1149692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149757 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 4]
def baseStart_1149757 : Nat := 118140960795 + 1149757 * 2 ^ 59
def prefixEnd_1149757 : Nat := 4983230072969 + 3 ^ 40 * 1149757 * 2
def baseEnd_1149757 : Nat := 262390211942917024066609

theorem tailTrace_1149757 : CollatzResearch.WordTrace tailWord_1149757 prefixEnd_1149757 262390211942917024066609 := by
  unfold tailWord_1149757
  simp only [CollatzResearch.WordTrace]
  refine ⟨41935082895634226707463525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27956721930422817804975683 41935082895634226707463525)
  ·
    refine ⟨7862828042931417507649411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41935082895634226707463525 7862828042931417507649411)
    ·
      refine ⟨11794242064397126261474117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7862828042931417507649411 11794242064397126261474117)
      ·
        refine ⟨2211420387074461174026397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11794242064397126261474117 2211420387074461174026397)
        ·
          refine ⟨829282645152922940259899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2211420387074461174026397 829282645152922940259899)
          ·
            refine ⟨1243923967729384410389849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829282645152922940259899 1243923967729384410389849)
            ·
              refine ⟨932942975797038307792387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1243923967729384410389849 932942975797038307792387)
              ·
                refine ⟨1399414463695557461688581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932942975797038307792387 1399414463695557461688581)
                ·
                  refine ⟨262390211942917024066609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399414463695557461688581 262390211942917024066609)
                  ·
                    rfl

theorem cell21_1149757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_1149757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149757 prefixEnd_1149757 := by exact prefixLift 1149757
  have htrace : WordTrace (prefixWord ++ tailWord_1149757) baseStart_1149757 baseEnd_1149757 := by
    simpa [prefixWord, tailWord_1149757, baseEnd_1149757] using wordTrace_append hprefix tailTrace_1149757
  have hstable : (prefixWord ++ tailWord_1149757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149757).length < 2 ^ (prefixWord ++ tailWord_1149757).sum := by decide
  have hdescent : baseEnd_1149757 < baseStart_1149757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149813 : List Nat := [1, 3, 4, 1, 1, 4, 1, 6]
def baseStart_1149813 : Nat := 118140960795 + 1149813 * 2 ^ 59
def prefixEnd_1149813 : Nat := 4983230072969 + 3 ^ 40 * 1149813 * 2
def baseEnd_1149813 : Nat := 87467663968624457044387

theorem tailTrace_1149813 : CollatzResearch.WordTrace tailWord_1149813 prefixEnd_1149813 87467663968624457044387 := by
  unfold tailWord_1149813
  simp only [CollatzResearch.WordTrace]
  refine ⟨41937125383431348271502093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27958083588954232181001395 41937125383431348271502093)
  ·
    refine ⟨15726422018786755601813285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41937125383431348271502093 15726422018786755601813285)
    ·
      refine ⟨2948704128522516675339991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15726422018786755601813285 2948704128522516675339991)
      ·
        refine ⟨4423056192783775013009987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2948704128522516675339991 4423056192783775013009987)
        ·
          refine ⟨6634584289175662519514981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4423056192783775013009987 6634584289175662519514981)
          ·
            refine ⟨1243984554220436722409059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6634584289175662519514981 1243984554220436722409059)
            ·
              refine ⟨1865976831330655083613589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243984554220436722409059 1865976831330655083613589)
              ·
                refine ⟨87467663968624457044387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1865976831330655083613589 87467663968624457044387)
                ·
                  rfl

theorem cell21_1149813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 6].length) (baseStart_1149813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149813 prefixEnd_1149813 := by exact prefixLift 1149813
  have htrace : WordTrace (prefixWord ++ tailWord_1149813) baseStart_1149813 baseEnd_1149813 := by
    simpa [prefixWord, tailWord_1149813, baseEnd_1149813] using wordTrace_append hprefix tailTrace_1149813
  have hstable : (prefixWord ++ tailWord_1149813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149813).length < 2 ^ (prefixWord ++ tailWord_1149813).sum := by decide
  have hdescent : baseEnd_1149813 < baseStart_1149813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149858 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1149858 : Nat := 118140960795 + 1149858 * 2 ^ 59
def prefixEnd_1149858 : Nat := 4983230072969 + 3 ^ 40 * 1149858 * 2
def baseEnd_1149858 : Nat := 262413261518963292883069

theorem tailTrace_1149858 : CollatzResearch.WordTrace tailWord_1149858 prefixEnd_1149858 262413261518963292883069 := by
  unfold tailWord_1149858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10484691667067080239222557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27959177778845547304593485 10484691667067080239222557)
  ·
    refine ⟨3931759375150155089708459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10484691667067080239222557 3931759375150155089708459)
    ·
      refine ⟨5897639062725232634562689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3931759375150155089708459 5897639062725232634562689)
      ·
        refine ⟨4423229297043924475922017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5897639062725232634562689 4423229297043924475922017)
        ·
          refine ⟨3317421972782943356941513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4423229297043924475922017 3317421972782943356941513)
          ·
            refine ⟨2488066479587207517706135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3317421972782943356941513 2488066479587207517706135)
            ·
              refine ⟨3732099719380811276559203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488066479587207517706135 3732099719380811276559203)
              ·
                refine ⟨5598149579071216914838805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732099719380811276559203 5598149579071216914838805)
                ·
                  refine ⟨262413261518963292883069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5598149579071216914838805 262413261518963292883069)
                  ·
                    rfl

theorem cell21_1149858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1149858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1149858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1149858 prefixEnd_1149858 := by exact prefixLift 1149858
  have htrace : WordTrace (prefixWord ++ tailWord_1149858) baseStart_1149858 baseEnd_1149858 := by
    simpa [prefixWord, tailWord_1149858, baseEnd_1149858] using wordTrace_append hprefix tailTrace_1149858
  have hstable : (prefixWord ++ tailWord_1149858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149858).length < 2 ^ (prefixWord ++ tailWord_1149858).sum := by decide
  have hdescent : baseEnd_1149858 < baseStart_1149858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150103 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 4]
def baseStart_1150103 : Nat := 118140960795 + 1150103 * 2 ^ 59
def prefixEnd_1150103 : Nat := 4983230072969 + 3 ^ 40 * 1150103 * 2
def baseEnd_1150103 : Nat := 262469173856897311299235

theorem tailTrace_1150103 : CollatzResearch.WordTrace tailWord_1150103 prefixEnd_1150103 262469173856897311299235 := by
  unfold tailWord_1150103
  simp only [CollatzResearch.WordTrace]
  refine ⟨41947702552380727799558963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27965135034920485199705975 41947702552380727799558963)
  ·
    refine ⟨62921553828571091699338445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41947702552380727799558963 62921553828571091699338445)
    ·
      refine ⟨23595582685714159387251917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62921553828571091699338445 23595582685714159387251917)
      ·
        refine ⟨8848343507142809770219469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23595582685714159387251917 8848343507142809770219469)
        ·
          refine ⟨3318128815178553663832301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8848343507142809770219469 3318128815178553663832301)
          ·
            refine ⟨1244298305691957623937113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3318128815178553663832301 1244298305691957623937113)
            ·
              refine ⟨933223729268968217952835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244298305691957623937113 933223729268968217952835)
              ·
                refine ⟨1399835593903452326929253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933223729268968217952835 1399835593903452326929253)
                ·
                  refine ⟨262469173856897311299235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399835593903452326929253 262469173856897311299235)
                  ·
                    rfl

theorem cell21_1150103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 4].length) (baseStart_1150103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150103 prefixEnd_1150103 := by exact prefixLift 1150103
  have htrace : WordTrace (prefixWord ++ tailWord_1150103) baseStart_1150103 baseEnd_1150103 := by
    simpa [prefixWord, tailWord_1150103, baseEnd_1150103] using wordTrace_append hprefix tailTrace_1150103
  have hstable : (prefixWord ++ tailWord_1150103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150103).length < 2 ^ (prefixWord ++ tailWord_1150103).sum := by decide
  have hdescent : baseEnd_1150103 < baseStart_1150103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150134 : List Nat := [5, 1, 3, 2, 2, 8]
def baseStart_1150134 : Nat := 118140960795 + 1150134 * 2 ^ 59
def prefixEnd_1150134 : Nat := 4983230072969 + 3 ^ 40 * 1150134 * 2
def baseEnd_1150134 : Nat := 9721342536268449862315

theorem tailTrace_1150134 : CollatzResearch.WordTrace tailWord_1150134 prefixEnd_1150134 9721342536268449862315 := by
  unfold tailWord_1150134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621802075954276255871091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27965888810178946729291637 2621802075954276255871091)
  ·
    refine ⟨3932703113931414383806637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2621802075954276255871091 3932703113931414383806637)
    ·
      refine ⟨1474763667724280393927489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3932703113931414383806637 1474763667724280393927489)
      ·
        refine ⟨1106072750793210295445617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1474763667724280393927489 1106072750793210295445617)
        ·
          refine ⟨829554563094907721584213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1106072750793210295445617 829554563094907721584213)
          ·
            refine ⟨9721342536268449862315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 829554563094907721584213 9721342536268449862315)
            ·
              rfl

theorem cell21_1150134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 8].length) (baseStart_1150134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150134 prefixEnd_1150134 := by exact prefixLift 1150134
  have htrace : WordTrace (prefixWord ++ tailWord_1150134) baseStart_1150134 baseEnd_1150134 := by
    simpa [prefixWord, tailWord_1150134, baseEnd_1150134] using wordTrace_append hprefix tailTrace_1150134
  have hstable : (prefixWord ++ tailWord_1150134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150134).length < 2 ^ (prefixWord ++ tailWord_1150134).sum := by decide
  have hdescent : baseEnd_1150134 < baseStart_1150134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150176 : List Nat := [2, 1, 1, 3, 1, 5, 3, 5]
def baseStart_1150176 : Nat := 118140960795 + 1150176 * 2 ^ 59
def prefixEnd_1150176 : Nat := 4983230072969 + 3 ^ 40 * 1150176 * 2
def baseEnd_1150176 : Nat := 87495277817155135527473

theorem tailTrace_1150176 : CollatzResearch.WordTrace tailWord_1150176 prefixEnd_1150176 87495277817155135527473 := by
  unfold tailWord_1150176
  simp only [CollatzResearch.WordTrace]
  refine ⟨20975182540558130633483191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27966910054077507511310921 20975182540558130633483191)
  ·
    refine ⟨31462773810837195950224787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20975182540558130633483191 31462773810837195950224787)
    ·
      refine ⟨47194160716255793925337181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31462773810837195950224787 47194160716255793925337181)
      ·
        refine ⟨17697810268595922722001443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47194160716255793925337181 17697810268595922722001443)
        ·
          refine ⟨26546715402893884083002165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17697810268595922722001443 26546715402893884083002165)
          ·
            refine ⟨2488754569021301632781453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26546715402893884083002165 2488754569021301632781453)
            ·
              refine ⟨933282963382988112293045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2488754569021301632781453 933282963382988112293045)
              ·
                refine ⟨87495277817155135527473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 933282963382988112293045 87495277817155135527473)
                ·
                  rfl

theorem cell21_1150176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_1150176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150176 prefixEnd_1150176 := by exact prefixLift 1150176
  have htrace : WordTrace (prefixWord ++ tailWord_1150176) baseStart_1150176 baseEnd_1150176 := by
    simpa [prefixWord, tailWord_1150176, baseEnd_1150176] using wordTrace_append hprefix tailTrace_1150176
  have hstable : (prefixWord ++ tailWord_1150176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150176).length < 2 ^ (prefixWord ++ tailWord_1150176).sum := by decide
  have hdescent : baseEnd_1150176 < baseStart_1150176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150196 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1150196 : Nat := 118140960795 + 1150196 * 2 ^ 59
def prefixEnd_1150196 : Nat := 4983230072969 + 3 ^ 40 * 1150196 * 2
def baseEnd_1150196 : Nat := 262490397723949816249045

theorem tailTrace_1150196 : CollatzResearch.WordTrace tailWord_1150196 prefixEnd_1150196 262490397723949816249045 := by
  unfold tailWord_1150196
  simp only [CollatzResearch.WordTrace]
  refine ⟨20975547270521902341347221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27967396360695869788462961 20975547270521902341347221)
  ·
    refine ⟨983228778305714172250651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20975547270521902341347221 983228778305714172250651)
    ·
      refine ⟨1474843167458571258375977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 983228778305714172250651 1474843167458571258375977)
      ·
        refine ⟨1106132375593928443781983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1474843167458571258375977 1106132375593928443781983)
        ·
          refine ⟨1659198563390892665672975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106132375593928443781983 1659198563390892665672975)
          ·
            refine ⟨2488797845086338998509463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659198563390892665672975 2488797845086338998509463)
            ·
              refine ⟨3733196767629508497764195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488797845086338998509463 3733196767629508497764195)
              ·
                refine ⟨5599795151444262746646293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3733196767629508497764195 5599795151444262746646293)
                ·
                  refine ⟨262490397723949816249045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5599795151444262746646293 262490397723949816249045)
                  ·
                    rfl

theorem cell21_1150196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1150196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150196 prefixEnd_1150196 := by exact prefixLift 1150196
  have htrace : WordTrace (prefixWord ++ tailWord_1150196) baseStart_1150196 baseEnd_1150196 := by
    simpa [prefixWord, tailWord_1150196, baseEnd_1150196] using wordTrace_append hprefix tailTrace_1150196
  have hstable : (prefixWord ++ tailWord_1150196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150196).length < 2 ^ (prefixWord ++ tailWord_1150196).sum := by decide
  have hdescent : baseEnd_1150196 < baseStart_1150196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150207 : List Nat := [1, 1, 2, 2, 1, 5, 2, 4, 3]
def baseStart_1150207 : Nat := 118140960795 + 1150207 * 2 ^ 59
def prefixEnd_1150207 : Nat := 4983230072969 + 3 ^ 40 * 1150207 * 2
def baseEnd_1150207 : Nat := 262492908073816241565689

theorem tailTrace_1150207 : CollatzResearch.WordTrace tailWord_1150207 prefixEnd_1150207 262492908073816241565689 := by
  unfold tailWord_1150207
  simp only [CollatzResearch.WordTrace]
  refine ⟨41951495744003953561344875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27967663829335969040896583 41951495744003953561344875)
  ·
    refine ⟨62927243616005930342017313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41951495744003953561344875 62927243616005930342017313)
    ·
      refine ⟨47195432712004447756512985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62927243616005930342017313 47195432712004447756512985)
      ·
        refine ⟨35396574534003335817384739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47195432712004447756512985 35396574534003335817384739)
        ·
          refine ⟨53094861801005003726077109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35396574534003335817384739 53094861801005003726077109)
          ·
            refine ⟨4977643293844219099319729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53094861801005003726077109 4977643293844219099319729)
            ·
              refine ⟨3733232470383164324489797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4977643293844219099319729 3733232470383164324489797)
              ·
                refine ⟨699981088196843310841837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3733232470383164324489797 699981088196843310841837)
                ·
                  refine ⟨262492908073816241565689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 699981088196843310841837 262492908073816241565689)
                  ·
                    rfl

theorem cell21_1150207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 3].length) (baseStart_1150207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150207 prefixEnd_1150207 := by exact prefixLift 1150207
  have htrace : WordTrace (prefixWord ++ tailWord_1150207) baseStart_1150207 baseEnd_1150207 := by
    simpa [prefixWord, tailWord_1150207, baseEnd_1150207] using wordTrace_append hprefix tailTrace_1150207
  have hstable : (prefixWord ++ tailWord_1150207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150207).length < 2 ^ (prefixWord ++ tailWord_1150207).sum := by decide
  have hdescent : baseEnd_1150207 < baseStart_1150207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150269 : List Nat := [1, 4, 1, 5, 1, 1, 2, 6]
def baseStart_1150269 : Nat := 118140960795 + 1150269 * 2 ^ 59
def prefixEnd_1150269 : Nat := 4983230072969 + 3 ^ 40 * 1150269 * 2
def baseEnd_1150269 : Nat := 87502352439505970510743

theorem tailTrace_1150269 : CollatzResearch.WordTrace tailWord_1150269 prefixEnd_1150269 87502352439505970510743 := by
  unfold tailWord_1150269
  simp only [CollatzResearch.WordTrace]
  refine ⟨41953757069779338150101861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27969171379852892100067907 41953757069779338150101861)
  ·
    refine ⟨7866329450583625903144099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41953757069779338150101861 7866329450583625903144099)
    ·
      refine ⟨11799494175875438854716149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7866329450583625903144099 11799494175875438854716149)
      ·
        refine ⟨1106202578988322392629639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11799494175875438854716149 1106202578988322392629639)
        ·
          refine ⟨1659303868482483588944459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106202578988322392629639 1659303868482483588944459)
          ·
            refine ⟨2488955802723725383416689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659303868482483588944459 2488955802723725383416689)
            ·
              refine ⟨1866716852042794037562517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488955802723725383416689 1866716852042794037562517)
              ·
                refine ⟨87502352439505970510743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1866716852042794037562517 87502352439505970510743)
                ·
                  rfl

theorem cell21_1150269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 6].length) (baseStart_1150269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150269 prefixEnd_1150269 := by exact prefixLift 1150269
  have htrace : WordTrace (prefixWord ++ tailWord_1150269) baseStart_1150269 baseEnd_1150269 := by
    simpa [prefixWord, tailWord_1150269, baseEnd_1150269] using wordTrace_append hprefix tailTrace_1150269
  have hstable : (prefixWord ++ tailWord_1150269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150269).length < 2 ^ (prefixWord ++ tailWord_1150269).sum := by decide
  have hdescent : baseEnd_1150269 < baseStart_1150269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150311 : List Nat := [1, 1, 5, 1, 4, 9]
def baseStart_1150311 : Nat := 118140960795 + 1150311 * 2 ^ 59
def prefixEnd_1150311 : Nat := 4983230072969 + 3 ^ 40 * 1150311 * 2
def baseEnd_1150311 : Nat := 9722838603360561919709

theorem tailTrace_1150311 : CollatzResearch.WordTrace tailWord_1150311 prefixEnd_1150311 9722838603360561919709 := by
  unfold tailWord_1150311
  simp only [CollatzResearch.WordTrace]
  refine ⟨41955288935627179323130787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27970192623751452882087191 41955288935627179323130787)
  ·
    refine ⟨62932933403440768984696181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41955288935627179323130787 62932933403440768984696181)
    ·
      refine ⟨5899962506572572092315267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62932933403440768984696181 5899962506572572092315267)
      ·
        refine ⟨8849943759858858138472901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5899962506572572092315267 8849943759858858138472901)
        ·
          refine ⟨1659364454973535900963669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8849943759858858138472901 1659364454973535900963669)
          ·
            refine ⟨9722838603360561919709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1659364454973535900963669 9722838603360561919709)
            ·
              rfl

theorem cell21_1150311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 9].length) (baseStart_1150311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150311 prefixEnd_1150311 := by exact prefixLift 1150311
  have htrace : WordTrace (prefixWord ++ tailWord_1150311) baseStart_1150311 baseEnd_1150311 := by
    simpa [prefixWord, tailWord_1150311, baseEnd_1150311] using wordTrace_append hprefix tailTrace_1150311
  have hstable : (prefixWord ++ tailWord_1150311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150311).length < 2 ^ (prefixWord ++ tailWord_1150311).sum := by decide
  have hdescent : baseEnd_1150311 < baseStart_1150311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150317 : List Nat := [1, 5, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1150317 : Nat := 118140960795 + 1150317 * 2 ^ 59
def prefixEnd_1150317 : Nat := 4983230072969 + 3 ^ 40 * 1150317 * 2
def baseEnd_1150317 : Nat := 262518011572480494732131

theorem tailTrace_1150317 : CollatzResearch.WordTrace tailWord_1150317 prefixEnd_1150317 262518011572480494732131 := by
  unfold tailWord_1150317
  simp only [CollatzResearch.WordTrace]
  refine ⟨41955507773605442347849205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27970338515736961565232803 41955507773605442347849205)
  ·
    refine ⟨3933328853775510220110863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41955507773605442347849205 3933328853775510220110863)
    ·
      refine ⟨5899993280663265330166295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3933328853775510220110863 5899993280663265330166295)
      ·
        refine ⟨8849989920994897995249443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5899993280663265330166295 8849989920994897995249443)
        ·
          refine ⟨13274984881492346992874165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8849989920994897995249443 13274984881492346992874165)
          ·
            refine ⟨1244529832639907530581953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13274984881492346992874165 1244529832639907530581953)
            ·
              refine ⟨933397374479930647936465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244529832639907530581953 933397374479930647936465)
              ·
                refine ⟨700048030859947985952349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933397374479930647936465 700048030859947985952349)
                ·
                  refine ⟨262518011572480494732131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700048030859947985952349 262518011572480494732131)
                  ·
                    rfl

theorem cell21_1150317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1150317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150317 prefixEnd_1150317 := by exact prefixLift 1150317
  have htrace : WordTrace (prefixWord ++ tailWord_1150317) baseStart_1150317 baseEnd_1150317 := by
    simpa [prefixWord, tailWord_1150317, baseEnd_1150317] using wordTrace_append hprefix tailTrace_1150317
  have hstable : (prefixWord ++ tailWord_1150317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150317).length < 2 ^ (prefixWord ++ tailWord_1150317).sum := by decide
  have hdescent : baseEnd_1150317 < baseStart_1150317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150376 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_1150376 : Nat := 118140960795 + 1150376 * 2 ^ 59
def prefixEnd_1150376 : Nat := 4983230072969 + 3 ^ 40 * 1150376 * 2
def baseEnd_1150376 : Nat := 262531476176309503248677

theorem tailTrace_1150376 : CollatzResearch.WordTrace tailWord_1150376 prefixEnd_1150376 262531476176309503248677 := by
  unfold tailWord_1150376
  simp only [CollatzResearch.WordTrace]
  refine ⟨20978829840195847712123491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27971773120261130282831321 20978829840195847712123491)
  ·
    refine ⟨31468244760293771568185237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20978829840195847712123491 31468244760293771568185237)
    ·
      refine ⟨1475073973138770542258683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31468244760293771568185237 1475073973138770542258683)
      ·
        refine ⟨2212610959708155813388025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475073973138770542258683 2212610959708155813388025)
        ·
          refine ⟨1659458219781116860041019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2212610959708155813388025 1659458219781116860041019)
          ·
            refine ⟨2489187329671675290061529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659458219781116860041019 2489187329671675290061529)
            ·
              refine ⟨1866890497253756467546147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2489187329671675290061529 1866890497253756467546147)
              ·
                refine ⟨2800335745880634701319221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866890497253756467546147 2800335745880634701319221)
                ·
                  refine ⟨262531476176309503248677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2800335745880634701319221 262531476176309503248677)
                  ·
                    rfl

theorem cell21_1150376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_1150376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150376 prefixEnd_1150376 := by exact prefixLift 1150376
  have htrace : WordTrace (prefixWord ++ tailWord_1150376) baseStart_1150376 baseEnd_1150376 := by
    simpa [prefixWord, tailWord_1150376, baseEnd_1150376] using wordTrace_append hprefix tailTrace_1150376
  have hstable : (prefixWord ++ tailWord_1150376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150376).length < 2 ^ (prefixWord ++ tailWord_1150376).sum := by decide
  have hdescent : baseEnd_1150376 < baseStart_1150376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150404 : List Nat := [2, 3, 3, 2, 1, 2, 1, 7]
def baseStart_1150404 : Nat := 118140960795 + 1150404 * 2 ^ 59
def prefixEnd_1150404 : Nat := 4983230072969 + 3 ^ 40 * 1150404 * 2
def baseEnd_1150404 : Nat := 87512622052595892260651

theorem tailTrace_1150404 : CollatzResearch.WordTrace tailWord_1150404 prefixEnd_1150404 87512622052595892260651 := by
  unfold tailWord_1150404
  simp only [CollatzResearch.WordTrace]
  refine ⟨20979340462145128103133133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27972453949526837470844177 20979340462145128103133133)
  ·
    refine ⟨7867252673304423038674925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20979340462145128103133133 7867252673304423038674925)
    ·
      refine ⟨2950219752489158639503097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7867252673304423038674925 2950219752489158639503097)
      ·
        refine ⟨2212664814366868979627323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2950219752489158639503097 2212664814366868979627323)
        ·
          refine ⟨3318997221550303469440985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212664814366868979627323 3318997221550303469440985)
          ·
            refine ⟨2489247916162727602080739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3318997221550303469440985 2489247916162727602080739)
            ·
              refine ⟨3733871874244091403121109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489247916162727602080739 3733871874244091403121109)
              ·
                refine ⟨87512622052595892260651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3733871874244091403121109 87512622052595892260651)
                ·
                  rfl

theorem cell21_1150404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_1150404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150404 prefixEnd_1150404 := by exact prefixLift 1150404
  have htrace : WordTrace (prefixWord ++ tailWord_1150404) baseStart_1150404 baseEnd_1150404 := by
    simpa [prefixWord, tailWord_1150404, baseEnd_1150404] using wordTrace_append hprefix tailTrace_1150404
  have hstable : (prefixWord ++ tailWord_1150404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150404).length < 2 ^ (prefixWord ++ tailWord_1150404).sum := by decide
  have hdescent : baseEnd_1150404 < baseStart_1150404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150435 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 5]
def baseStart_1150435 : Nat := 118140960795 + 1150435 * 2 ^ 59
def prefixEnd_1150435 : Nat := 4983230072969 + 3 ^ 40 * 1150435 * 2
def baseEnd_1150435 : Nat := 262544940780138511765223

theorem tailTrace_1150435 : CollatzResearch.WordTrace tailWord_1150435 prefixEnd_1150435 262544940780138511765223 := by
  unfold tailWord_1150435
  simp only [CollatzResearch.WordTrace]
  refine ⟨41959811587177948500644759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27973207724785299000429839 41959811587177948500644759)
  ·
    refine ⟨62939717380766922750967139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41959811587177948500644759 62939717380766922750967139)
    ·
      refine ⟨94409576071150384126450709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62939717380766922750967139 94409576071150384126450709)
      ·
        refine ⟨4425448878335174255927377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94409576071150384126450709 4425448878335174255927377)
        ·
          refine ⟨3319086658751380691945533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4425448878335174255927377 3319086658751380691945533)
          ·
            refine ⟨1244657497031767759479575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3319086658751380691945533 1244657497031767759479575)
            ·
              refine ⟨1866986245547651639219363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244657497031767759479575 1866986245547651639219363)
              ·
                refine ⟨2800479368321477458829045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866986245547651639219363 2800479368321477458829045)
                ·
                  refine ⟨262544940780138511765223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2800479368321477458829045 262544940780138511765223)
                  ·
                    rfl

theorem cell21_1150435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 5].length) (baseStart_1150435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150435 prefixEnd_1150435 := by exact prefixLift 1150435
  have htrace : WordTrace (prefixWord ++ tailWord_1150435) baseStart_1150435 baseEnd_1150435 := by
    simpa [prefixWord, tailWord_1150435, baseEnd_1150435] using wordTrace_append hprefix tailTrace_1150435
  have hstable : (prefixWord ++ tailWord_1150435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150435).length < 2 ^ (prefixWord ++ tailWord_1150435).sum := by decide
  have hdescent : baseEnd_1150435 < baseStart_1150435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150449 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 4]
def baseStart_1150449 : Nat := 118140960795 + 1150449 * 2 ^ 59
def prefixEnd_1150449 : Nat := 4983230072969 + 3 ^ 40 * 1150449 * 2
def baseEnd_1150449 : Nat := 262548135770877598531861

theorem tailTrace_1150449 : CollatzResearch.WordTrace tailWord_1150449 prefixEnd_1150449 262548135770877598531861 := by
  unfold tailWord_1150449
  simp only [CollatzResearch.WordTrace]
  refine ⟨41960322209127228891654401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27973548139418152594436267 41960322209127228891654401)
  ·
    refine ⟨31470241656845421668740801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41960322209127228891654401 31470241656845421668740801)
    ·
      refine ⟨23602681242634066251555601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31470241656845421668740801 23602681242634066251555601)
      ·
        refine ⟨17702010931975549688666701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23602681242634066251555601 17702010931975549688666701)
        ·
          refine ⟨6638254099490831133250013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17702010931975549688666701 6638254099490831133250013)
          ·
            refine ⟨2489345287309061674968755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6638254099490831133250013 2489345287309061674968755)
            ·
              refine ⟨3734017930963592512453133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489345287309061674968755 3734017930963592512453133)
              ·
                refine ⟨1400256724111347192169925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3734017930963592512453133 1400256724111347192169925)
                ·
                  refine ⟨262548135770877598531861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400256724111347192169925 262548135770877598531861)
                  ·
                    rfl

theorem cell21_1150449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_1150449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150449 prefixEnd_1150449 := by exact prefixLift 1150449
  have htrace : WordTrace (prefixWord ++ tailWord_1150449) baseStart_1150449 baseEnd_1150449 := by
    simpa [prefixWord, tailWord_1150449, baseEnd_1150449] using wordTrace_append hprefix tailTrace_1150449
  have hstable : (prefixWord ++ tailWord_1150449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150449).length < 2 ^ (prefixWord ++ tailWord_1150449).sum := by decide
  have hdescent : baseEnd_1150449 < baseStart_1150449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150570 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_1150570 : Nat := 118140960795 + 1150570 * 2 ^ 59
def prefixEnd_1150570 : Nat := 4983230072969 + 3 ^ 40 * 1150570 * 2
def baseEnd_1150570 : Nat := 262575749619408277014947

theorem tailTrace_1150570 : CollatzResearch.WordTrace tailWord_1150570 prefixEnd_1150570 262575749619408277014947 := by
  unfold tailWord_1150570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10491183860422216639202291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27976490294459244371206109 10491183860422216639202291)
  ·
    refine ⟨15736775790633324958803437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10491183860422216639202291 15736775790633324958803437)
    ·
      refine ⟨5901290921487496859551289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15736775790633324958803437 5901290921487496859551289)
      ·
        refine ⟨4425968191115622644663467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5901290921487496859551289 4425968191115622644663467)
        ·
          refine ⟨6638952286673433966995201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425968191115622644663467 6638952286673433966995201)
          ·
            refine ⟨4979214215005075475246401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6638952286673433966995201 4979214215005075475246401)
            ·
              refine ⟨3734410661253806606434801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4979214215005075475246401 3734410661253806606434801)
              ·
                refine ⟨2800807995940354954826101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3734410661253806606434801 2800807995940354954826101)
                ·
                  refine ⟨262575749619408277014947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2800807995940354954826101 262575749619408277014947)
                  ·
                    rfl

theorem cell21_1150570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_1150570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150570 prefixEnd_1150570 := by exact prefixLift 1150570
  have htrace : WordTrace (prefixWord ++ tailWord_1150570) baseStart_1150570 baseEnd_1150570 := by
    simpa [prefixWord, tailWord_1150570, baseEnd_1150570] using wordTrace_append hprefix tailTrace_1150570
  have hstable : (prefixWord ++ tailWord_1150570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150570).length < 2 ^ (prefixWord ++ tailWord_1150570).sum := by decide
  have hdescent : baseEnd_1150570 < baseStart_1150570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150573 : List Nat := [1, 5, 1, 1, 4, 2, 2, 5]
def baseStart_1150573 : Nat := 118140960795 + 1150573 * 2 ^ 59
def prefixEnd_1150573 : Nat := 4983230072969 + 3 ^ 40 * 1150573 * 2
def baseEnd_1150573 : Nat := 87525478086760312821647

theorem tailTrace_1150573 : CollatzResearch.WordTrace tailWord_1150573 prefixEnd_1150573 87525478086760312821647 := by
  unfold tailWord_1150573
  simp only [CollatzResearch.WordTrace]
  refine ⟨41964844860677998069168373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27976563240451998712778915 41964844860677998069168373)
  ·
    refine ⟨3934204205688562318984535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41964844860677998069168373 3934204205688562318984535)
    ·
      refine ⟨5901306308532843478476803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3934204205688562318984535 5901306308532843478476803)
      ·
        refine ⟨8851959462799265217715205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5901306308532843478476803 8851959462799265217715205)
        ·
          refine ⟨1659742399274862228321601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8851959462799265217715205 1659742399274862228321601)
          ·
            refine ⟨1244806799456146671241201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1659742399274862228321601 1244806799456146671241201)
            ·
              refine ⟨933605099592110003430901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244806799456146671241201 933605099592110003430901)
              ·
                refine ⟨87525478086760312821647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 933605099592110003430901 87525478086760312821647)
                ·
                  rfl

theorem cell21_1150573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 5].length) (baseStart_1150573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150573 prefixEnd_1150573 := by exact prefixLift 1150573
  have htrace : WordTrace (prefixWord ++ tailWord_1150573) baseStart_1150573 baseEnd_1150573 := by
    simpa [prefixWord, tailWord_1150573, baseEnd_1150573] using wordTrace_append hprefix tailTrace_1150573
  have hstable : (prefixWord ++ tailWord_1150573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150573).length < 2 ^ (prefixWord ++ tailWord_1150573).sum := by decide
  have hdescent : baseEnd_1150573 < baseStart_1150573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150615 : List Nat := [1, 1, 3, 3, 2, 3, 2, 6]
def baseStart_1150615 : Nat := 118140960795 + 1150615 * 2 ^ 59
def prefixEnd_1150615 : Nat := 4983230072969 + 3 ^ 40 * 1150615 * 2
def baseEnd_1150615 : Nat := 87528673077499399588285

theorem tailTrace_1150615 : CollatzResearch.WordTrace tailWord_1150615 prefixEnd_1150615 87528673077499399588285 := by
  unfold tailWord_1150615
  simp only [CollatzResearch.WordTrace]
  refine ⟨41966376726525839242197299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27977584484350559494798199 41966376726525839242197299)
  ·
    refine ⟨62949565089788758863295949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41966376726525839242197299 62949565089788758863295949)
    ·
      refine ⟨23606086908670784573735981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62949565089788758863295949 23606086908670784573735981)
      ·
        refine ⟨8852282590751544215150993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23606086908670784573735981 8852282590751544215150993)
        ·
          refine ⟨6639211943063658161363245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8852282590751544215150993 6639211943063658161363245)
          ·
            refine ⟨2489704478648871810511217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6639211943063658161363245 2489704478648871810511217)
            ·
              refine ⟨1867278358986653857883413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2489704478648871810511217 1867278358986653857883413)
              ·
                refine ⟨87528673077499399588285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1867278358986653857883413 87528673077499399588285)
                ·
                  rfl

theorem cell21_1150615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 6].length) (baseStart_1150615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150615 prefixEnd_1150615 := by exact prefixLift 1150615
  have htrace : WordTrace (prefixWord ++ tailWord_1150615) baseStart_1150615 baseEnd_1150615 := by
    simpa [prefixWord, tailWord_1150615, baseEnd_1150615] using wordTrace_append hprefix tailTrace_1150615
  have hstable : (prefixWord ++ tailWord_1150615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150615).length < 2 ^ (prefixWord ++ tailWord_1150615).sum := by decide
  have hdescent : baseEnd_1150615 < baseStart_1150615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150629 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 5]
def baseStart_1150629 : Nat := 118140960795 + 1150629 * 2 ^ 59
def prefixEnd_1150629 : Nat := 4983230072969 + 3 ^ 40 * 1150629 * 2
def baseEnd_1150629 : Nat := 262589214223237285531493

theorem tailTrace_1150629 : CollatzResearch.WordTrace tailWord_1150629 prefixEnd_1150629 262589214223237285531493 := by
  unfold tailWord_1150629
  simp only [CollatzResearch.WordTrace]
  refine ⟨41966887348475119633206941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27977924898983413088804627 41966887348475119633206941)
  ·
    refine ⟨15737582755678169862452603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41966887348475119633206941 15737582755678169862452603)
    ·
      refine ⟨23606374133517254793678905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15737582755678169862452603 23606374133517254793678905)
      ·
        refine ⟨17704780600137941095259179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23606374133517254793678905 17704780600137941095259179)
        ·
          refine ⟨26557170900206911642888769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17704780600137941095259179 26557170900206911642888769)
          ·
            refine ⟨19917878175155183732166577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26557170900206911642888769 19917878175155183732166577)
            ·
              refine ⟨14938408631366387799124933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19917878175155183732166577 14938408631366387799124933)
              ·
                refine ⟨2800951618381197712335925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14938408631366387799124933 2800951618381197712335925)
                ·
                  refine ⟨262589214223237285531493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2800951618381197712335925 262589214223237285531493)
                  ·
                    rfl

theorem cell21_1150629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_1150629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150629 prefixEnd_1150629 := by exact prefixLift 1150629
  have htrace : WordTrace (prefixWord ++ tailWord_1150629) baseStart_1150629 baseEnd_1150629 := by
    simpa [prefixWord, tailWord_1150629, baseEnd_1150629] using wordTrace_append hprefix tailTrace_1150629
  have hstable : (prefixWord ++ tailWord_1150629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150629).length < 2 ^ (prefixWord ++ tailWord_1150629).sum := by decide
  have hdescent : baseEnd_1150629 < baseStart_1150629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150756 : List Nat := [2, 3, 1, 3, 2, 3, 1, 3, 3]
def baseStart_1150756 : Nat := 118140960795 + 1150756 * 2 ^ 59
def prefixEnd_1150756 : Nat := 4983230072969 + 3 ^ 40 * 1150756 * 2
def baseEnd_1150756 : Nat := 262618197353513286914567

theorem tailTrace_1150756 : CollatzResearch.WordTrace tailWord_1150756 prefixEnd_1150756 262618197353513286914567 := by
  unfold tailWord_1150756
  simp only [CollatzResearch.WordTrace]
  refine ⟨20985759709507510161540061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27981012946010013548720081 20985759709507510161540061)
  ·
    refine ⟨7869659891065316310577523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20985759709507510161540061 7869659891065316310577523)
    ·
      refine ⟨11804489836597974465866285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7869659891065316310577523 11804489836597974465866285)
      ·
        refine ⟨4426683688724240424699857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11804489836597974465866285 4426683688724240424699857)
        ·
          refine ⟨3320012766543180318524893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4426683688724240424699857 3320012766543180318524893)
          ·
            refine ⟨1245004787453692619446835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3320012766543180318524893 1245004787453692619446835)
            ·
              refine ⟨1867507181180538929170253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245004787453692619446835 1867507181180538929170253)
              ·
                refine ⟨700315192942702098438845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1867507181180538929170253 700315192942702098438845)
                ·
                  refine ⟨262618197353513286914567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700315192942702098438845 262618197353513286914567)
                  ·
                    rfl

theorem cell21_1150756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_1150756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150756 prefixEnd_1150756 := by exact prefixLift 1150756
  have htrace : WordTrace (prefixWord ++ tailWord_1150756) baseStart_1150756 baseEnd_1150756 := by
    simpa [prefixWord, tailWord_1150756, baseEnd_1150756] using wordTrace_append hprefix tailTrace_1150756
  have hstable : (prefixWord ++ tailWord_1150756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150756).length < 2 ^ (prefixWord ++ tailWord_1150756).sum := by decide
  have hdescent : baseEnd_1150756 < baseStart_1150756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150846 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1150846 : Nat := 118140960795 + 1150846 * 2 ^ 59
def prefixEnd_1150846 : Nat := 4983230072969 + 3 ^ 40 * 1150846 * 2
def baseEnd_1150846 : Nat := 262638736579693130414383

theorem tailTrace_1150846 : CollatzResearch.WordTrace tailWord_1150846 prefixEnd_1150846 262638736579693130414383 := by
  unfold tailWord_1150846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5246850248586120711732049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27983201325792643795904261 5246850248586120711732049)
  ·
    refine ⟨3935137686439590533799037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5246850248586120711732049 3935137686439590533799037)
    ·
      refine ⟨1475676632414846450174639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3935137686439590533799037 1475676632414846450174639)
      ·
        refine ⟨2213514948622269675261959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475676632414846450174639 2213514948622269675261959)
        ·
          refine ⟨3320272422933404512892939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2213514948622269675261959 3320272422933404512892939)
          ·
            refine ⟨4980408634400106769339409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3320272422933404512892939 4980408634400106769339409)
            ·
              refine ⟨3735306475800080077004557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4980408634400106769339409 3735306475800080077004557)
              ·
                refine ⟨1400739928425030028876709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3735306475800080077004557 1400739928425030028876709)
                ·
                  refine ⟨262638736579693130414383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400739928425030028876709 262638736579693130414383)
                  ·
                    rfl

theorem cell21_1150846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1150846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150846 prefixEnd_1150846 := by exact prefixLift 1150846
  have htrace : WordTrace (prefixWord ++ tailWord_1150846) baseStart_1150846 baseEnd_1150846 := by
    simpa [prefixWord, tailWord_1150846, baseEnd_1150846] using wordTrace_append hprefix tailTrace_1150846
  have hstable : (prefixWord ++ tailWord_1150846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150846).length < 2 ^ (prefixWord ++ tailWord_1150846).sum := by decide
  have hdescent : baseEnd_1150846 < baseStart_1150846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150857 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 5]
def baseStart_1150857 : Nat := 118140960795 + 1150857 * 2 ^ 59
def prefixEnd_1150857 : Nat := 4983230072969 + 3 ^ 40 * 1150857 * 2
def baseEnd_1150857 : Nat := 262641246929559555731027

theorem tailTrace_1150857 : CollatzResearch.WordTrace tailWord_1150857 prefixEnd_1150857 262641246929559555731027 := by
  unfold tailWord_1150857
  simp only [CollatzResearch.WordTrace]
  refine ⟨41975203191649114572506825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27983468794432743048337883 41975203191649114572506825)
  ·
    refine ⟨31481402393736835929380119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41975203191649114572506825 31481402393736835929380119)
    ·
      refine ⟨47222103590605253894070179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31481402393736835929380119 47222103590605253894070179)
      ·
        refine ⟨70833155385907880841105269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47222103590605253894070179 70833155385907880841105269)
        ·
          refine ⟨6640608317428863828853619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70833155385907880841105269 6640608317428863828853619)
          ·
            refine ⟨9960912476143295743280429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6640608317428863828853619 9960912476143295743280429)
            ·
              refine ⟨3735342178553735903730161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9960912476143295743280429 3735342178553735903730161)
              ·
                refine ⟨2801506633915301927797621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3735342178553735903730161 2801506633915301927797621)
                ·
                  refine ⟨262641246929559555731027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2801506633915301927797621 262641246929559555731027)
                  ·
                    rfl

theorem cell21_1150857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_1150857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150857 prefixEnd_1150857 := by exact prefixLift 1150857
  have htrace : WordTrace (prefixWord ++ tailWord_1150857) baseStart_1150857 baseEnd_1150857 := by
    simpa [prefixWord, tailWord_1150857, baseEnd_1150857] using wordTrace_append hprefix tailTrace_1150857
  have hstable : (prefixWord ++ tailWord_1150857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150857).length < 2 ^ (prefixWord ++ tailWord_1150857).sum := by decide
  have hdescent : baseEnd_1150857 < baseStart_1150857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150905 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 4]
def baseStart_1150905 : Nat := 118140960795 + 1150905 * 2 ^ 59
def prefixEnd_1150905 : Nat := 4983230072969 + 3 ^ 40 * 1150905 * 2
def baseEnd_1150905 : Nat := 262652201183522138930929

theorem tailTrace_1150905 : CollatzResearch.WordTrace tailWord_1150905 prefixEnd_1150905 262652201183522138930929 := by
  unfold tailWord_1150905
  simp only [CollatzResearch.WordTrace]
  refine ⟨41976953895475218770254169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27984635930316812513502779 41976953895475218770254169)
  ·
    refine ⟨31482715421606414077690627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41976953895475218770254169 31482715421606414077690627)
    ·
      refine ⟨47224073132409621116535941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31482715421606414077690627 47224073132409621116535941)
      ·
        refine ⟨8854513712326803959350489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47224073132409621116535941 8854513712326803959350489)
        ·
          refine ⟨6640885284245102969512867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8854513712326803959350489 6640885284245102969512867)
          ·
            refine ⟨9961327926367654454269301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6640885284245102969512867 9961327926367654454269301)
            ·
              refine ⟨933874493096967605087747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9961327926367654454269301 933874493096967605087747)
              ·
                refine ⟨1400811739645451407631621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933874493096967605087747 1400811739645451407631621)
                ·
                  refine ⟨262652201183522138930929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400811739645451407631621 262652201183522138930929)
                  ·
                    rfl

theorem cell21_1150905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_1150905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150905 prefixEnd_1150905 := by exact prefixLift 1150905
  have htrace : WordTrace (prefixWord ++ tailWord_1150905) baseStart_1150905 baseEnd_1150905 := by
    simpa [prefixWord, tailWord_1150905, baseEnd_1150905] using wordTrace_append hprefix tailTrace_1150905
  have hstable : (prefixWord ++ tailWord_1150905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150905).length < 2 ^ (prefixWord ++ tailWord_1150905).sum := by decide
  have hdescent : baseEnd_1150905 < baseStart_1150905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150992 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_1150992 : Nat := 118140960795 + 1150992 * 2 ^ 59
def prefixEnd_1150992 : Nat := 4983230072969 + 3 ^ 40 * 1150992 * 2
def baseEnd_1150992 : Nat := 262672055768829320980751

theorem tailTrace_1150992 : CollatzResearch.WordTrace tailWord_1150992 prefixEnd_1150992 262672055768829320980751 := by
  unfold tailWord_1150992
  simp only [CollatzResearch.WordTrace]
  refine ⟨20990063523080016314335615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27986751364106688419114153 20990063523080016314335615)
  ·
    refine ⟨31485095284620024471503423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20990063523080016314335615 31485095284620024471503423)
    ·
      refine ⟨47227642926930036707255135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31485095284620024471503423 47227642926930036707255135)
      ·
        refine ⟨70841464390395055060882703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47227642926930036707255135 70841464390395055060882703)
        ·
          refine ⟨106262196585592582591324055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70841464390395055060882703 106262196585592582591324055)
          ·
            refine ⟨159393294878388873886986083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106262196585592582591324055 159393294878388873886986083)
            ·
              refine ⟨239089942317583310830479125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159393294878388873886986083 239089942317583310830479125)
              ·
                refine ⟨11207341046136717695178709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 239089942317583310830479125 11207341046136717695178709)
                ·
                  refine ⟨262672055768829320980751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11207341046136717695178709 262672055768829320980751)
                  ·
                    rfl

theorem cell21_1150992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_1150992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1150992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1150992 prefixEnd_1150992 := by exact prefixLift 1150992
  have htrace : WordTrace (prefixWord ++ tailWord_1150992) baseStart_1150992 baseEnd_1150992 := by
    simpa [prefixWord, tailWord_1150992, baseEnd_1150992] using wordTrace_append hprefix tailTrace_1150992
  have hstable : (prefixWord ++ tailWord_1150992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150992).length < 2 ^ (prefixWord ++ tailWord_1150992).sum := by decide
  have hdescent : baseEnd_1150992 < baseStart_1150992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151012 : List Nat := [2, 3, 1, 4, 2, 2, 1, 6]
def baseStart_1151012 : Nat := 118140960795 + 1151012 * 2 ^ 59
def prefixEnd_1151012 : Nat := 4983230072969 + 3 ^ 40 * 1151012 * 2
def baseEnd_1151012 : Nat := 87558873347104576882459

theorem tailTrace_1151012 : CollatzResearch.WordTrace tailWord_1151012 prefixEnd_1151012 87558873347104576882459 := by
  unfold tailWord_1151012
  simp only [CollatzResearch.WordTrace]
  refine ⟨20990428253043788022199645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27987237670725050696266193 20990428253043788022199645)
  ·
    refine ⟨7871410594891420508324867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20990428253043788022199645 7871410594891420508324867)
    ·
      refine ⟨11807115892337130762487301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7871410594891420508324867 11807115892337130762487301)
      ·
        refine ⟨2213834229813212017966369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11807115892337130762487301 2213834229813212017966369)
        ·
          refine ⟨1660375672359909013474777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2213834229813212017966369 1660375672359909013474777)
          ·
            refine ⟨1245281754269931760106083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1660375672359909013474777 1245281754269931760106083)
            ·
              refine ⟨1867922631404897640159125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245281754269931760106083 1867922631404897640159125)
              ·
                refine ⟨87558873347104576882459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1867922631404897640159125 87558873347104576882459)
                ·
                  rfl

theorem cell21_1151012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_1151012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151012 prefixEnd_1151012 := by exact prefixLift 1151012
  have htrace : WordTrace (prefixWord ++ tailWord_1151012) baseStart_1151012 baseEnd_1151012 := by
    simpa [prefixWord, tailWord_1151012, baseEnd_1151012] using wordTrace_append hprefix tailTrace_1151012
  have hstable : (prefixWord ++ tailWord_1151012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151012).length < 2 ^ (prefixWord ++ tailWord_1151012).sum := by decide
  have hdescent : baseEnd_1151012 < baseStart_1151012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151054 : List Nat := [4, 1, 1, 1, 1, 5, 8]
def baseStart_1151054 : Nat := 118140960795 + 1151054 * 2 ^ 59
def prefixEnd_1151054 : Nat := 4983230072969 + 3 ^ 40 * 1151054 * 2
def baseEnd_1151054 : Nat := 29187356112614554549699

theorem tailTrace_1151054 : CollatzResearch.WordTrace tailWord_1151054 prefixEnd_1151054 29187356112614554549699 := by
  unfold tailWord_1151054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5247798546491927152178527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27988258914623611478285477 5247798546491927152178527)
  ·
    refine ⟨7871697819737890728267791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5247798546491927152178527 7871697819737890728267791)
    ·
      refine ⟨11807546729606836092401687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7871697819737890728267791 11807546729606836092401687)
      ·
        refine ⟨17711320094410254138602531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11807546729606836092401687 17711320094410254138602531)
        ·
          refine ⟨26566980141615381207903797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17711320094410254138602531 26566980141615381207903797)
          ·
            refine ⟨2490654388276441988240981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26566980141615381207903797 2490654388276441988240981)
            ·
              refine ⟨29187356112614554549699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2490654388276441988240981 29187356112614554549699)
              ·
                rfl

theorem cell21_1151054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 8].length) (baseStart_1151054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151054 prefixEnd_1151054 := by exact prefixLift 1151054
  have htrace : WordTrace (prefixWord ++ tailWord_1151054) baseStart_1151054 baseEnd_1151054 := by
    simpa [prefixWord, tailWord_1151054, baseEnd_1151054] using wordTrace_append hprefix tailTrace_1151054
  have hstable : (prefixWord ++ tailWord_1151054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151054).length < 2 ^ (prefixWord ++ tailWord_1151054).sum := by decide
  have hdescent : baseEnd_1151054 < baseStart_1151054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151085 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1151085 : Nat := 118140960795 + 1151085 * 2 ^ 59
def prefixEnd_1151085 : Nat := 4983230072969 + 3 ^ 40 * 1151085 * 2
def baseEnd_1151085 : Nat := 262693279635881825930561

theorem tailTrace_1151085 : CollatzResearch.WordTrace tailWord_1151085 prefixEnd_1151085 262693279635881825930561 := by
  unfold tailWord_1151085
  simp only [CollatzResearch.WordTrace]
  refine ⟨41983519034823109511806709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27989012689882073007871139 41983519034823109511806709)
  ·
    refine ⟨3935954909514666516731879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41983519034823109511806709 3935954909514666516731879)
    ·
      refine ⟨5903932364271999775097819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3935954909514666516731879 5903932364271999775097819)
      ·
        refine ⟨8855898546407999662646729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5903932364271999775097819 8855898546407999662646729)
        ·
          refine ⟨6641923909805999746985047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8855898546407999662646729 6641923909805999746985047)
          ·
            refine ⟨9962885864708999620477571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6641923909805999746985047 9962885864708999620477571)
            ·
              refine ⟨14944328797063499430716357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9962885864708999620477571 14944328797063499430716357)
              ·
                refine ⟨2802061649449406143259317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14944328797063499430716357 2802061649449406143259317)
                ·
                  refine ⟨262693279635881825930561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2802061649449406143259317 262693279635881825930561)
                  ·
                    rfl

theorem cell21_1151085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1151085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151085 prefixEnd_1151085 := by exact prefixLift 1151085
  have htrace : WordTrace (prefixWord ++ tailWord_1151085) baseStart_1151085 baseEnd_1151085 := by
    simpa [prefixWord, tailWord_1151085, baseEnd_1151085] using wordTrace_append hprefix tailTrace_1151085
  have hstable : (prefixWord ++ tailWord_1151085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151085).length < 2 ^ (prefixWord ++ tailWord_1151085).sum := by decide
  have hdescent : baseEnd_1151085 < baseStart_1151085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151133 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1151133 : Nat := 118140960795 + 1151133 * 2 ^ 59
def prefixEnd_1151133 : Nat := 4983230072969 + 3 ^ 40 * 1151133 * 2
def baseEnd_1151133 : Nat := 262704233889844409130463

theorem tailTrace_1151133 : CollatzResearch.WordTrace tailWord_1151133 prefixEnd_1151133 262704233889844409130463 := by
  unfold tailWord_1151133
  simp only [CollatzResearch.WordTrace]
  refine ⟨41985269738649213709554053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27990179825766142473036035 41985269738649213709554053)
  ·
    refine ⟨7872238075996727570541385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41985269738649213709554053 7872238075996727570541385)
    ·
      refine ⟨5904178556997545677906039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7872238075996727570541385 5904178556997545677906039)
      ·
        refine ⟨8856267835496318516859059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5904178556997545677906039 8856267835496318516859059)
        ·
          refine ⟨13284401753244477775288589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8856267835496318516859059 13284401753244477775288589)
          ·
            refine ⟨4981650657466679165733221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13284401753244477775288589 4981650657466679165733221)
            ·
              refine ⟨934059498275002343574979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4981650657466679165733221 934059498275002343574979)
              ·
                refine ⟨1401089247412503515362469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934059498275002343574979 1401089247412503515362469)
                ·
                  refine ⟨262704233889844409130463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401089247412503515362469 262704233889844409130463)
                  ·
                    rfl

theorem cell21_1151133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1151133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151133 prefixEnd_1151133 := by exact prefixLift 1151133
  have htrace : WordTrace (prefixWord ++ tailWord_1151133) baseStart_1151133 baseEnd_1151133 := by
    simpa [prefixWord, tailWord_1151133, baseEnd_1151133] using wordTrace_append hprefix tailTrace_1151133
  have hstable : (prefixWord ++ tailWord_1151133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151133).length < 2 ^ (prefixWord ++ tailWord_1151133).sum := by decide
  have hdescent : baseEnd_1151133 < baseStart_1151133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151170 : List Nat := [3, 5, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1151170 : Nat := 118140960795 + 1151170 * 2 ^ 59
def prefixEnd_1151170 : Nat := 4983230072969 + 3 ^ 40 * 1151170 * 2
def baseEnd_1151170 : Nat := 262712677793940567013721

theorem tailTrace_1151170 : CollatzResearch.WordTrace tailWord_1151170 prefixEnd_1151170 262712677793940567013721 := by
  unfold tailWord_1151170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10496654809878792257162741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27991079493010112685767309 10496654809878792257162741)
  ·
    refine ⟨984061388426136774109007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10496654809878792257162741 984061388426136774109007)
    ·
      refine ⟨1476092082639205161163511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984061388426136774109007 1476092082639205161163511)
      ·
        refine ⟨2214138123958807741745267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476092082639205161163511 2214138123958807741745267)
        ·
          refine ⟨3321207185938211612617901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214138123958807741745267 3321207185938211612617901)
          ·
            refine ⟨1245452694726829354731713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3321207185938211612617901 1245452694726829354731713)
            ·
              refine ⟨934089521045122016048785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245452694726829354731713 934089521045122016048785)
              ·
                refine ⟨700567140783841512036589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934089521045122016048785 700567140783841512036589)
                ·
                  refine ⟨262712677793940567013721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700567140783841512036589 262712677793940567013721)
                  ·
                    rfl

theorem cell21_1151170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1151170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151170 prefixEnd_1151170 := by exact prefixLift 1151170
  have htrace : WordTrace (prefixWord ++ tailWord_1151170) baseStart_1151170 baseEnd_1151170 := by
    simpa [prefixWord, tailWord_1151170, baseEnd_1151170] using wordTrace_append hprefix tailTrace_1151170
  have hstable : (prefixWord ++ tailWord_1151170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151170).length < 2 ^ (prefixWord ++ tailWord_1151170).sum := by decide
  have hdescent : baseEnd_1151170 < baseStart_1151170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151178 : List Nat := [3, 1, 2, 1, 3, 1, 3, 4, 3]
def baseStart_1151178 : Nat := 118140960795 + 1151178 * 2 ^ 59
def prefixEnd_1151178 : Nat := 4983230072969 + 3 ^ 40 * 1151178 * 2
def baseEnd_1151178 : Nat := 262714503502934330880371

theorem tailTrace_1151178 : CollatzResearch.WordTrace tailWord_1151178 prefixEnd_1151178 262714503502934330880371 := by
  unfold tailWord_1151178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10496727755871546598735547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27991274015657457596628125 10496727755871546598735547)
  ·
    refine ⟨15745091633807319898103321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10496727755871546598735547 15745091633807319898103321)
    ·
      refine ⟨11808818725355489923577491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15745091633807319898103321 11808818725355489923577491)
      ·
        refine ⟨17713228088033234885366237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11808818725355489923577491 17713228088033234885366237)
        ·
          refine ⟨6642460533012463082012339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17713228088033234885366237 6642460533012463082012339)
          ·
            refine ⟨9963690799518694623018509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6642460533012463082012339 9963690799518694623018509)
            ·
              refine ⟨3736384049819510483631941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9963690799518694623018509 3736384049819510483631941)
              ·
                refine ⟨700572009341158215680989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3736384049819510483631941 700572009341158215680989)
                ·
                  refine ⟨262714503502934330880371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700572009341158215680989 262714503502934330880371)
                  ·
                    rfl

theorem cell21_1151178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_1151178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151178 prefixEnd_1151178 := by exact prefixLift 1151178
  have htrace : WordTrace (prefixWord ++ tailWord_1151178) baseStart_1151178 baseEnd_1151178 := by
    simpa [prefixWord, tailWord_1151178, baseEnd_1151178] using wordTrace_append hprefix tailTrace_1151178
  have hstable : (prefixWord ++ tailWord_1151178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151178).length < 2 ^ (prefixWord ++ tailWord_1151178).sum := by decide
  have hdescent : baseEnd_1151178 < baseStart_1151178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151192 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_1151192 : Nat := 118140960795 + 1151192 * 2 ^ 59
def prefixEnd_1151192 : Nat := 4983230072969 + 3 ^ 40 * 1151192 * 2
def baseEnd_1151192 : Nat := 262717698493673417647009

theorem tailTrace_1151192 : CollatzResearch.WordTrace tailWord_1151192 prefixEnd_1151192 262717698493673417647009 := by
  unfold tailWord_1151192
  simp only [CollatzResearch.WordTrace]
  refine ⟨20993710822717733392975915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27991614430290311190634553 20993710822717733392975915)
  ·
    refine ⟨31490566234076600089463873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20993710822717733392975915 31490566234076600089463873)
    ·
      refine ⟨23617924675557450067097905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31490566234076600089463873 23617924675557450067097905)
      ·
        refine ⟨17713443506668087550323429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23617924675557450067097905 17713443506668087550323429)
        ·
          refine ⟨3321270657500266415685643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17713443506668087550323429 3321270657500266415685643)
          ·
            refine ⟨4981905986250399623528465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321270657500266415685643 4981905986250399623528465)
            ·
              refine ⟨3736429489687799717646349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4981905986250399623528465 3736429489687799717646349)
              ·
                refine ⟨1401161058632924894117381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3736429489687799717646349 1401161058632924894117381)
                ·
                  refine ⟨262717698493673417647009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401161058632924894117381 262717698493673417647009)
                  ·
                    rfl

theorem cell21_1151192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_1151192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151192 prefixEnd_1151192 := by exact prefixLift 1151192
  have htrace : WordTrace (prefixWord ++ tailWord_1151192) baseStart_1151192 baseEnd_1151192 := by
    simpa [prefixWord, tailWord_1151192, baseEnd_1151192] using wordTrace_append hprefix tailTrace_1151192
  have hstable : (prefixWord ++ tailWord_1151192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151192).length < 2 ^ (prefixWord ++ tailWord_1151192).sum := by decide
  have hdescent : baseEnd_1151192 < baseStart_1151192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151251 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 4]
def baseStart_1151251 : Nat := 118140960795 + 1151251 * 2 ^ 59
def prefixEnd_1151251 : Nat := 4983230072969 + 3 ^ 40 * 1151251 * 2
def baseEnd_1151251 : Nat := 262731163097502426163555

theorem tailTrace_1151251 : CollatzResearch.WordTrace tailWord_1151251 prefixEnd_1151251 262731163097502426163555 := by
  unfold tailWord_1151251
  simp only [CollatzResearch.WordTrace]
  refine ⟨41989573552221719862349607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27993049034814479908233071 41989573552221719862349607)
  ·
    refine ⟨62984360328332579793524411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41989573552221719862349607 62984360328332579793524411)
    ·
      refine ⟨94476540492498869690286617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62984360328332579793524411 94476540492498869690286617)
      ·
        refine ⟨70857405369374152267714963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94476540492498869690286617 70857405369374152267714963)
        ·
          refine ⟨106286108054061228401572445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70857405369374152267714963 106286108054061228401572445)
          ·
            refine ⟨39857290520272960650589667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106286108054061228401572445 39857290520272960650589667)
            ·
              refine ⟨59785935780409440975884501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39857290520272960650589667 59785935780409440975884501)
              ·
                refine ⟨1401232869853346272872293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59785935780409440975884501 1401232869853346272872293)
                ·
                  refine ⟨262731163097502426163555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401232869853346272872293 262731163097502426163555)
                  ·
                    rfl

theorem cell21_1151251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 4].length) (baseStart_1151251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151251 prefixEnd_1151251 := by exact prefixLift 1151251
  have htrace : WordTrace (prefixWord ++ tailWord_1151251) baseStart_1151251 baseEnd_1151251 := by
    simpa [prefixWord, tailWord_1151251, baseEnd_1151251] using wordTrace_append hprefix tailTrace_1151251
  have hstable : (prefixWord ++ tailWord_1151251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151251).length < 2 ^ (prefixWord ++ tailWord_1151251).sum := by decide
  have hdescent : baseEnd_1151251 < baseStart_1151251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151296 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_1151296 : Nat := 118140960795 + 1151296 * 2 ^ 59
def prefixEnd_1151296 : Nat := 4983230072969 + 3 ^ 40 * 1151296 * 2
def baseEnd_1151296 : Nat := 262741432710592347913463

theorem tailTrace_1151296 : CollatzResearch.WordTrace tailWord_1151296 prefixEnd_1151296 262741432710592347913463 := by
  unfold tailWord_1151296
  simp only [CollatzResearch.WordTrace]
  refine ⟨20995607418529346273868871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27994143224705795031825161 20995607418529346273868871)
  ·
    refine ⟨31493411127794019410803307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20995607418529346273868871 31493411127794019410803307)
    ·
      refine ⟨47240116691691029116204961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31493411127794019410803307 47240116691691029116204961)
      ·
        refine ⟨35430087518768271837153721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47240116691691029116204961 35430087518768271837153721)
        ·
          refine ⟨26572565639076203877865291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35430087518768271837153721 26572565639076203877865291)
          ·
            refine ⟨39858848458614305816797937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26572565639076203877865291 39858848458614305816797937)
            ·
              refine ⟨29894136343960729362598453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39858848458614305816797937 29894136343960729362598453)
              ·
                refine ⟨2802575282246318377743605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29894136343960729362598453 2802575282246318377743605)
                ·
                  refine ⟨262741432710592347913463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2802575282246318377743605 262741432710592347913463)
                  ·
                    rfl

theorem cell21_1151296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_1151296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151296 prefixEnd_1151296 := by exact prefixLift 1151296
  have htrace : WordTrace (prefixWord ++ tailWord_1151296) baseStart_1151296 baseEnd_1151296 := by
    simpa [prefixWord, tailWord_1151296, baseEnd_1151296] using wordTrace_append hprefix tailTrace_1151296
  have hstable : (prefixWord ++ tailWord_1151296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151296).length < 2 ^ (prefixWord ++ tailWord_1151296).sum := by decide
  have hdescent : baseEnd_1151296 < baseStart_1151296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151344 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_1151344 : Nat := 118140960795 + 1151344 * 2 ^ 59
def prefixEnd_1151344 : Nat := 4983230072969 + 3 ^ 40 * 1151344 * 2
def baseEnd_1151344 : Nat := 262752386964554931113365

theorem tailTrace_1151344 : CollatzResearch.WordTrace tailWord_1151344 prefixEnd_1151344 262752386964554931113365 := by
  unfold tailWord_1151344
  simp only [CollatzResearch.WordTrace]
  refine ⟨20996482770442398372742543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27995310360589864496990057 20996482770442398372742543)
  ·
    refine ⟨31494724155663597559113815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20996482770442398372742543 31494724155663597559113815)
    ·
      refine ⟨47242086233495396338670723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31494724155663597559113815 47242086233495396338670723)
      ·
        refine ⟨70863129350243094508006085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47242086233495396338670723 70863129350243094508006085)
        ·
          refine ⟨13286836753170580220251141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70863129350243094508006085 13286836753170580220251141)
          ·
            refine ⟨2491281891219483791297089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13286836753170580220251141 2491281891219483791297089)
            ·
              refine ⟨1868461418414612843472817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2491281891219483791297089 1868461418414612843472817)
              ·
                refine ⟨1401346063810959632604613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1868461418414612843472817 1401346063810959632604613)
                ·
                  refine ⟨262752386964554931113365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401346063810959632604613 262752386964554931113365)
                  ·
                    rfl

theorem cell21_1151344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_1151344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151344 prefixEnd_1151344 := by exact prefixLift 1151344
  have htrace : WordTrace (prefixWord ++ tailWord_1151344) baseStart_1151344 baseEnd_1151344 := by
    simpa [prefixWord, tailWord_1151344, baseEnd_1151344] using wordTrace_append hprefix tailTrace_1151344
  have hstable : (prefixWord ++ tailWord_1151344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151344).length < 2 ^ (prefixWord ++ tailWord_1151344).sum := by decide
  have hdescent : baseEnd_1151344 < baseStart_1151344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151372 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_1151372 : Nat := 118140960795 + 1151372 * 2 ^ 59
def prefixEnd_1151372 : Nat := 4983230072969 + 3 ^ 40 * 1151372 * 2
def baseEnd_1151372 : Nat := 262758776946033104646641

theorem tailTrace_1151372 : CollatzResearch.WordTrace tailWord_1151372 prefixEnd_1151372 262758776946033104646641 := by
  unfold tailWord_1151372
  simp only [CollatzResearch.WordTrace]
  refine ⟨20996993392391678763752185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27995991189855571685002913 20996993392391678763752185)
  ·
    refine ⟨15747745044293759072814139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20996993392391678763752185 15747745044293759072814139)
    ·
      refine ⟨23621617566440638609221209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15747745044293759072814139 23621617566440638609221209)
      ·
        refine ⟨17716213174830478956915907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23621617566440638609221209 17716213174830478956915907)
        ·
          refine ⟨26574319762245718435373861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17716213174830478956915907 26574319762245718435373861)
          ·
            refine ⟨4982684955421072206632599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26574319762245718435373861 4982684955421072206632599)
            ·
              refine ⟨7474027433131608309948899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4982684955421072206632599 7474027433131608309948899)
              ·
                refine ⟨11211041149697412464923349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7474027433131608309948899 11211041149697412464923349)
                ·
                  refine ⟨262758776946033104646641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11211041149697412464923349 262758776946033104646641)
                  ·
                    rfl

theorem cell21_1151372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_1151372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151372 prefixEnd_1151372 := by exact prefixLift 1151372
  have htrace : WordTrace (prefixWord ++ tailWord_1151372) baseStart_1151372 baseEnd_1151372 := by
    simpa [prefixWord, tailWord_1151372, baseEnd_1151372] using wordTrace_append hprefix tailTrace_1151372
  have hstable : (prefixWord ++ tailWord_1151372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151372).length < 2 ^ (prefixWord ++ tailWord_1151372).sum := by decide
  have hdescent : baseEnd_1151372 < baseStart_1151372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151493 : List Nat := [1, 3, 1, 1, 2, 2, 4, 7]
def baseStart_1151493 : Nat := 118140960795 + 1151493 * 2 ^ 59
def prefixEnd_1151493 : Nat := 4983230072969 + 3 ^ 40 * 1151493 * 2
def baseEnd_1151493 : Nat := 87595463598187927709909

theorem tailTrace_1151493 : CollatzResearch.WordTrace tailWord_1151493 prefixEnd_1151493 87595463598187927709909 := by
  unfold tailWord_1151493
  simp only [CollatzResearch.WordTrace]
  refine ⟨41998400017344995192659133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27998933344896663461772755 41998400017344995192659133)
  ·
    refine ⟨15749400006504373197247175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41998400017344995192659133 15749400006504373197247175)
    ·
      refine ⟨23624100009756559795870763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15749400006504373197247175 23624100009756559795870763)
      ·
        refine ⟨35436150014634839693806145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23624100009756559795870763 35436150014634839693806145)
        ·
          refine ⟨26577112510976129770354609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35436150014634839693806145 26577112510976129770354609)
          ·
            refine ⟨19932834383232097327765957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26577112510976129770354609 19932834383232097327765957)
            ·
              refine ⟨3737406446856018248956117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19932834383232097327765957 3737406446856018248956117)
              ·
                refine ⟨87595463598187927709909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3737406446856018248956117 87595463598187927709909)
                ·
                  rfl

theorem cell21_1151493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 7].length) (baseStart_1151493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151493 prefixEnd_1151493 := by exact prefixLift 1151493
  have htrace : WordTrace (prefixWord ++ tailWord_1151493) baseStart_1151493 baseEnd_1151493 := by
    simpa [prefixWord, tailWord_1151493, baseEnd_1151493] using wordTrace_append hprefix tailTrace_1151493
  have hstable : (prefixWord ++ tailWord_1151493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151493).length < 2 ^ (prefixWord ++ tailWord_1151493).sum := by decide
  have hdescent : baseEnd_1151493 < baseStart_1151493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151569 : List Nat := [1, 2, 2, 1, 3, 4, 8]
def baseStart_1151569 : Nat := 118140960795 + 1151569 * 2 ^ 59
def prefixEnd_1151569 : Nat := 4983230072969 + 3 ^ 40 * 1151569 * 2
def baseEnd_1151569 : Nat := 29200415003333837762545

theorem tailTrace_1151569 : CollatzResearch.WordTrace tailWord_1151569 prefixEnd_1151569 29200415003333837762545 := by
  unfold tailWord_1151569
  simp only [CollatzResearch.WordTrace]
  refine ⟨42001171965069660172425761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28000781310046440114950507 42001171965069660172425761)
  ·
    refine ⟨31500878973802245129319321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42001171965069660172425761 31500878973802245129319321)
    ·
      refine ⟨23625659230351683846989491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31500878973802245129319321 23625659230351683846989491)
      ·
        refine ⟨35438488845527525770484237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23625659230351683846989491 35438488845527525770484237)
        ·
          refine ⟨13289433317072822163931589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35438488845527525770484237 13289433317072822163931589)
          ·
            refine ⟨2491768746951154155737173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13289433317072822163931589 2491768746951154155737173)
            ·
              refine ⟨29200415003333837762545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2491768746951154155737173 29200415003333837762545)
              ·
                rfl

theorem cell21_1151569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 8].length) (baseStart_1151569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151569 prefixEnd_1151569 := by exact prefixLift 1151569
  have htrace : WordTrace (prefixWord ++ tailWord_1151569) baseStart_1151569 baseEnd_1151569 := by
    simpa [prefixWord, tailWord_1151569, baseEnd_1151569] using wordTrace_append hprefix tailTrace_1151569
  have hstable : (prefixWord ++ tailWord_1151569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151569).length < 2 ^ (prefixWord ++ tailWord_1151569).sum := by decide
  have hdescent : baseEnd_1151569 < baseStart_1151569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151572 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1151572 : Nat := 118140960795 + 1151572 * 2 ^ 59
def prefixEnd_1151572 : Nat := 4983230072969 + 3 ^ 40 * 1151572 * 2
def baseEnd_1151572 : Nat := 262804419670877201312899

theorem tailTrace_1151572 : CollatzResearch.WordTrace tailWord_1151572 prefixEnd_1151572 262804419670877201312899 := by
  unfold tailWord_1151572
  simp only [CollatzResearch.WordTrace]
  refine ⟨21000640692029395842392485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28000854256039194456523313 21000640692029395842392485)
  ·
    refine ⟨3937620129755511720448591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21000640692029395842392485 3937620129755511720448591)
    ·
      refine ⟨5906430194633267580672887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3937620129755511720448591 5906430194633267580672887)
      ·
        refine ⟨8859645291949901371009331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5906430194633267580672887 8859645291949901371009331)
        ·
          refine ⟨13289467937924852056513997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8859645291949901371009331 13289467937924852056513997)
          ·
            refine ⟨4983550476721819521192749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13289467937924852056513997 4983550476721819521192749)
            ·
              refine ⟨1868831428770682320447281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4983550476721819521192749 1868831428770682320447281)
              ·
                refine ⟨1401623571578011740335461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1868831428770682320447281 1401623571578011740335461)
                ·
                  refine ⟨262804419670877201312899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401623571578011740335461 262804419670877201312899)
                  ·
                    rfl

theorem cell21_1151572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1151572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151572 prefixEnd_1151572 := by exact prefixLift 1151572
  have htrace : WordTrace (prefixWord ++ tailWord_1151572) baseStart_1151572 baseEnd_1151572 := by
    simpa [prefixWord, tailWord_1151572, baseEnd_1151572] using wordTrace_append hprefix tailTrace_1151572
  have hstable : (prefixWord ++ tailWord_1151572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151572).length < 2 ^ (prefixWord ++ tailWord_1151572).sum := by decide
  have hdescent : baseEnd_1151572 < baseStart_1151572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151589 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 4]
def baseStart_1151589 : Nat := 118140960795 + 1151589 * 2 ^ 59
def prefixEnd_1151589 : Nat := 4983230072969 + 3 ^ 40 * 1151589 * 2
def baseEnd_1151589 : Nat := 262808299302488949529531

theorem tailTrace_1151589 : CollatzResearch.WordTrace tailWord_1151589 prefixEnd_1151589 262808299302488949529531 := by
  unfold tailWord_1151589
  simp only [CollatzResearch.WordTrace]
  refine ⟨42001901424997203588153821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28001267616664802392102547 42001901424997203588153821)
  ·
    refine ⟨15750713034373951345557683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42001901424997203588153821 15750713034373951345557683)
    ·
      refine ⟨23626069551560927018336525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15750713034373951345557683 23626069551560927018336525)
      ·
        refine ⟨8859776081835347631876197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23626069551560927018336525 8859776081835347631876197)
        ·
          refine ⟨1661208015344127680976787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8859776081835347631876197 1661208015344127680976787)
          ·
            refine ⟨2491812023016191521465181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661208015344127680976787 2491812023016191521465181)
            ·
              refine ⟨934429508631071820549443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2491812023016191521465181 934429508631071820549443)
              ·
                refine ⟨1401644262946607730824165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934429508631071820549443 1401644262946607730824165)
                ·
                  refine ⟨262808299302488949529531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401644262946607730824165 262808299302488949529531)
                  ·
                    rfl

theorem cell21_1151589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_1151589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151589 prefixEnd_1151589 := by exact prefixLift 1151589
  have htrace : WordTrace (prefixWord ++ tailWord_1151589) baseStart_1151589 baseEnd_1151589 := by
    simpa [prefixWord, tailWord_1151589, baseEnd_1151589] using wordTrace_append hprefix tailTrace_1151589
  have hstable : (prefixWord ++ tailWord_1151589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151589).length < 2 ^ (prefixWord ++ tailWord_1151589).sum := by decide
  have hdescent : baseEnd_1151589 < baseStart_1151589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151634 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_1151634 : Nat := 118140960795 + 1151634 * 2 ^ 59
def prefixEnd_1151634 : Nat := 4983230072969 + 3 ^ 40 * 1151634 * 2
def baseEnd_1151634 : Nat := 262818568915578871279439

theorem tailTrace_1151634 : CollatzResearch.WordTrace tailWord_1151634 prefixEnd_1151634 262818568915578871279439 := by
  unfold tailWord_1151634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10500885677458544068385489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28002361806556117515694637 10500885677458544068385489)
  ·
    refine ⟨7875664258093908051289117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10500885677458544068385489 7875664258093908051289117)
    ·
      refine ⟨2953374096785215519233419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7875664258093908051289117 2953374096785215519233419)
      ·
        refine ⟨4430061145177823278850129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2953374096785215519233419 4430061145177823278850129)
        ·
          refine ⟨3322545858883367459137597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4430061145177823278850129 3322545858883367459137597)
          ·
            refine ⟨1245954697081262797176599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3322545858883367459137597 1245954697081262797176599)
            ·
              refine ⟨1868932045621894195764899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245954697081262797176599 1868932045621894195764899)
              ·
                refine ⟨2803398068432841293647349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868932045621894195764899 2803398068432841293647349)
                ·
                  refine ⟨262818568915578871279439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2803398068432841293647349 262818568915578871279439)
                  ·
                    rfl

theorem cell21_1151634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_1151634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151634 prefixEnd_1151634 := by exact prefixLift 1151634
  have htrace : WordTrace (prefixWord ++ tailWord_1151634) baseStart_1151634 baseEnd_1151634 := by
    simpa [prefixWord, tailWord_1151634, baseEnd_1151634] using wordTrace_append hprefix tailTrace_1151634
  have hstable : (prefixWord ++ tailWord_1151634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151634).length < 2 ^ (prefixWord ++ tailWord_1151634).sum := by decide
  have hdescent : baseEnd_1151634 < baseStart_1151634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151645 : List Nat := [1, 4, 2, 1, 1, 1, 3, 8]
def baseStart_1151645 : Nat := 118140960795 + 1151645 * 2 ^ 59
def prefixEnd_1151645 : Nat := 4983230072969 + 3 ^ 40 * 1151645 * 2
def baseEnd_1151645 : Nat := 87607026421815098865361

theorem tailTrace_1151645 : CollatzResearch.WordTrace tailWord_1151645 prefixEnd_1151645 87607026421815098865361 := by
  unfold tailWord_1151645
  simp only [CollatzResearch.WordTrace]
  refine ⟨42003943912794325152192389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28002629275196216768128259 42003943912794325152192389)
  ·
    refine ⟨7875739483648935966036073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42003943912794325152192389 7875739483648935966036073)
    ·
      refine ⟨5906804612736701974527055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7875739483648935966036073 5906804612736701974527055)
      ·
        refine ⟨8860206919105052961790583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5906804612736701974527055 8860206919105052961790583)
        ·
          refine ⟨13290310378657579442685875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8860206919105052961790583 13290310378657579442685875)
          ·
            refine ⟨19935465567986369164028813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13290310378657579442685875 19935465567986369164028813)
            ·
              refine ⟨7475799587994888436510805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19935465567986369164028813 7475799587994888436510805)
              ·
                refine ⟨87607026421815098865361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7475799587994888436510805 87607026421815098865361)
                ·
                  rfl

theorem cell21_1151645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 8].length) (baseStart_1151645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151645 prefixEnd_1151645 := by exact prefixLift 1151645
  have htrace : WordTrace (prefixWord ++ tailWord_1151645) baseStart_1151645 baseEnd_1151645 := by
    simpa [prefixWord, tailWord_1151645, baseEnd_1151645] using wordTrace_append hprefix tailTrace_1151645
  have hstable : (prefixWord ++ tailWord_1151645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151645).length < 2 ^ (prefixWord ++ tailWord_1151645).sum := by decide
  have hdescent : baseEnd_1151645 < baseStart_1151645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151648 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_1151648 : Nat := 118140960795 + 1151648 * 2 ^ 59
def prefixEnd_1151648 : Nat := 4983230072969 + 3 ^ 40 * 1151648 * 2
def baseEnd_1151648 : Nat := 262821763906317958046077

theorem tailTrace_1151648 : CollatzResearch.WordTrace tailWord_1151648 prefixEnd_1151648 262821763906317958046077 := by
  unfold tailWord_1151648
  simp only [CollatzResearch.WordTrace]
  refine ⟨21002026665891728332275799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28002702221188971109701065 21002026665891728332275799)
  ·
    refine ⟨31503039998837592498413699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21002026665891728332275799 31503039998837592498413699)
    ·
      refine ⟨47254559998256388747620549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31503039998837592498413699 47254559998256388747620549)
      ·
        refine ⟨8860229999673072890178853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47254559998256388747620549 8860229999673072890178853)
        ·
          refine ⟨1661293124938701166908535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8860229999673072890178853 1661293124938701166908535)
          ·
            refine ⟨2491939687408051750362803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661293124938701166908535 2491939687408051750362803)
            ·
              refine ⟨3737909531112077625544205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491939687408051750362803 3737909531112077625544205)
              ·
                refine ⟨1401716074167029109579077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3737909531112077625544205 1401716074167029109579077)
                ·
                  refine ⟨262821763906317958046077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401716074167029109579077 262821763906317958046077)
                  ·
                    rfl

theorem cell21_1151648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_1151648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151648 prefixEnd_1151648 := by exact prefixLift 1151648
  have htrace : WordTrace (prefixWord ++ tailWord_1151648) baseStart_1151648 baseEnd_1151648 := by
    simpa [prefixWord, tailWord_1151648, baseEnd_1151648] using wordTrace_append hprefix tailTrace_1151648
  have hstable : (prefixWord ++ tailWord_1151648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151648).length < 2 ^ (prefixWord ++ tailWord_1151648).sum := by decide
  have hdescent : baseEnd_1151648 < baseStart_1151648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151735 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 9]
def baseStart_1151735 : Nat := 118140960795 + 1151735 * 2 ^ 59
def prefixEnd_1151735 : Nat := 4983230072969 + 3 ^ 40 * 1151735 * 2
def baseEnd_1151735 : Nat := 262841618491625140095899

theorem tailTrace_1151735 : CollatzResearch.WordTrace tailWord_1151735 prefixEnd_1151735 262841618491625140095899 := by
  unfold tailWord_1151735
  simp only [CollatzResearch.WordTrace]
  refine ⟨42007226482468270522968659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28004817654978847015312439 42007226482468270522968659)
  ·
    refine ⟨63010839723702405784452989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42007226482468270522968659 63010839723702405784452989)
    ·
      refine ⟨23629064896388402169169871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63010839723702405784452989 23629064896388402169169871)
      ·
        refine ⟨35443597344582603253754807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23629064896388402169169871 35443597344582603253754807)
        ·
          refine ⟨53165396016873904880632211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35443597344582603253754807 53165396016873904880632211)
          ·
            refine ⟨79748094025310857320948317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53165396016873904880632211 79748094025310857320948317)
            ·
              refine ⟨29905535259491571495355619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79748094025310857320948317 29905535259491571495355619)
              ·
                refine ⟨44858302889237357243033429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29905535259491571495355619 44858302889237357243033429)
                ·
                  refine ⟨262841618491625140095899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44858302889237357243033429 262841618491625140095899)
                  ·
                    rfl

theorem cell21_1151735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_1151735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151735 prefixEnd_1151735 := by exact prefixLift 1151735
  have htrace : WordTrace (prefixWord ++ tailWord_1151735) baseStart_1151735 baseEnd_1151735 := by
    simpa [prefixWord, tailWord_1151735, baseEnd_1151735] using wordTrace_append hprefix tailTrace_1151735
  have hstable : (prefixWord ++ tailWord_1151735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151735).length < 2 ^ (prefixWord ++ tailWord_1151735).sum := by decide
  have hdescent : baseEnd_1151735 < baseStart_1151735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151752 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_1151752 : Nat := 118140960795 + 1151752 * 2 ^ 59
def prefixEnd_1151752 : Nat := 4983230072969 + 3 ^ 40 * 1151752 * 2
def baseEnd_1151752 : Nat := 262845498123236888312531

theorem tailTrace_1151752 : CollatzResearch.WordTrace tailWord_1151752 prefixEnd_1151752 262845498123236888312531 := by
  unfold tailWord_1151752
  simp only [CollatzResearch.WordTrace]
  refine ⟨21003923261703341213168755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28005231015604454950891673 21003923261703341213168755)
  ·
    refine ⟨31505884892555011819753133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21003923261703341213168755 31505884892555011819753133)
    ·
      refine ⟨11814706834708129432407425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31505884892555011819753133 11814706834708129432407425)
      ·
        refine ⟨8861030126031097074305569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11814706834708129432407425 8861030126031097074305569)
        ·
          refine ⟨6645772594523322805729177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8861030126031097074305569 6645772594523322805729177)
          ·
            refine ⟨4984329445892492104296883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6645772594523322805729177 4984329445892492104296883)
            ·
              refine ⟨7476494168838738156445325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984329445892492104296883 7476494168838738156445325)
              ·
                refine ⟨2803685313314526808666997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7476494168838738156445325 2803685313314526808666997)
                ·
                  refine ⟨262845498123236888312531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2803685313314526808666997 262845498123236888312531)
                  ·
                    rfl

theorem cell21_1151752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_1151752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151752 prefixEnd_1151752 := by exact prefixLift 1151752
  have htrace : WordTrace (prefixWord ++ tailWord_1151752) baseStart_1151752 baseEnd_1151752 := by
    simpa [prefixWord, tailWord_1151752, baseEnd_1151752] using wordTrace_append hprefix tailTrace_1151752
  have hstable : (prefixWord ++ tailWord_1151752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151752).length < 2 ^ (prefixWord ++ tailWord_1151752).sum := by decide
  have hdescent : baseEnd_1151752 < baseStart_1151752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151797 : List Nat := [1, 3, 3, 1, 3, 1, 9]
def baseStart_1151797 : Nat := 118140960795 + 1151797 * 2 ^ 59
def prefixEnd_1151797 : Nat := 4983230072969 + 3 ^ 40 * 1151797 * 2
def baseEnd_1151797 : Nat := 29206196415147423340271

theorem tailTrace_1151797 : CollatzResearch.WordTrace tailWord_1151797 prefixEnd_1151797 29206196415147423340271 := by
  unfold tailWord_1151797
  simp only [CollatzResearch.WordTrace]
  refine ⟨42009487808243655111725645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28006325205495770074483763 42009487808243655111725645)
  ·
    refine ⟨15753557928091370666897117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42009487808243655111725645 15753557928091370666897117)
    ·
      refine ⟨5907584223034264000086419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15753557928091370666897117 5907584223034264000086419)
      ·
        refine ⟨8861376334551396000129629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5907584223034264000086419 8861376334551396000129629)
        ·
          refine ⟨3323016125456773500048611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8861376334551396000129629 3323016125456773500048611)
          ·
            refine ⟨4984524188185160250072917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323016125456773500048611 4984524188185160250072917)
            ·
              refine ⟨29206196415147423340271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4984524188185160250072917 29206196415147423340271)
              ·
                rfl

theorem cell21_1151797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 9].length) (baseStart_1151797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151797 prefixEnd_1151797 := by exact prefixLift 1151797
  have htrace : WordTrace (prefixWord ++ tailWord_1151797) baseStart_1151797 baseEnd_1151797 := by
    simpa [prefixWord, tailWord_1151797, baseEnd_1151797] using wordTrace_append hprefix tailTrace_1151797
  have hstable : (prefixWord ++ tailWord_1151797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151797).length < 2 ^ (prefixWord ++ tailWord_1151797).sum := by decide
  have hdescent : baseEnd_1151797 < baseStart_1151797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151921 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 5]
def baseStart_1151921 : Nat := 118140960795 + 1151921 * 2 ^ 59
def prefixEnd_1151921 : Nat := 4983230072969 + 3 ^ 40 * 1151921 * 2
def baseEnd_1151921 : Nat := 262884066225730149995519

theorem tailTrace_1151921 : CollatzResearch.WordTrace tailWord_1151921 prefixEnd_1151921 262884066225730149995519 := by
  unfold tailWord_1151921
  simp only [CollatzResearch.WordTrace]
  refine ⟨42014010459794424289239617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28009340306529616192826411 42014010459794424289239617)
  ·
    refine ⟨31510507844845818216929713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42014010459794424289239617 31510507844845818216929713)
    ·
      refine ⟨23632880883634363662697285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31510507844845818216929713 23632880883634363662697285)
      ·
        refine ⟨4431165165681443186755741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23632880883634363662697285 4431165165681443186755741)
        ·
          refine ⟨1661686937130541195033403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4431165165681443186755741 1661686937130541195033403)
          ·
            refine ⟨2492530405695811792550105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661686937130541195033403 2492530405695811792550105)
            ·
              refine ⟨1869397804271858844412579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2492530405695811792550105 1869397804271858844412579)
              ·
                refine ⟨2804096706407788266618869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869397804271858844412579 2804096706407788266618869)
                ·
                  refine ⟨262884066225730149995519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2804096706407788266618869 262884066225730149995519)
                  ·
                    rfl

theorem cell21_1151921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_1151921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151921 prefixEnd_1151921 := by exact prefixLift 1151921
  have htrace : WordTrace (prefixWord ++ tailWord_1151921) baseStart_1151921 baseEnd_1151921 := by
    simpa [prefixWord, tailWord_1151921, baseEnd_1151921] using wordTrace_append hprefix tailTrace_1151921
  have hstable : (prefixWord ++ tailWord_1151921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151921).length < 2 ^ (prefixWord ++ tailWord_1151921).sum := by decide
  have hdescent : baseEnd_1151921 < baseStart_1151921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151986 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_1151986 : Nat := 118140960795 + 1151986 * 2 ^ 59
def prefixEnd_1151986 : Nat := 4983230072969 + 3 ^ 40 * 1151986 * 2
def baseEnd_1151986 : Nat := 262898900111304481412053

theorem tailTrace_1151986 : CollatzResearch.WordTrace tailWord_1151986 prefixEnd_1151986 262898900111304481412053 := by
  unfold tailWord_1151986
  simp only [CollatzResearch.WordTrace]
  refine ⟨10504095301139735097588953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28010920803039293593570541 10504095301139735097588953)
  ·
    refine ⟨7878071475854801323191715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10504095301139735097588953 7878071475854801323191715)
    ·
      refine ⟨11817107213782201984787573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7878071475854801323191715 11817107213782201984787573)
      ·
        refine ⟨1107853801292081436073835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11817107213782201984787573 1107853801292081436073835)
        ·
          refine ⟨1661780701938122154110753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107853801292081436073835 1661780701938122154110753)
          ·
            refine ⟨1246335526453591615583065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1661780701938122154110753 1246335526453591615583065)
            ·
              refine ⟨934751644840193711687299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246335526453591615583065 934751644840193711687299)
              ·
                refine ⟨1402127467260290567530949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934751644840193711687299 1402127467260290567530949)
                ·
                  refine ⟨262898900111304481412053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402127467260290567530949 262898900111304481412053)
                  ·
                    rfl

theorem cell21_1151986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_1151986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1151986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1151986 prefixEnd_1151986 := by exact prefixLift 1151986
  have htrace : WordTrace (prefixWord ++ tailWord_1151986) baseStart_1151986 baseEnd_1151986 := by
    simpa [prefixWord, tailWord_1151986, baseEnd_1151986] using wordTrace_append hprefix tailTrace_1151986
  have hstable : (prefixWord ++ tailWord_1151986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151986).length < 2 ^ (prefixWord ++ tailWord_1151986).sum := by decide
  have hdescent : baseEnd_1151986 < baseStart_1151986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152028 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_1152028 : Nat := 118140960795 + 1152028 * 2 ^ 59
def prefixEnd_1152028 : Nat := 4983230072969 + 3 ^ 40 * 1152028 * 2
def baseEnd_1152028 : Nat := 262908485083521741711967

theorem tailTrace_1152028 : CollatzResearch.WordTrace tailWord_1152028 prefixEnd_1152028 262908485083521741711967 := by
  unfold tailWord_1152028
  simp only [CollatzResearch.WordTrace]
  refine ⟨21008956535203390781692369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28011942046937854375589825 21008956535203390781692369)
  ·
    refine ⟨15756717401402543086269277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21008956535203390781692369 15756717401402543086269277)
    ·
      refine ⟨5908769025525953657350979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15756717401402543086269277 5908769025525953657350979)
      ·
        refine ⟨8863153538288930486026469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5908769025525953657350979 8863153538288930486026469)
        ·
          refine ⟨1661841288429174466129963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8863153538288930486026469 1661841288429174466129963)
          ·
            refine ⟨2492761932643761699194945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661841288429174466129963 2492761932643761699194945)
            ·
              refine ⟨1869571449482821274396209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2492761932643761699194945 1869571449482821274396209)
              ·
                refine ⟨1402178587112115955797157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1869571449482821274396209 1402178587112115955797157)
                ·
                  refine ⟨262908485083521741711967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402178587112115955797157 262908485083521741711967)
                  ·
                    rfl

theorem cell21_1152028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_1152028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152028 prefixEnd_1152028 := by exact prefixLift 1152028
  have htrace : WordTrace (prefixWord ++ tailWord_1152028) baseStart_1152028 baseEnd_1152028 := by
    simpa [prefixWord, tailWord_1152028, baseEnd_1152028] using wordTrace_append hprefix tailTrace_1152028
  have hstable : (prefixWord ++ tailWord_1152028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152028).length < 2 ^ (prefixWord ++ tailWord_1152028).sum := by decide
  have hdescent : baseEnd_1152028 < baseStart_1152028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152056 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_1152056 : Nat := 118140960795 + 1152056 * 2 ^ 59
def prefixEnd_1152056 : Nat := 4983230072969 + 3 ^ 40 * 1152056 * 2
def baseEnd_1152056 : Nat := 262914875064999915245243

theorem tailTrace_1152056 : CollatzResearch.WordTrace tailWord_1152056 prefixEnd_1152056 262914875064999915245243 := by
  unfold tailWord_1152056
  simp only [CollatzResearch.WordTrace]
  refine ⟨21009467157152671172702011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28012622876203561563602681 21009467157152671172702011)
  ·
    refine ⟨31514200735729006759053017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21009467157152671172702011 31514200735729006759053017)
    ·
      refine ⟨23635650551796755069289763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31514200735729006759053017 23635650551796755069289763)
      ·
        refine ⟨35453475827695132603934645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23635650551796755069289763 35453475827695132603934645)
        ·
          refine ⟨3323763358846418681618873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35453475827695132603934645 3323763358846418681618873)
          ·
            refine ⟨2492822519134814011214155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3323763358846418681618873 2492822519134814011214155)
            ·
              refine ⟨3739233778702221016821233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492822519134814011214155 3739233778702221016821233)
              ·
                refine ⟨2804425334026665762615925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3739233778702221016821233 2804425334026665762615925)
                ·
                  refine ⟨262914875064999915245243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2804425334026665762615925 262914875064999915245243)
                  ·
                    rfl

theorem cell21_1152056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_1152056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152056 prefixEnd_1152056 := by exact prefixLift 1152056
  have htrace : WordTrace (prefixWord ++ tailWord_1152056) baseStart_1152056 baseEnd_1152056 := by
    simpa [prefixWord, tailWord_1152056, baseEnd_1152056] using wordTrace_append hprefix tailTrace_1152056
  have hstable : (prefixWord ++ tailWord_1152056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152056).length < 2 ^ (prefixWord ++ tailWord_1152056).sum := by decide
  have hdescent : baseEnd_1152056 < baseStart_1152056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152177 : List Nat := [1, 2, 2, 5, 1, 1, 2, 7]
def baseStart_1152177 : Nat := 118140960795 + 1152177 * 2 ^ 59
def prefixEnd_1152177 : Nat := 4983230072969 + 3 ^ 40 * 1152177 * 2
def baseEnd_1152177 : Nat := 87647496304510197909443

theorem tailTrace_1152177 : CollatzResearch.WordTrace tailWord_1152177 prefixEnd_1152177 87647496304510197909443 := by
  unfold tailWord_1152177
  simp only [CollatzResearch.WordTrace]
  refine ⟨42023347546866980010558785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28015565031244653340372523 42023347546866980010558785)
  ·
    refine ⟨31517510660150235007919089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42023347546866980010558785 31517510660150235007919089)
    ·
      refine ⟨23638132995112676255939317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31517510660150235007919089 23638132995112676255939317)
      ·
        refine ⟨2216074968291813398994311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23638132995112676255939317 2216074968291813398994311)
        ·
          refine ⟨3324112452437720098491467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216074968291813398994311 3324112452437720098491467)
          ·
            refine ⟨4986168678656580147737201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324112452437720098491467 4986168678656580147737201)
            ·
              refine ⟨3739626508992435110802901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4986168678656580147737201 3739626508992435110802901)
              ·
                refine ⟨87647496304510197909443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3739626508992435110802901 87647496304510197909443)
                ·
                  rfl

theorem cell21_1152177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 7].length) (baseStart_1152177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152177 prefixEnd_1152177 := by exact prefixLift 1152177
  have htrace : WordTrace (prefixWord ++ tailWord_1152177) baseStart_1152177 baseEnd_1152177 := by
    simpa [prefixWord, tailWord_1152177, baseEnd_1152177] using wordTrace_append hprefix tailTrace_1152177
  have hstable : (prefixWord ++ tailWord_1152177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152177).length < 2 ^ (prefixWord ++ tailWord_1152177).sum := by decide
  have hdescent : baseEnd_1152177 < baseStart_1152177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152194 : List Nat := [3, 5, 1, 1, 11]
def baseStart_1152194 : Nat := 118140960795 + 1152194 * 2 ^ 59
def prefixEnd_1152194 : Nat := 4983230072969 + 3 ^ 40 * 1152194 * 2
def baseEnd_1152194 : Nat := 3246251463520275826481

theorem tailTrace_1152194 : CollatzResearch.WordTrace tailWord_1152194 prefixEnd_1152194 3246251463520275826481 := by
  unfold tailWord_1152194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10505991896951347978481909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28015978391870261275951757 10505991896951347978481909)
  ·
    refine ⟨984936740339188872982679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10505991896951347978481909 984936740339188872982679)
    ·
      refine ⟨1477405110508783309474019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984936740339188872982679 1477405110508783309474019)
      ·
        refine ⟨2216107665763174964211029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477405110508783309474019 2216107665763174964211029)
        ·
          refine ⟨3246251463520275826481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2216107665763174964211029 3246251463520275826481)
          ·
            rfl

theorem cell21_1152194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 11].length) (baseStart_1152194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152194 prefixEnd_1152194 := by exact prefixLift 1152194
  have htrace : WordTrace (prefixWord ++ tailWord_1152194) baseStart_1152194 baseEnd_1152194 := by
    simpa [prefixWord, tailWord_1152194, baseEnd_1152194] using wordTrace_append hprefix tailTrace_1152194
  have hstable : (prefixWord ++ tailWord_1152194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152194).length < 2 ^ (prefixWord ++ tailWord_1152194).sum := by decide
  have hdescent : baseEnd_1152194 < baseStart_1152194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152242 : List Nat := [3, 2, 1, 3, 3, 1, 2, 3, 3]
def baseStart_1152242 : Nat := 118140960795 + 1152242 * 2 ^ 59
def prefixEnd_1152242 : Nat := 4983230072969 + 3 ^ 40 * 1152242 * 2
def baseEnd_1152242 : Nat := 262957322799104925144863

theorem tailTrace_1152242 : CollatzResearch.WordTrace tailWord_1152242 prefixEnd_1152242 262957322799104925144863 := by
  unfold tailWord_1152242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10506429572907874027918745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28017145527754330741116653 10506429572907874027918745)
  ·
    refine ⟨7879822179680905520939059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10506429572907874027918745 7879822179680905520939059)
    ·
      refine ⟨11819733269521358281408589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7879822179680905520939059 11819733269521358281408589)
      ·
        refine ⟨4432399976070509355528221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11819733269521358281408589 4432399976070509355528221)
        ·
          refine ⟨1662149991026441008323083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4432399976070509355528221 1662149991026441008323083)
          ·
            refine ⟨2493224986539661512484625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662149991026441008323083 2493224986539661512484625)
            ·
              refine ⟨1869918739904746134363469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2493224986539661512484625 1869918739904746134363469)
              ·
                refine ⟨701219527464279800386301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1869918739904746134363469 701219527464279800386301)
                ·
                  refine ⟨262957322799104925144863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701219527464279800386301 262957322799104925144863)
                  ·
                    rfl

theorem cell21_1152242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_1152242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152242 prefixEnd_1152242 := by exact prefixLift 1152242
  have htrace : WordTrace (prefixWord ++ tailWord_1152242) baseStart_1152242 baseEnd_1152242 := by
    simpa [prefixWord, tailWord_1152242, baseEnd_1152242] using wordTrace_append hprefix tailTrace_1152242
  have hstable : (prefixWord ++ tailWord_1152242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152242).length < 2 ^ (prefixWord ++ tailWord_1152242).sum := by decide
  have hdescent : baseEnd_1152242 < baseStart_1152242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152267 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 5]
def baseStart_1152267 : Nat := 118140960795 + 1152267 * 2 ^ 59
def prefixEnd_1152267 : Nat := 4983230072969 + 3 ^ 40 * 1152267 * 2
def baseEnd_1152267 : Nat := 262963028139710437228145

theorem tailTrace_1152267 : CollatzResearch.WordTrace tailWord_1152267 prefixEnd_1152267 262963028139710437228145 := by
  unfold tailWord_1152267
  simp only [CollatzResearch.WordTrace]
  refine ⟨42026630116540925381335055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28017753411027283587556703 42026630116540925381335055)
  ·
    refine ⟨63039945174811388072002583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42026630116540925381335055 63039945174811388072002583)
    ·
      refine ⟨94559917762217082108003875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63039945174811388072002583 94559917762217082108003875)
      ·
        refine ⟨141839876643325623162005813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94559917762217082108003875 141839876643325623162005813)
        ·
          refine ⟨13297488435311777171438045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141839876643325623162005813 13297488435311777171438045)
          ·
            refine ⟨4986558163241916439289267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13297488435311777171438045 4986558163241916439289267)
            ·
              refine ⟨7479837244862874658933901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4986558163241916439289267 7479837244862874658933901)
              ·
                refine ⟨2804938966823577997100213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7479837244862874658933901 2804938966823577997100213)
                ·
                  refine ⟨262963028139710437228145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2804938966823577997100213 262963028139710437228145)
                  ·
                    rfl

theorem cell21_1152267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_1152267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152267 prefixEnd_1152267 := by exact prefixLift 1152267
  have htrace : WordTrace (prefixWord ++ tailWord_1152267) baseStart_1152267 baseEnd_1152267 := by
    simpa [prefixWord, tailWord_1152267, baseEnd_1152267] using wordTrace_append hprefix tailTrace_1152267
  have hstable : (prefixWord ++ tailWord_1152267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152267).length < 2 ^ (prefixWord ++ tailWord_1152267).sum := by decide
  have hdescent : baseEnd_1152267 < baseStart_1152267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152287 : List Nat := [1, 1, 2, 4, 5, 1, 2, 5]
def baseStart_1152287 : Nat := 118140960795 + 1152287 * 2 ^ 59
def prefixEnd_1152287 : Nat := 4983230072969 + 3 ^ 40 * 1152287 * 2
def baseEnd_1152287 : Nat := 87655864137398282298257

theorem tailTrace_1152287 : CollatzResearch.WordTrace tailWord_1152287 prefixEnd_1152287 87655864137398282298257 := by
  unfold tailWord_1152287
  simp only [CollatzResearch.WordTrace]
  refine ⟨42027359576468468797063115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28018239717645645864708743 42027359576468468797063115)
  ·
    refine ⟨63041039364702703195594673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42027359576468468797063115 63041039364702703195594673)
    ·
      refine ⟨47280779523527027396696005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63041039364702703195594673 47280779523527027396696005)
      ·
        refine ⟨8865146160661317636880501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47280779523527027396696005 8865146160661317636880501)
        ·
          refine ⟨831107452561998528457547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8865146160661317636880501 831107452561998528457547)
          ·
            refine ⟨1246661178842997792686321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831107452561998528457547 1246661178842997792686321)
            ·
              refine ⟨934995884132248344514741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246661178842997792686321 934995884132248344514741)
              ·
                refine ⟨87655864137398282298257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 934995884132248344514741 87655864137398282298257)
                ·
                  rfl

theorem cell21_1152287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 5].length) (baseStart_1152287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152287 prefixEnd_1152287 := by exact prefixLift 1152287
  have htrace : WordTrace (prefixWord ++ tailWord_1152287) baseStart_1152287 baseEnd_1152287 := by
    simpa [prefixWord, tailWord_1152287, baseEnd_1152287] using wordTrace_append hprefix tailTrace_1152287
  have hstable : (prefixWord ++ tailWord_1152287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152287).length < 2 ^ (prefixWord ++ tailWord_1152287).sum := by decide
  have hdescent : baseEnd_1152287 < baseStart_1152287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152318 : List Nat := [4, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_1152318 : Nat := 118140960795 + 1152318 * 2 ^ 59
def prefixEnd_1152318 : Nat := 4983230072969 + 3 ^ 40 * 1152318 * 2
def baseEnd_1152318 : Nat := 262974667034545681878041

theorem tailTrace_1152318 : CollatzResearch.WordTrace tailWord_1152318 prefixEnd_1152318 262974667034545681878041 := by
  unfold tailWord_1152318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5253561279919520136430201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28018993492904107394294405 5253561279919520136430201)
  ·
    refine ⟨3940170959939640102322651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5253561279919520136430201 3940170959939640102322651)
    ·
      refine ⟨5910256439909460153483977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3940170959939640102322651 5910256439909460153483977)
      ·
        refine ⟨4432692329932095115112983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5910256439909460153483977 4432692329932095115112983)
        ·
          refine ⟨6649038494898142672669475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4432692329932095115112983 6649038494898142672669475)
          ·
            refine ⟨9973557742347214009004213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6649038494898142672669475 9973557742347214009004213)
            ·
              refine ⟨935021038345051313344145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9973557742347214009004213 935021038345051313344145)
              ·
                refine ⟨701265778758788485008109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935021038345051313344145 701265778758788485008109)
                ·
                  refine ⟨262974667034545681878041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701265778758788485008109 262974667034545681878041)
                  ·
                    rfl

theorem cell21_1152318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_1152318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152318 prefixEnd_1152318 := by exact prefixLift 1152318
  have htrace : WordTrace (prefixWord ++ tailWord_1152318) baseStart_1152318 baseEnd_1152318 := by
    simpa [prefixWord, tailWord_1152318, baseEnd_1152318] using wordTrace_append hprefix tailTrace_1152318
  have hstable : (prefixWord ++ tailWord_1152318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152318).length < 2 ^ (prefixWord ++ tailWord_1152318).sum := by decide
  have hdescent : baseEnd_1152318 < baseStart_1152318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152332 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 4]
def baseStart_1152332 : Nat := 118140960795 + 1152332 * 2 ^ 59
def prefixEnd_1152332 : Nat := 4983230072969 + 3 ^ 40 * 1152332 * 2
def baseEnd_1152332 : Nat := 262977862025284768644679

theorem tailTrace_1152332 : CollatzResearch.WordTrace tailWord_1152332 prefixEnd_1152332 262977862025284768644679 := by
  unfold tailWord_1152332
  simp only [CollatzResearch.WordTrace]
  refine ⟨21014500430652720741225625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28019333907536960988300833 21014500430652720741225625)
  ·
    refine ⟨15760875322989540555919219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21014500430652720741225625 15760875322989540555919219)
    ·
      refine ⟨23641312984484310833878829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15760875322989540555919219 23641312984484310833878829)
      ·
        refine ⟨8865492369181616562704561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23641312984484310833878829 8865492369181616562704561)
        ·
          refine ⟨6649119276886212422028421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8865492369181616562704561 6649119276886212422028421)
          ·
            refine ⟨1246709864416164829130329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6649119276886212422028421 1246709864416164829130329)
            ·
              refine ⟨935032398312123621847747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246709864416164829130329 935032398312123621847747)
              ·
                refine ⟨1402548597468185432771621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935032398312123621847747 1402548597468185432771621)
                ·
                  refine ⟨262977862025284768644679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402548597468185432771621 262977862025284768644679)
                  ·
                    rfl

theorem cell21_1152332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_1152332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152332 prefixEnd_1152332 := by exact prefixLift 1152332
  have htrace : WordTrace (prefixWord ++ tailWord_1152332) baseStart_1152332 baseEnd_1152332 := by
    simpa [prefixWord, tailWord_1152332, baseEnd_1152332] using wordTrace_append hprefix tailTrace_1152332
  have hstable : (prefixWord ++ tailWord_1152332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152332).length < 2 ^ (prefixWord ++ tailWord_1152332).sum := by decide
  have hdescent : baseEnd_1152332 < baseStart_1152332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152377 : List Nat := [1, 2, 1, 3, 2, 1, 6, 2, 3]
def baseStart_1152377 : Nat := 118140960795 + 1152377 * 2 ^ 59
def prefixEnd_1152377 : Nat := 4983230072969 + 3 ^ 40 * 1152377 * 2
def baseEnd_1152377 : Nat := 262988131638374690394587

theorem tailTrace_1152377 : CollatzResearch.WordTrace tailWord_1152377 prefixEnd_1152377 262988131638374690394587 := by
  unfold tailWord_1152377
  simp only [CollatzResearch.WordTrace]
  refine ⟨42030642146142414167839385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28020428097428276111892923 42030642146142414167839385)
  ·
    refine ⟨31522981609606810625879539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42030642146142414167839385 31522981609606810625879539)
    ·
      refine ⟨47284472414410215938819309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31522981609606810625879539 47284472414410215938819309)
      ·
        refine ⟨17731677155403830977057241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47284472414410215938819309 17731677155403830977057241)
        ·
          refine ⟨13298757866552873232792931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17731677155403830977057241 13298757866552873232792931)
          ·
            refine ⟨19948136799829309849189397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13298757866552873232792931 19948136799829309849189397)
            ·
              refine ⟨935068912491998899180753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19948136799829309849189397 935068912491998899180753)
              ·
                refine ⟨701301684368999174385565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935068912491998899180753 701301684368999174385565)
                ·
                  refine ⟨262988131638374690394587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701301684368999174385565 262988131638374690394587)
                  ·
                    rfl

theorem cell21_1152377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 3].length) (baseStart_1152377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152377 prefixEnd_1152377 := by exact prefixLift 1152377
  have htrace : WordTrace (prefixWord ++ tailWord_1152377) baseStart_1152377 baseEnd_1152377 := by
    simpa [prefixWord, tailWord_1152377, baseEnd_1152377] using wordTrace_append hprefix tailTrace_1152377
  have hstable : (prefixWord ++ tailWord_1152377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152377).length < 2 ^ (prefixWord ++ tailWord_1152377).sum := by decide
  have hdescent : baseEnd_1152377 < baseStart_1152377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152470 : List Nat := [5, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1152470 : Nat := 118140960795 + 1152470 * 2 ^ 59
def prefixEnd_1152470 : Nat := 4983230072969 + 3 ^ 40 * 1152470 * 2
def baseEnd_1152470 : Nat := 263009355505427195344397

theorem tailTrace_1152470 : CollatzResearch.WordTrace tailWord_1152470 prefixEnd_1152470 263009355505427195344397 := by
  unfold tailWord_1152470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627127133425343190685929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28022689423203660700649909 2627127133425343190685929)
  ·
    refine ⟨1970345350069007393014447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2627127133425343190685929 1970345350069007393014447)
    ·
      refine ⟨2955518025103511089521671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1970345350069007393014447 2955518025103511089521671)
      ·
        refine ⟨4433277037655266634282507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2955518025103511089521671 4433277037655266634282507)
        ·
          refine ⟨6649915556482899951423761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4433277037655266634282507 6649915556482899951423761)
          ·
            refine ⟨4987436667362174963567821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6649915556482899951423761 4987436667362174963567821)
            ·
              refine ⟨1870288750260815611337933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4987436667362174963567821 1870288750260815611337933)
              ·
                refine ⟨701358281347805854251725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1870288750260815611337933 701358281347805854251725)
                ·
                  refine ⟨263009355505427195344397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701358281347805854251725 263009355505427195344397)
                  ·
                    rfl

theorem cell21_1152470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1152470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152470 prefixEnd_1152470 := by exact prefixLift 1152470
  have htrace : WordTrace (prefixWord ++ tailWord_1152470) baseStart_1152470 baseEnd_1152470 := by
    simpa [prefixWord, tailWord_1152470, baseEnd_1152470] using wordTrace_append hprefix tailTrace_1152470
  have hstable : (prefixWord ++ tailWord_1152470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152470).length < 2 ^ (prefixWord ++ tailWord_1152470).sum := by decide
  have hdescent : baseEnd_1152470 < baseStart_1152470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152495 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 5]
def baseStart_1152495 : Nat := 118140960795 + 1152495 * 2 ^ 59
def prefixEnd_1152495 : Nat := 4983230072969 + 3 ^ 40 * 1152495 * 2
def baseEnd_1152495 : Nat := 263015060846032707427679

theorem tailTrace_1152495 : CollatzResearch.WordTrace tailWord_1152495 prefixEnd_1152495 263015060846032707427679 := by
  unfold tailWord_1152495
  simp only [CollatzResearch.WordTrace]
  refine ⟨42034945959714920320634939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28023297306476613547089959 42034945959714920320634939)
  ·
    refine ⟨63052418939572380480952409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42034945959714920320634939 63052418939572380480952409)
    ·
      refine ⟨47289314204679285360714307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63052418939572380480952409 47289314204679285360714307)
      ·
        refine ⟨70933971307018928041071461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47289314204679285360714307 70933971307018928041071461)
        ·
          refine ⟨13300119620066049007700899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70933971307018928041071461 13300119620066049007700899)
          ·
            refine ⟨19950179430099073511551349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13300119620066049007700899 19950179430099073511551349)
            ·
              refine ⟨1870329321571788141707939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19950179430099073511551349 1870329321571788141707939)
              ·
                refine ⟨2805493982357682212561909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1870329321571788141707939 2805493982357682212561909)
                ·
                  refine ⟨263015060846032707427679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2805493982357682212561909 263015060846032707427679)
                  ·
                    rfl

theorem cell21_1152495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 5].length) (baseStart_1152495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152495 prefixEnd_1152495 := by exact prefixLift 1152495
  have htrace : WordTrace (prefixWord ++ tailWord_1152495) baseStart_1152495 baseEnd_1152495 := by
    simpa [prefixWord, tailWord_1152495, baseEnd_1152495] using wordTrace_append hprefix tailTrace_1152495
  have hstable : (prefixWord ++ tailWord_1152495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152495).length < 2 ^ (prefixWord ++ tailWord_1152495).sum := by decide
  have hdescent : baseEnd_1152495 < baseStart_1152495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152501 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 4]
def baseStart_1152501 : Nat := 118140960795 + 1152501 * 2 ^ 59
def prefixEnd_1152501 : Nat := 4983230072969 + 3 ^ 40 * 1152501 * 2
def baseEnd_1152501 : Nat := 263016430127778030327667

theorem tailTrace_1152501 : CollatzResearch.WordTrace tailWord_1152501 prefixEnd_1152501 263016430127778030327667 := by
  unfold tailWord_1152501
  simp only [CollatzResearch.WordTrace]
  refine ⟨42035164797693183345353357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28023443198462122230235571 42035164797693183345353357)
  ·
    refine ⟨15763186799134943754507509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42035164797693183345353357 15763186799134943754507509)
    ·
      refine ⟨1477798762418900976985079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15763186799134943754507509 1477798762418900976985079)
      ·
        refine ⟨2216698143628351465477619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477798762418900976985079 2216698143628351465477619)
        ·
          refine ⟨3325047215442527198216429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216698143628351465477619 3325047215442527198216429)
          ·
            refine ⟨1246892705790947699331161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3325047215442527198216429 1246892705790947699331161)
            ·
              refine ⟨935169529343210774498371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246892705790947699331161 935169529343210774498371)
              ·
                refine ⟨1402754294014816161747557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935169529343210774498371 1402754294014816161747557)
                ·
                  refine ⟨263016430127778030327667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402754294014816161747557 263016430127778030327667)
                  ·
                    rfl

theorem cell21_1152501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_1152501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152501 prefixEnd_1152501 := by exact prefixLift 1152501
  have htrace : WordTrace (prefixWord ++ tailWord_1152501) baseStart_1152501 baseEnd_1152501 := by
    simpa [prefixWord, tailWord_1152501, baseEnd_1152501] using wordTrace_append hprefix tailTrace_1152501
  have hstable : (prefixWord ++ tailWord_1152501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152501).length < 2 ^ (prefixWord ++ tailWord_1152501).sum := by decide
  have hdescent : baseEnd_1152501 < baseStart_1152501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152588 : List Nat := [2, 2, 1, 3, 1, 3, 1, 5, 3]
def baseStart_1152588 : Nat := 118140960795 + 1152588 * 2 ^ 59
def prefixEnd_1152588 : Nat := 4983230072969 + 3 ^ 40 * 1152588 * 2
def baseEnd_1152588 : Nat := 263036284713085212377489

theorem tailTrace_1152588 : CollatzResearch.WordTrace tailWord_1152588 prefixEnd_1152588 263036284713085212377489 := by
  unfold tailWord_1152588
  simp only [CollatzResearch.WordTrace]
  refine ⟨21019168974188998601885209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28025558632251998135846945 21019168974188998601885209)
  ·
    refine ⟨15764376730641748951413907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21019168974188998601885209 15764376730641748951413907)
    ·
      refine ⟨23646565095962623427120861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15764376730641748951413907 23646565095962623427120861)
      ·
        refine ⟨8867461910985983785170323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23646565095962623427120861 8867461910985983785170323)
        ·
          refine ⟨13301192866478975677755485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8867461910985983785170323 13301192866478975677755485)
          ·
            refine ⟨4987947324929615879158307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13301192866478975677755485 4987947324929615879158307)
            ·
              refine ⟨7481920987394423818737461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4987947324929615879158307 7481920987394423818737461)
              ·
                refine ⟨701430092568227233006637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7481920987394423818737461 701430092568227233006637)
                ·
                  refine ⟨263036284713085212377489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701430092568227233006637 263036284713085212377489)
                  ·
                    rfl

theorem cell21_1152588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_1152588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152588 prefixEnd_1152588 := by exact prefixLift 1152588
  have htrace : WordTrace (prefixWord ++ tailWord_1152588) baseStart_1152588 baseEnd_1152588 := by
    simpa [prefixWord, tailWord_1152588, baseEnd_1152588] using wordTrace_append hprefix tailTrace_1152588
  have hstable : (prefixWord ++ tailWord_1152588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152588).length < 2 ^ (prefixWord ++ tailWord_1152588).sum := by decide
  have hdescent : baseEnd_1152588 < baseStart_1152588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152664 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 5]
def baseStart_1152664 : Nat := 118140960795 + 1152664 * 2 ^ 59
def prefixEnd_1152664 : Nat := 4983230072969 + 3 ^ 40 * 1152664 * 2
def baseEnd_1152664 : Nat := 263053628948525969110667

theorem tailTrace_1152664 : CollatzResearch.WordTrace tailWord_1152664 prefixEnd_1152664 263053628948525969110667 := by
  unfold tailWord_1152664
  simp only [CollatzResearch.WordTrace]
  refine ⟨21020554948051331091768523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28027406597401774789024697 21020554948051331091768523)
  ·
    refine ⟨31530832422076996637652785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21020554948051331091768523 31530832422076996637652785)
    ·
      refine ⟨23648124316557747478239589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31530832422076996637652785 23648124316557747478239589)
      ·
        refine ⟨4434023309354577652169923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23648124316557747478239589 4434023309354577652169923)
        ·
          refine ⟨6651034964031866478254885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4434023309354577652169923 6651034964031866478254885)
          ·
            refine ⟨1247069055755974964672791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6651034964031866478254885 1247069055755974964672791)
            ·
              refine ⟨1870603583633962447009187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247069055755974964672791 1870603583633962447009187)
              ·
                refine ⟨2805905375450943670513781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1870603583633962447009187 2805905375450943670513781)
                ·
                  refine ⟨263053628948525969110667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2805905375450943670513781 263053628948525969110667)
                  ·
                    rfl

theorem cell21_1152664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_1152664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152664 prefixEnd_1152664 := by exact prefixLift 1152664
  have htrace : WordTrace (prefixWord ++ tailWord_1152664) baseStart_1152664 baseEnd_1152664 := by
    simpa [prefixWord, tailWord_1152664, baseEnd_1152664] using wordTrace_append hprefix tailTrace_1152664
  have hstable : (prefixWord ++ tailWord_1152664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152664).length < 2 ^ (prefixWord ++ tailWord_1152664).sum := by decide
  have hdescent : baseEnd_1152664 < baseStart_1152664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152830 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_1152830 : Nat := 118140960795 + 1152830 * 2 ^ 59
def prefixEnd_1152830 : Nat := 4983230072969 + 3 ^ 40 * 1152830 * 2
def baseEnd_1152830 : Nat := 263091512410146569343661

theorem tailTrace_1152830 : CollatzResearch.WordTrace tailWord_1152830 prefixEnd_1152830 263091512410146569343661 := by
  unfold tailWord_1152830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5255895551687659066759993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28031442942334181689386629 5255895551687659066759993)
  ·
    refine ⟨3941921663765744300069995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5255895551687659066759993 3941921663765744300069995)
    ·
      refine ⟨5912882495648616450104993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3941921663765744300069995 5912882495648616450104993)
      ·
        refine ⟨4434661871736462337578745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5912882495648616450104993 4434661871736462337578745)
        ·
          refine ⟨3325996403802346753184059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4434661871736462337578745 3325996403802346753184059)
          ·
            refine ⟨4988994605703520129776089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325996403802346753184059 4988994605703520129776089)
            ·
              refine ⟨3741745954277640097332067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4988994605703520129776089 3741745954277640097332067)
              ·
                refine ⟨5612618931416460145998101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741745954277640097332067 5612618931416460145998101)
                ·
                  refine ⟨263091512410146569343661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5612618931416460145998101 263091512410146569343661)
                  ·
                    rfl

theorem cell21_1152830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_1152830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152830 prefixEnd_1152830 := by exact prefixLift 1152830
  have htrace : WordTrace (prefixWord ++ tailWord_1152830) baseStart_1152830 baseEnd_1152830 := by
    simpa [prefixWord, tailWord_1152830, baseEnd_1152830] using wordTrace_append hprefix tailTrace_1152830
  have hstable : (prefixWord ++ tailWord_1152830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152830).length < 2 ^ (prefixWord ++ tailWord_1152830).sum := by decide
  have hdescent : baseEnd_1152830 < baseStart_1152830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152858 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_1152858 : Nat := 118140960795 + 1152858 * 2 ^ 59
def prefixEnd_1152858 : Nat := 4983230072969 + 3 ^ 40 * 1152858 * 2
def baseEnd_1152858 : Nat := 263097902391624742876937

theorem tailTrace_1152858 : CollatzResearch.WordTrace tailWord_1152858 prefixEnd_1152858 263097902391624742876937 := by
  unfold tailWord_1152858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10512046414349958329024807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28032123771599888877399485 10512046414349958329024807)
  ·
    refine ⟨15768069621524937493537211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10512046414349958329024807 15768069621524937493537211)
    ·
      refine ⟨23652104432287406240305817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15768069621524937493537211 23652104432287406240305817)
      ·
        refine ⟨17739078324215554680229363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23652104432287406240305817 17739078324215554680229363)
        ·
          refine ⟨26608617486323332020344045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17739078324215554680229363 26608617486323332020344045)
          ·
            refine ⟨9978231557371249507629017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26608617486323332020344045 9978231557371249507629017)
            ·
              refine ⟨7483673668028437130721763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9978231557371249507629017 7483673668028437130721763)
              ·
                refine ⟨11225510502042655696082645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7483673668028437130721763 11225510502042655696082645)
                ·
                  refine ⟨263097902391624742876937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11225510502042655696082645 263097902391624742876937)
                  ·
                    rfl

theorem cell21_1152858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_1152858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152858 prefixEnd_1152858 := by exact prefixLift 1152858
  have htrace : WordTrace (prefixWord ++ tailWord_1152858) baseStart_1152858 baseEnd_1152858 := by
    simpa [prefixWord, tailWord_1152858, baseEnd_1152858] using wordTrace_append hprefix tailTrace_1152858
  have hstable : (prefixWord ++ tailWord_1152858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152858).length < 2 ^ (prefixWord ++ tailWord_1152858).sum := by decide
  have hdescent : baseEnd_1152858 < baseStart_1152858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152875 : List Nat := [1, 1, 1, 1, 2, 2, 3, 7, 3]
def baseStart_1152875 : Nat := 118140960795 + 1152875 * 2 ^ 59
def prefixEnd_1152875 : Nat := 4983230072969 + 3 ^ 40 * 1152875 * 2
def baseEnd_1152875 : Nat := 263101782023236491093569

theorem tailTrace_1152875 : CollatzResearch.WordTrace tailWord_1152875 prefixEnd_1152875 263101782023236491093569 := by
  unfold tailWord_1152875
  simp only [CollatzResearch.WordTrace]
  refine ⟨42048805698338245219468079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28032537132225496812978719 42048805698338245219468079)
  ·
    refine ⟨63073208547507367829202119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42048805698338245219468079 63073208547507367829202119)
    ·
      refine ⟨94609812821261051743803179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63073208547507367829202119 94609812821261051743803179)
      ·
        refine ⟨141914719231891577615704769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94609812821261051743803179 141914719231891577615704769)
        ·
          refine ⟨106436039423918683211778577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141914719231891577615704769 106436039423918683211778577)
          ·
            refine ⟨79827029567939012408833933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106436039423918683211778577 79827029567939012408833933)
            ·
              refine ⟨29935136087977129653312725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79827029567939012408833933 29935136087977129653312725)
              ·
                refine ⟨701604752061963976249517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29935136087977129653312725 701604752061963976249517)
                ·
                  refine ⟨263101782023236491093569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701604752061963976249517 263101782023236491093569)
                  ·
                    rfl

theorem cell21_1152875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 3].length) (baseStart_1152875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152875 prefixEnd_1152875 := by exact prefixLift 1152875
  have htrace : WordTrace (prefixWord ++ tailWord_1152875) baseStart_1152875 baseEnd_1152875 := by
    simpa [prefixWord, tailWord_1152875, baseEnd_1152875] using wordTrace_append hprefix tailTrace_1152875
  have hstable : (prefixWord ++ tailWord_1152875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152875).length < 2 ^ (prefixWord ++ tailWord_1152875).sum := by decide
  have hdescent : baseEnd_1152875 < baseStart_1152875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152985 : List Nat := [1, 2, 1, 2, 6, 2, 1, 3, 3]
def baseStart_1152985 : Nat := 118140960795 + 1152985 * 2 ^ 59
def prefixEnd_1152985 : Nat := 4983230072969 + 3 ^ 40 * 1152985 * 2
def baseEnd_1152985 : Nat := 263126885521900744260011

theorem tailTrace_1152985 : CollatzResearch.WordTrace tailWord_1152985 prefixEnd_1152985 263126885521900744260011 := by
  unfold tailWord_1152985
  simp only [CollatzResearch.WordTrace]
  refine ⟨42052817727939734005972409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28035211818626489337314939 42052817727939734005972409)
  ·
    refine ⟨31539613295954800504479307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42052817727939734005972409 31539613295954800504479307)
    ·
      refine ⟨47309419943932200756718961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31539613295954800504479307 47309419943932200756718961)
      ·
        refine ⟨35482064957949150567539221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47309419943932200756718961 35482064957949150567539221)
        ·
          refine ⟨1663221794903866432853401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35482064957949150567539221 1663221794903866432853401)
          ·
            refine ⟨1247416346177899824640051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663221794903866432853401 1247416346177899824640051)
            ·
              refine ⟨1871124519266849736960077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247416346177899824640051 1871124519266849736960077)
              ·
                refine ⟨701671694725068651360029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1871124519266849736960077 701671694725068651360029)
                ·
                  refine ⟨263126885521900744260011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701671694725068651360029 263126885521900744260011)
                  ·
                    rfl

theorem cell21_1152985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 3].length) (baseStart_1152985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1152985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1152985 prefixEnd_1152985 := by exact prefixLift 1152985
  have htrace : WordTrace (prefixWord ++ tailWord_1152985) baseStart_1152985 baseEnd_1152985 := by
    simpa [prefixWord, tailWord_1152985, baseEnd_1152985] using wordTrace_append hprefix tailTrace_1152985
  have hstable : (prefixWord ++ tailWord_1152985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152985).length < 2 ^ (prefixWord ++ tailWord_1152985).sum := by decide
  have hdescent : baseEnd_1152985 < baseStart_1152985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153024 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_1153024 : Nat := 118140960795 + 1153024 * 2 ^ 59
def prefixEnd_1153024 : Nat := 4983230072969 + 3 ^ 40 * 1153024 * 2
def baseEnd_1153024 : Nat := 263135785853245343109931

theorem tailTrace_1153024 : CollatzResearch.WordTrace tailWord_1153024 prefixEnd_1153024 263135785853245343109931 := by
  unfold tailWord_1153024
  simp only [CollatzResearch.WordTrace]
  refine ⟨21027120087399221833321063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28036160116532295777761417 21027120087399221833321063)
  ·
    refine ⟨31540680131098832749981595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21027120087399221833321063 31540680131098832749981595)
    ·
      refine ⟨47311020196648249124972393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31540680131098832749981595 47311020196648249124972393)
      ·
        refine ⟨35483265147486186843729295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47311020196648249124972393 35483265147486186843729295)
        ·
          refine ⟨53224897721229280265593943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35483265147486186843729295 53224897721229280265593943)
          ·
            refine ⟨79837346581843920398390915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53224897721229280265593943 79837346581843920398390915)
            ·
              refine ⟨119756019872765880597586373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79837346581843920398390915 119756019872765880597586373)
              ·
                refine ⟨22454253726143602612047445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119756019872765880597586373 22454253726143602612047445)
                ·
                  refine ⟨263135785853245343109931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22454253726143602612047445 263135785853245343109931)
                  ·
                    rfl

theorem cell21_1153024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_1153024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153024 prefixEnd_1153024 := by exact prefixLift 1153024
  have htrace : WordTrace (prefixWord ++ tailWord_1153024) baseStart_1153024 baseEnd_1153024 := by
    simpa [prefixWord, tailWord_1153024, baseEnd_1153024] using wordTrace_append hprefix tailTrace_1153024
  have hstable : (prefixWord ++ tailWord_1153024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153024).length < 2 ^ (prefixWord ++ tailWord_1153024).sum := by decide
  have hdescent : baseEnd_1153024 < baseStart_1153024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153058 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1153058 : Nat := 118140960795 + 1153058 * 2 ^ 59
def prefixEnd_1153058 : Nat := 4983230072969 + 3 ^ 40 * 1153058 * 2
def baseEnd_1153058 : Nat := 263143545116468839543195

theorem tailTrace_1153058 : CollatzResearch.WordTrace tailWord_1153058 prefixEnd_1153058 263143545116468839543195 := by
  unfold tailWord_1153058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10513870064168816868344957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28036986837783511648919885 10513870064168816868344957)
  ·
    refine ⟨3942701274063306325629359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10513870064168816868344957 3942701274063306325629359)
    ·
      refine ⟨5914051911094959488444039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3942701274063306325629359 5914051911094959488444039)
      ·
        refine ⟨8871077866642439232666059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5914051911094959488444039 8871077866642439232666059)
        ·
          refine ⟨13306616799963658848999089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8871077866642439232666059 13306616799963658848999089)
          ·
            refine ⟨9979962599972744136749317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13306616799963658848999089 9979962599972744136749317)
            ·
              refine ⟨1871242987494889525640497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9979962599972744136749317 1871242987494889525640497)
              ·
                refine ⟨1403432240621167144230373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871242987494889525640497 1403432240621167144230373)
                ·
                  refine ⟨263143545116468839543195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1403432240621167144230373 263143545116468839543195)
                  ·
                    rfl

theorem cell21_1153058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1153058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153058 prefixEnd_1153058 := by exact prefixLift 1153058
  have htrace : WordTrace (prefixWord ++ tailWord_1153058) baseStart_1153058 baseEnd_1153058 := by
    simpa [prefixWord, tailWord_1153058, baseEnd_1153058] using wordTrace_append hprefix tailTrace_1153058
  have hstable : (prefixWord ++ tailWord_1153058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153058).length < 2 ^ (prefixWord ++ tailWord_1153058).sum := by decide
  have hdescent : baseEnd_1153058 < baseStart_1153058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153061 : List Nat := [1, 3, 1, 2, 2, 5, 2, 2, 3]
def baseStart_1153061 : Nat := 118140960795 + 1153061 * 2 ^ 59
def prefixEnd_1153061 : Nat := 4983230072969 + 3 ^ 40 * 1153061 * 2
def baseEnd_1153061 : Nat := 263144229757341500993189

theorem tailTrace_1153061 : CollatzResearch.WordTrace tailWord_1153061 prefixEnd_1153061 263144229757341500993189 := by
  unfold tailWord_1153061
  simp only [CollatzResearch.WordTrace]
  refine ⟨42055589675664398985739037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28037059783776265990492691 42055589675664398985739037)
  ·
    refine ⟨15770846128374149619652139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42055589675664398985739037 15770846128374149619652139)
    ·
      refine ⟨23656269192561224429478209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15770846128374149619652139 23656269192561224429478209)
      ·
        refine ⟨17742201894420918322108657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23656269192561224429478209 17742201894420918322108657)
        ·
          refine ⟨13306651420815688741581493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17742201894420918322108657 13306651420815688741581493)
          ·
            refine ⟨1247498570701470819523265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13306651420815688741581493 1247498570701470819523265)
            ·
              refine ⟨935623928026103114642449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247498570701470819523265 935623928026103114642449)
              ·
                refine ⟨701717946019577335981837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935623928026103114642449 701717946019577335981837)
                ·
                  refine ⟨263144229757341500993189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701717946019577335981837 263144229757341500993189)
                  ·
                    rfl

theorem cell21_1153061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_1153061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153061 prefixEnd_1153061 := by exact prefixLift 1153061
  have htrace : WordTrace (prefixWord ++ tailWord_1153061) baseStart_1153061 baseEnd_1153061 := by
    simpa [prefixWord, tailWord_1153061, baseEnd_1153061] using wordTrace_append hprefix tailTrace_1153061
  have hstable : (prefixWord ++ tailWord_1153061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153061).length < 2 ^ (prefixWord ++ tailWord_1153061).sum := by decide
  have hdescent : baseEnd_1153061 < baseStart_1153061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153072 : List Nat := [2, 1, 1, 1, 2, 7, 1, 6]
def baseStart_1153072 : Nat := 118140960795 + 1153072 * 2 ^ 59
def prefixEnd_1153072 : Nat := 4983230072969 + 3 ^ 40 * 1153072 * 2
def baseEnd_1153072 : Nat := 87715580035735975436611

theorem tailTrace_1153072 : CollatzResearch.WordTrace tailWord_1153072 prefixEnd_1153072 87715580035735975436611 := by
  unfold tailWord_1153072
  simp only [CollatzResearch.WordTrace]
  refine ⟨21027995439312273932194735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28037327252416365242926313 21027995439312273932194735)
  ·
    refine ⟨31541993158968410898292103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21027995439312273932194735 31541993158968410898292103)
    ·
      refine ⟨47312989738452616347438155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31541993158968410898292103 47312989738452616347438155)
      ·
        refine ⟨70969484607678924521157233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47312989738452616347438155 70969484607678924521157233)
        ·
          refine ⟨53227113455759193390867925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70969484607678924521157233 53227113455759193390867925)
          ·
            refine ⟨1247510471619356095098467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53227113455759193390867925 1247510471619356095098467)
            ·
              refine ⟨1871265707429034142647701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247510471619356095098467 1871265707429034142647701)
              ·
                refine ⟨87715580035735975436611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1871265707429034142647701 87715580035735975436611)
                ·
                  rfl

theorem cell21_1153072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_1153072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153072 prefixEnd_1153072 := by exact prefixLift 1153072
  have htrace : WordTrace (prefixWord ++ tailWord_1153072) baseStart_1153072 baseEnd_1153072 := by
    simpa [prefixWord, tailWord_1153072, baseEnd_1153072] using wordTrace_append hprefix tailTrace_1153072
  have hstable : (prefixWord ++ tailWord_1153072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153072).length < 2 ^ (prefixWord ++ tailWord_1153072).sum := by decide
  have hdescent : baseEnd_1153072 < baseStart_1153072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153089 : List Nat := [1, 2, 5, 1, 2, 2, 3, 5]
def baseStart_1153089 : Nat := 118140960795 + 1153089 * 2 ^ 59
def prefixEnd_1153089 : Nat := 4983230072969 + 3 ^ 40 * 1153089 * 2
def baseEnd_1153089 : Nat := 87716873246273224842155

theorem tailTrace_1153089 : CollatzResearch.WordTrace tailWord_1153089 prefixEnd_1153089 87716873246273224842155 := by
  unfold tailWord_1153089
  simp only [CollatzResearch.WordTrace]
  refine ⟨42056610919562959767758321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28037740613041973178505547 42056610919562959767758321)
  ·
    refine ⟨31542458189672219825818741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42056610919562959767758321 31542458189672219825818741)
    ·
      refine ⟨2957105455281770608670507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31542458189672219825818741 2957105455281770608670507)
      ·
        refine ⟨4435658182922655913005761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957105455281770608670507 4435658182922655913005761)
        ·
          refine ⟨3326743637191991934754321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4435658182922655913005761 3326743637191991934754321)
          ·
            refine ⟨2495057727893993951065741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3326743637191991934754321 2495057727893993951065741)
            ·
              refine ⟨935646647960247731649653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2495057727893993951065741 935646647960247731649653)
              ·
                refine ⟨87716873246273224842155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 935646647960247731649653 87716873246273224842155)
                ·
                  rfl

theorem cell21_1153089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 5].length) (baseStart_1153089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153089 prefixEnd_1153089 := by exact prefixLift 1153089
  have htrace : WordTrace (prefixWord ++ tailWord_1153089) baseStart_1153089 baseEnd_1153089 := by
    simpa [prefixWord, tailWord_1153089, baseEnd_1153089] using wordTrace_append hprefix tailTrace_1153089
  have hstable : (prefixWord ++ tailWord_1153089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153089).length < 2 ^ (prefixWord ++ tailWord_1153089).sum := by decide
  have hdescent : baseEnd_1153089 < baseStart_1153089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153148 : List Nat := [2, 2, 2, 1, 1, 4, 4, 5]
def baseStart_1153148 : Nat := 118140960795 + 1153148 * 2 ^ 59
def prefixEnd_1153148 : Nat := 4983230072969 + 3 ^ 40 * 1153148 * 2
def baseEnd_1153148 : Nat := 87721361447549561014337

theorem tailTrace_1153148 : CollatzResearch.WordTrace tailWord_1153148 prefixEnd_1153148 87721361447549561014337 := by
  unfold tailWord_1153148
  simp only [CollatzResearch.WordTrace]
  refine ⟨21029381413174606422078049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28039175217566141896104065 21029381413174606422078049)
  ·
    refine ⟨15772036059880954816558537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21029381413174606422078049 15772036059880954816558537)
    ·
      refine ⟨11829027044910716112418903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15772036059880954816558537 11829027044910716112418903)
      ·
        refine ⟨17743540567366074168628355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11829027044910716112418903 17743540567366074168628355)
        ·
          refine ⟨26615310851049111252942533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17743540567366074168628355 26615310851049111252942533)
          ·
            refine ⟨4990370784571708359926725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26615310851049111252942533 4990370784571708359926725)
            ·
              refine ⟨935694522107195317486261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4990370784571708359926725 935694522107195317486261)
              ·
                refine ⟨87721361447549561014337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 935694522107195317486261 87721361447549561014337)
                ·
                  rfl

theorem cell21_1153148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_1153148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153148 prefixEnd_1153148 := by exact prefixLift 1153148
  have htrace : WordTrace (prefixWord ++ tailWord_1153148) baseStart_1153148 baseEnd_1153148 := by
    simpa [prefixWord, tailWord_1153148, baseEnd_1153148] using wordTrace_append hprefix tailTrace_1153148
  have hstable : (prefixWord ++ tailWord_1153148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153148).length < 2 ^ (prefixWord ++ tailWord_1153148).sum := by decide
  have hdescent : baseEnd_1153148 < baseStart_1153148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153207 : List Nat := [1, 1, 3, 1, 4, 2, 2, 7]
def baseStart_1153207 : Nat := 118140960795 + 1153207 * 2 ^ 59
def prefixEnd_1153207 : Nat := 4983230072969 + 3 ^ 40 * 1153207 * 2
def baseEnd_1153207 : Nat := 87725849648825897186519

theorem tailTrace_1153207 : CollatzResearch.WordTrace tailWord_1153207 prefixEnd_1153207 87725849648825897186519 := by
  unfold tailWord_1153207
  simp only [CollatzResearch.WordTrace]
  refine ⟨42060914733135465920553875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28040609822090310613702583 42060914733135465920553875)
  ·
    refine ⟨63091372099703198880830813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42060914733135465920553875 63091372099703198880830813)
    ·
      refine ⟨23659264537388699580311555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63091372099703198880830813 23659264537388699580311555)
      ·
        refine ⟨35488896806083049370467333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23659264537388699580311555 35488896806083049370467333)
        ·
          refine ⟨6654168151140571756962625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35488896806083049370467333 6654168151140571756962625)
          ·
            refine ⟨4990626113355428817721969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6654168151140571756962625 4990626113355428817721969)
            ·
              refine ⟨3742969585016571613291477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4990626113355428817721969 3742969585016571613291477)
              ·
                refine ⟨87725849648825897186519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3742969585016571613291477 87725849648825897186519)
                ·
                  rfl

theorem cell21_1153207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 7].length) (baseStart_1153207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153207 prefixEnd_1153207 := by exact prefixLift 1153207
  have htrace : WordTrace (prefixWord ++ tailWord_1153207) baseStart_1153207 baseEnd_1153207 := by
    simpa [prefixWord, tailWord_1153207, baseEnd_1153207] using wordTrace_append hprefix tailTrace_1153207
  have hstable : (prefixWord ++ tailWord_1153207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153207).length < 2 ^ (prefixWord ++ tailWord_1153207).sum := by decide
  have hdescent : baseEnd_1153207 < baseStart_1153207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153252 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_1153252 : Nat := 118140960795 + 1153252 * 2 ^ 59
def prefixEnd_1153252 : Nat := 4983230072969 + 3 ^ 40 * 1153252 * 2
def baseEnd_1153252 : Nat := 263187818559567613309465

theorem tailTrace_1153252 : CollatzResearch.WordTrace tailWord_1153252 prefixEnd_1153252 263187818559567613309465 := by
  unfold tailWord_1153252
  simp only [CollatzResearch.WordTrace]
  refine ⟨21031278008986219302971005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28041704011981625737294673 21031278008986219302971005)
  ·
    refine ⟨7886729253369832238614127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21031278008986219302971005 7886729253369832238614127)
    ·
      refine ⟨11830093880054748357921191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7886729253369832238614127 11830093880054748357921191)
      ·
        refine ⟨17745140820082122536881787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11830093880054748357921191 17745140820082122536881787)
        ·
          refine ⟨26617711230123183805322681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17745140820082122536881787 26617711230123183805322681)
          ·
            refine ⟨19963283422592387853992011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26617711230123183805322681 19963283422592387853992011)
            ·
              refine ⟨29944925133888581780988017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19963283422592387853992011 29944925133888581780988017)
              ·
                refine ⟨22458693850416436335741013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29944925133888581780988017 22458693850416436335741013)
                ·
                  refine ⟨263187818559567613309465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22458693850416436335741013 263187818559567613309465)
                  ·
                    rfl

theorem cell21_1153252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_1153252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153252 prefixEnd_1153252 := by exact prefixLift 1153252
  have htrace : WordTrace (prefixWord ++ tailWord_1153252) baseStart_1153252 baseEnd_1153252 := by
    simpa [prefixWord, tailWord_1153252, baseEnd_1153252] using wordTrace_append hprefix tailTrace_1153252
  have hstable : (prefixWord ++ tailWord_1153252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153252).length < 2 ^ (prefixWord ++ tailWord_1153252).sum := by decide
  have hdescent : baseEnd_1153252 < baseStart_1153252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153255 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 5]
def baseStart_1153255 : Nat := 118140960795 + 1153255 * 2 ^ 59
def prefixEnd_1153255 : Nat := 4983230072969 + 3 ^ 40 * 1153255 * 2
def baseEnd_1153255 : Nat := 263188503200440274759459

theorem tailTrace_1153255 : CollatzResearch.WordTrace tailWord_1153255 prefixEnd_1153255 263188503200440274759459 := by
  unfold tailWord_1153255
  simp only [CollatzResearch.WordTrace]
  refine ⟨42062665436961570118301219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28041776957974380078867479 42062665436961570118301219)
  ·
    refine ⟨63093998155442355177451829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42062665436961570118301219 63093998155442355177451829)
    ·
      refine ⟨5915062327072720797886109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63093998155442355177451829 5915062327072720797886109)
      ·
        refine ⟨2218148372652270299207291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5915062327072720797886109 2218148372652270299207291)
        ·
          refine ⟨3327222558978405448810937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2218148372652270299207291 3327222558978405448810937)
          ·
            refine ⟨2495416919233804086608203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3327222558978405448810937 2495416919233804086608203)
            ·
              refine ⟨3743125378850706129912305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495416919233804086608203 3743125378850706129912305)
              ·
                refine ⟨2807344034138029597434229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3743125378850706129912305 2807344034138029597434229)
                ·
                  refine ⟨263188503200440274759459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2807344034138029597434229 263188503200440274759459)
                  ·
                    rfl

theorem cell21_1153255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 5].length) (baseStart_1153255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153255 prefixEnd_1153255 := by exact prefixLift 1153255
  have htrace : WordTrace (prefixWord ++ tailWord_1153255) baseStart_1153255 baseEnd_1153255 := by
    simpa [prefixWord, tailWord_1153255, baseEnd_1153255] using wordTrace_append hprefix tailTrace_1153255
  have hstable : (prefixWord ++ tailWord_1153255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153255).length < 2 ^ (prefixWord ++ tailWord_1153255).sum := by decide
  have hdescent : baseEnd_1153255 < baseStart_1153255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153317 : List Nat := [1, 3, 1, 2, 5, 2, 2, 5]
def baseStart_1153317 : Nat := 118140960795 + 1153317 * 2 ^ 59
def prefixEnd_1153317 : Nat := 4983230072969 + 3 ^ 40 * 1153317 * 2
def baseEnd_1153317 : Nat := 87734217481713981575333

theorem tailTrace_1153317 : CollatzResearch.WordTrace tailWord_1153317 prefixEnd_1153317 87734217481713981575333 := by
  unfold tailWord_1153317
  simp only [CollatzResearch.WordTrace]
  refine ⟨42064926762736954707058205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28043284508491303138038803 42064926762736954707058205)
  ·
    refine ⟨15774347536026358015146827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42064926762736954707058205 15774347536026358015146827)
    ·
      refine ⟨23661521304039537022720241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15774347536026358015146827 23661521304039537022720241)
      ·
        refine ⟨17746140978029652767040181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23661521304039537022720241 17746140978029652767040181)
        ·
          refine ⟨1663700716690279946910017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17746140978029652767040181 1663700716690279946910017)
          ·
            refine ⟨1247775537517709960182513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663700716690279946910017 1247775537517709960182513)
            ·
              refine ⟨935831653138282470136885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247775537517709960182513 935831653138282470136885)
              ·
                refine ⟨87734217481713981575333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 935831653138282470136885 87734217481713981575333)
                ·
                  rfl

theorem cell21_1153317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 5].length) (baseStart_1153317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153317 prefixEnd_1153317 := by exact prefixLift 1153317
  have htrace : WordTrace (prefixWord ++ tailWord_1153317) baseStart_1153317 baseEnd_1153317 := by
    simpa [prefixWord, tailWord_1153317, baseEnd_1153317] using wordTrace_append hprefix tailTrace_1153317
  have hstable : (prefixWord ++ tailWord_1153317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153317).length < 2 ^ (prefixWord ++ tailWord_1153317).sum := by decide
  have hdescent : baseEnd_1153317 < baseStart_1153317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153362 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_1153362 : Nat := 118140960795 + 1153362 * 2 ^ 59
def prefixEnd_1153362 : Nat := 4983230072969 + 3 ^ 40 * 1153362 * 2
def baseEnd_1153362 : Nat := 263212922058231866475907

theorem tailTrace_1153362 : CollatzResearch.WordTrace tailWord_1153362 prefixEnd_1153362 263212922058231866475907 := by
  unfold tailWord_1153362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10516642011893481848111585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28044378698382618261630893 10516642011893481848111585)
  ·
    refine ⟨7887481508920111386083689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10516642011893481848111585 7887481508920111386083689)
    ·
      refine ⟨5915611131690083539562767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7887481508920111386083689 5915611131690083539562767)
      ·
        refine ⟨8873416697535125309344151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5915611131690083539562767 8873416697535125309344151)
        ·
          refine ⟨13310125046302687964016227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8873416697535125309344151 13310125046302687964016227)
          ·
            refine ⟨19965187569454031946024341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13310125046302687964016227 19965187569454031946024341)
            ·
              refine ⟨935868167318157747469891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19965187569454031946024341 935868167318157747469891)
              ·
                refine ⟨1403802250977236621204837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935868167318157747469891 1403802250977236621204837)
                ·
                  refine ⟨263212922058231866475907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1403802250977236621204837 263212922058231866475907)
                  ·
                    rfl

theorem cell21_1153362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_1153362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153362 prefixEnd_1153362 := by exact prefixLift 1153362
  have htrace : WordTrace (prefixWord ++ tailWord_1153362) baseStart_1153362 baseEnd_1153362 := by
    simpa [prefixWord, tailWord_1153362, baseEnd_1153362] using wordTrace_append hprefix tailTrace_1153362
  have hstable : (prefixWord ++ tailWord_1153362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153362).length < 2 ^ (prefixWord ++ tailWord_1153362).sum := by decide
  have hdescent : baseEnd_1153362 < baseStart_1153362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153410 : List Nat := [3, 4, 2, 1, 2, 2, 1, 6]
def baseStart_1153410 : Nat := 118140960795 + 1153410 * 2 ^ 59
def prefixEnd_1153410 : Nat := 4983230072969 + 3 ^ 40 * 1153410 * 2
def baseEnd_1153410 : Nat := 87741292104064816558603

theorem tailTrace_1153410 : CollatzResearch.WordTrace tailWord_1153410 prefixEnd_1153410 87741292104064816558603 := by
  unfold tailWord_1153410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517079687850007897548421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28045545834266687726795789 10517079687850007897548421)
  ·
    refine ⟨1971952441471876480790329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10517079687850007897548421 1971952441471876480790329)
    ·
      refine ⟨1478964331103907360592747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1971952441471876480790329 1478964331103907360592747)
      ·
        refine ⟨2218446496655861040889121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1478964331103907360592747 2218446496655861040889121)
        ·
          refine ⟨1663834872491895780666841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2218446496655861040889121 1663834872491895780666841)
          ·
            refine ⟨1247876154368921835500131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663834872491895780666841 1247876154368921835500131)
            ·
              refine ⟨1871814231553382753250197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247876154368921835500131 1871814231553382753250197)
              ·
                refine ⟨87741292104064816558603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1871814231553382753250197 87741292104064816558603)
                ·
                  rfl

theorem cell21_1153410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_1153410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153410 prefixEnd_1153410 := by exact prefixLift 1153410
  have htrace : WordTrace (prefixWord ++ tailWord_1153410) baseStart_1153410 baseEnd_1153410 := by
    simpa [prefixWord, tailWord_1153410, baseEnd_1153410] using wordTrace_append hprefix tailTrace_1153410
  have hstable : (prefixWord ++ tailWord_1153410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153410).length < 2 ^ (prefixWord ++ tailWord_1153410).sum := by decide
  have hdescent : baseEnd_1153410 < baseStart_1153410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153441 : List Nat := [1, 2, 3, 5, 1, 1, 2, 3, 3]
def baseStart_1153441 : Nat := 118140960795 + 1153441 * 2 ^ 59
def prefixEnd_1153441 : Nat := 4983230072969 + 3 ^ 40 * 1153441 * 2
def baseEnd_1153441 : Nat := 263230950934545284659079

theorem tailTrace_1153441 : CollatzResearch.WordTrace tailWord_1153441 prefixEnd_1153441 263230950934545284659079 := by
  unfold tailWord_1153441
  simp only [CollatzResearch.WordTrace]
  refine ⟨42069449414287723884572177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28046299609525149256381451 42069449414287723884572177)
  ·
    refine ⟨31552087060715792913429133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42069449414287723884572177 31552087060715792913429133)
    ·
      refine ⟨11832032647768422342535925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31552087060715792913429133 11832032647768422342535925)
      ·
        refine ⟨1109253060728289594612743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11832032647768422342535925 1109253060728289594612743)
        ·
          refine ⟨1663879591092434391919115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109253060728289594612743 1663879591092434391919115)
          ·
            refine ⟨2495819386638651587878673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663879591092434391919115 2495819386638651587878673)
            ·
              refine ⟨1871864539978988690909005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2495819386638651587878673 1871864539978988690909005)
              ·
                refine ⟨701949202492120759090877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1871864539978988690909005 701949202492120759090877)
                ·
                  refine ⟨263230950934545284659079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701949202492120759090877 263230950934545284659079)
                  ·
                    rfl

theorem cell21_1153441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 3].length) (baseStart_1153441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153441 prefixEnd_1153441 := by exact prefixLift 1153441
  have htrace : WordTrace (prefixWord ++ tailWord_1153441) baseStart_1153441 baseEnd_1153441 := by
    simpa [prefixWord, tailWord_1153441, baseEnd_1153441] using wordTrace_append hprefix tailTrace_1153441
  have hstable : (prefixWord ++ tailWord_1153441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153441).length < 2 ^ (prefixWord ++ tailWord_1153441).sum := by decide
  have hdescent : baseEnd_1153441 < baseStart_1153441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153517 : List Nat := [1, 5, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1153517 : Nat := 118140960795 + 1153517 * 2 ^ 59
def prefixEnd_1153517 : Nat := 4983230072969 + 3 ^ 40 * 1153517 * 2
def baseEnd_1153517 : Nat := 263248295169986041392257

theorem tailTrace_1153517 : CollatzResearch.WordTrace tailWord_1153517 prefixEnd_1153517 263248295169986041392257 := by
  unfold tailWord_1153517
  simp only [CollatzResearch.WordTrace]
  refine ⟨42072221362012388864338805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28048147574674925909559203 42072221362012388864338805)
  ·
    refine ⟨3944270752688661456031763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42072221362012388864338805 3944270752688661456031763)
    ·
      refine ⟨5916406129032992184047645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3944270752688661456031763 5916406129032992184047645)
      ·
        refine ⟨2218652298387372069017867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5916406129032992184047645 2218652298387372069017867)
        ·
          refine ⟨3327978447581058103526801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2218652298387372069017867 3327978447581058103526801)
          ·
            refine ⟨2495983835685793577645101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3327978447581058103526801 2495983835685793577645101)
            ·
              refine ⟨935993938382172591616913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2495983835685793577645101 935993938382172591616913)
              ·
                refine ⟨701995453786629443712685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935993938382172591616913 701995453786629443712685)
                ·
                  refine ⟨263248295169986041392257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701995453786629443712685 263248295169986041392257)
                  ·
                    rfl

theorem cell21_1153517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1153517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153517 prefixEnd_1153517 := by exact prefixLift 1153517
  have htrace : WordTrace (prefixWord ++ tailWord_1153517) baseStart_1153517 baseEnd_1153517 := by
    simpa [prefixWord, tailWord_1153517, baseEnd_1153517] using wordTrace_append hprefix tailTrace_1153517
  have hstable : (prefixWord ++ tailWord_1153517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153517).length < 2 ^ (prefixWord ++ tailWord_1153517).sum := by decide
  have hdescent : baseEnd_1153517 < baseStart_1153517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153576 : List Nat := [2, 1, 5, 2, 1, 2, 1, 4, 3]
def baseStart_1153576 : Nat := 118140960795 + 1153576 * 2 ^ 59
def prefixEnd_1153576 : Nat := 4983230072969 + 3 ^ 40 * 1153576 * 2
def baseEnd_1153576 : Nat := 263261759773815049908803

theorem tailTrace_1153576 : CollatzResearch.WordTrace tailWord_1153576 prefixEnd_1153576 263261759773815049908803 := by
  unfold tailWord_1153576
  simp only [CollatzResearch.WordTrace]
  refine ⟨21037186634399320970368291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28049582179199094627157721 21037186634399320970368291)
  ·
    refine ⟨31555779951598981455552437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21037186634399320970368291 31555779951598981455552437)
    ·
      refine ⟨2958354370462404511458041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31555779951598981455552437 2958354370462404511458041)
      ·
        refine ⟨2218765777846803383593531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2958354370462404511458041 2218765777846803383593531)
        ·
          refine ⟨3328148666770205075390297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2218765777846803383593531 3328148666770205075390297)
          ·
            refine ⟨2496111500077653806542723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3328148666770205075390297 2496111500077653806542723)
            ·
              refine ⟨3744167250116480709814085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496111500077653806542723 3744167250116480709814085)
              ·
                refine ⟨702031359396840133090141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3744167250116480709814085 702031359396840133090141)
                ·
                  refine ⟨263261759773815049908803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702031359396840133090141 263261759773815049908803)
                  ·
                    rfl

theorem cell21_1153576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 3].length) (baseStart_1153576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153576 prefixEnd_1153576 := by exact prefixLift 1153576
  have htrace : WordTrace (prefixWord ++ tailWord_1153576) baseStart_1153576 baseEnd_1153576 := by
    simpa [prefixWord, tailWord_1153576, baseEnd_1153576] using wordTrace_append hprefix tailTrace_1153576
  have hstable : (prefixWord ++ tailWord_1153576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153576).length < 2 ^ (prefixWord ++ tailWord_1153576).sum := by decide
  have hdescent : baseEnd_1153576 < baseStart_1153576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153590 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1153590 : Nat := 118140960795 + 1153590 * 2 ^ 59
def prefixEnd_1153590 : Nat := 4983230072969 + 3 ^ 40 * 1153590 * 2
def baseEnd_1153590 : Nat := 263264954764554136675441

theorem tailTrace_1153590 : CollatzResearch.WordTrace tailWord_1153590 prefixEnd_1153590 263264954764554136675441 := by
  unfold tailWord_1153590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629680243171745145734139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28049922593831948221164149 2629680243171745145734139)
  ·
    refine ⟨3944520364757617718601209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2629680243171745145734139 3944520364757617718601209)
    ·
      refine ⟨2958390273568213288950907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3944520364757617718601209 2958390273568213288950907)
      ·
        refine ⟨4437585410352319933426361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2958390273568213288950907 4437585410352319933426361)
        ·
          refine ⟨3328189057764239950069771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4437585410352319933426361 3328189057764239950069771)
          ·
            refine ⟨4992283586646359925104657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3328189057764239950069771 4992283586646359925104657)
            ·
              refine ⟨3744212689984769943828493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4992283586646359925104657 3744212689984769943828493)
              ·
                refine ⟨1404079758744288728935685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3744212689984769943828493 1404079758744288728935685)
                ·
                  refine ⟨263264954764554136675441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1404079758744288728935685 263264954764554136675441)
                  ·
                    rfl

theorem cell21_1153590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1153590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153590 prefixEnd_1153590 := by exact prefixLift 1153590
  have htrace : WordTrace (prefixWord ++ tailWord_1153590) baseStart_1153590 baseEnd_1153590 := by
    simpa [prefixWord, tailWord_1153590, baseEnd_1153590] using wordTrace_append hprefix tailTrace_1153590
  have hstable : (prefixWord ++ tailWord_1153590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153590).length < 2 ^ (prefixWord ++ tailWord_1153590).sum := by decide
  have hdescent : baseEnd_1153590 < baseStart_1153590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153722 : List Nat := [3, 1, 1, 1, 2, 3, 1, 9]
def baseStart_1153722 : Nat := 118140960795 + 1153722 * 2 ^ 59
def prefixEnd_1153722 : Nat := 4983230072969 + 3 ^ 40 * 1153722 * 2
def baseEnd_1153722 : Nat := 87765026320983746825057

theorem tailTrace_1153722 : CollatzResearch.WordTrace tailWord_1153722 prefixEnd_1153722 87765026320983746825057 := by
  unfold tailWord_1153722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10519924581567427218887855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28053132217513139250367613 10519924581567427218887855)
  ·
    refine ⟨15779886872351140828331783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10519924581567427218887855 15779886872351140828331783)
    ·
      refine ⟨23669830308526711242497675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15779886872351140828331783 23669830308526711242497675)
      ·
        refine ⟨35504745462790066863746513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23669830308526711242497675 35504745462790066863746513)
        ·
          refine ⟨26628559097092550147809885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35504745462790066863746513 26628559097092550147809885)
          ·
            refine ⟨9985709661409706305428707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26628559097092550147809885 9985709661409706305428707)
            ·
              refine ⟨14978564492114559458143061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9985709661409706305428707 14978564492114559458143061)
              ·
                refine ⟨87765026320983746825057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14978564492114559458143061 87765026320983746825057)
                ·
                  rfl

theorem cell21_1153722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_1153722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153722 prefixEnd_1153722 := by exact prefixLift 1153722
  have htrace : WordTrace (prefixWord ++ tailWord_1153722) baseStart_1153722 baseEnd_1153722 := by
    simpa [prefixWord, tailWord_1153722, baseEnd_1153722] using wordTrace_append hprefix tailTrace_1153722
  have hstable : (prefixWord ++ tailWord_1153722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153722).length < 2 ^ (prefixWord ++ tailWord_1153722).sum := by decide
  have hdescent : baseEnd_1153722 < baseStart_1153722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153753 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 5]
def baseStart_1153753 : Nat := 118140960795 + 1153753 * 2 ^ 59
def prefixEnd_1153753 : Nat := 4983230072969 + 3 ^ 40 * 1153753 * 2
def baseEnd_1153753 : Nat := 263302153585302075458441

theorem tailTrace_1153753 : CollatzResearch.WordTrace tailWord_1153753 prefixEnd_1153753 263302153585302075458441 := by
  unfold tailWord_1153753
  simp only [CollatzResearch.WordTrace]
  refine ⟨42080828989157401169929913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28053885992771600779953275 42080828989157401169929913)
  ·
    refine ⟨31560621741868050877447435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42080828989157401169929913 31560621741868050877447435)
    ·
      refine ⟨47340932612802076316171153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31560621741868050877447435 47340932612802076316171153)
      ·
        refine ⟨35505699459601557237128365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47340932612802076316171153 35505699459601557237128365)
        ·
          refine ⟨13314637297350583963923137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35505699459601557237128365 13314637297350583963923137)
          ·
            refine ⟨9985977973012937972942353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13314637297350583963923137 9985977973012937972942353)
            ·
              refine ⟨7489483479759703479706765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9985977973012937972942353 7489483479759703479706765)
              ·
                refine ⟨2808556304909888804890037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7489483479759703479706765 2808556304909888804890037)
                ·
                  refine ⟨263302153585302075458441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2808556304909888804890037 263302153585302075458441)
                  ·
                    rfl

theorem cell21_1153753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_1153753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153753 prefixEnd_1153753 := by exact prefixLift 1153753
  have htrace : WordTrace (prefixWord ++ tailWord_1153753) baseStart_1153753 baseEnd_1153753 := by
    simpa [prefixWord, tailWord_1153753, baseEnd_1153753] using wordTrace_append hprefix tailTrace_1153753
  have hstable : (prefixWord ++ tailWord_1153753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153753).length < 2 ^ (prefixWord ++ tailWord_1153753).sum := by decide
  have hdescent : baseEnd_1153753 < baseStart_1153753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153756 : List Nat := [2, 2, 5, 1, 1, 1, 3, 6]
def baseStart_1153756 : Nat := 118140960795 + 1153756 * 2 ^ 59
def prefixEnd_1153756 : Nat := 4983230072969 + 3 ^ 40 * 1153756 * 2
def baseEnd_1153756 : Nat := 87767612742058245636145

theorem tailTrace_1153756 : CollatzResearch.WordTrace tailWord_1153756 prefixEnd_1153756 87767612742058245636145 := by
  unfold tailWord_1153756
  simp only [CollatzResearch.WordTrace]
  refine ⟨21040469204073266341144561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28053958938764355121526081 21040469204073266341144561)
  ·
    refine ⟨15780351903054949755858421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21040469204073266341144561 15780351903054949755858421)
    ·
      refine ⟨1479407990911401539611727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15780351903054949755858421 1479407990911401539611727)
      ·
        refine ⟨2219111986367102309417591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1479407990911401539611727 2219111986367102309417591)
        ·
          refine ⟨3328667979550653464126387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219111986367102309417591 3328667979550653464126387)
          ·
            refine ⟨4993001969325980196189581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3328667979550653464126387 4993001969325980196189581)
            ·
              refine ⟨1872375738497242573571093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4993001969325980196189581 1872375738497242573571093)
              ·
                refine ⟨87767612742058245636145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1872375738497242573571093 87767612742058245636145)
                ·
                  rfl

theorem cell21_1153756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_1153756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153756 prefixEnd_1153756 := by exact prefixLift 1153756
  have htrace : WordTrace (prefixWord ++ tailWord_1153756) baseStart_1153756 baseEnd_1153756 := by
    simpa [prefixWord, tailWord_1153756, baseEnd_1153756] using wordTrace_append hprefix tailTrace_1153756
  have hstable : (prefixWord ++ tailWord_1153756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153756).length < 2 ^ (prefixWord ++ tailWord_1153756).sum := by decide
  have hdescent : baseEnd_1153756 < baseStart_1153756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153829 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 5]
def baseStart_1153829 : Nat := 118140960795 + 1153829 * 2 ^ 59
def prefixEnd_1153829 : Nat := 4983230072969 + 3 ^ 40 * 1153829 * 2
def baseEnd_1153829 : Nat := 263319497820742832191619

theorem tailTrace_1153829 : CollatzResearch.WordTrace tailWord_1153829 prefixEnd_1153829 263319497820742832191619 := by
  unfold tailWord_1153829
  simp only [CollatzResearch.WordTrace]
  refine ⟨42083600936882066149696541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28055733957921377433131027 42083600936882066149696541)
  ·
    refine ⟨15781350351330774806136203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42083600936882066149696541 15781350351330774806136203)
    ·
      refine ⟨23672025526996162209204305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15781350351330774806136203 23672025526996162209204305)
      ·
        refine ⟨17754019145247121656903229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23672025526996162209204305 17754019145247121656903229)
        ·
          refine ⟨6657757179467670621338711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17754019145247121656903229 6657757179467670621338711)
          ·
            refine ⟨9986635769201505932008067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6657757179467670621338711 9986635769201505932008067)
            ·
              refine ⟨14979953653802258898012101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9986635769201505932008067 14979953653802258898012101)
              ·
                refine ⟨2808741310087923543377269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14979953653802258898012101 2808741310087923543377269)
                ·
                  refine ⟨263319497820742832191619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2808741310087923543377269 263319497820742832191619)
                  ·
                    rfl

theorem cell21_1153829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_1153829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153829 prefixEnd_1153829 := by exact prefixLift 1153829
  have htrace : WordTrace (prefixWord ++ tailWord_1153829) baseStart_1153829 baseEnd_1153829 := by
    simpa [prefixWord, tailWord_1153829, baseEnd_1153829] using wordTrace_append hprefix tailTrace_1153829
  have hstable : (prefixWord ++ tailWord_1153829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153829).length < 2 ^ (prefixWord ++ tailWord_1153829).sum := by decide
  have hdescent : baseEnd_1153829 < baseStart_1153829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
