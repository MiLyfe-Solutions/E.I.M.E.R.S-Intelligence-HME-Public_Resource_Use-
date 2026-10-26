import V185TrunkScan22Chunk218

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1952133 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_1952133 : Nat := 118140960795 + 1952133 * 2 ^ 59
def prefixEnd_1952133 : Nat := 4983230072969 + 3 ^ 40 * 1952133 * 2
def baseEnd_1952133 : Nat := 668255020335677336239873

theorem tailTrace_1952133 : CollatzResearch.WordTrace tailWord_1952133 prefixEnd_1952133 668255020335677336239873 := by
  unfold tailWord_1952133
  simp only [CollatzResearch.WordTrace]
  refine ⟨71200139836763013618357053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47466759891175342412238035 71200139836763013618357053)
  ·
    refine ⟨26700052438786130106883895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71200139836763013618357053 26700052438786130106883895)
    ·
      refine ⟨40050078658179195160325843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26700052438786130106883895 40050078658179195160325843)
      ·
        refine ⟨60075117987268792740488765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40050078658179195160325843 60075117987268792740488765)
        ·
          refine ⟨22528169245225797277683287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60075117987268792740488765 22528169245225797277683287)
          ·
            refine ⟨33792253867838695916524931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22528169245225797277683287 33792253867838695916524931)
            ·
              refine ⟨50688380801758043874787397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33792253867838695916524931 50688380801758043874787397)
              ·
                refine ⟨9504071400329633226522637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50688380801758043874787397 9504071400329633226522637)
                ·
                  refine ⟨3564026775123612459945989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9504071400329633226522637 3564026775123612459945989)
                  ·
                    refine ⟨668255020335677336239873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3564026775123612459945989 668255020335677336239873)
                    ·
                      rfl

theorem cell22_1952133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_1952133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952133 prefixEnd_1952133 := by exact prefixLift 1952133
  have htrace : WordTrace (prefixWord ++ tailWord_1952133) baseStart_1952133 baseEnd_1952133 := by
    simpa [prefixWord, tailWord_1952133, baseEnd_1952133] using wordTrace_append hprefix tailTrace_1952133
  have hstable : (prefixWord ++ tailWord_1952133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952133).length < 2 ^ (prefixWord ++ tailWord_1952133).sum := by decide
  have hdescent : baseEnd_1952133 < baseStart_1952133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952137 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 5]
def baseStart_1952137 : Nat := 118140960795 + 1952137 * 2 ^ 59
def prefixEnd_1952137 : Nat := 4983230072969 + 3 ^ 40 * 1952137 * 2
def baseEnd_1952137 : Nat := 222752129872474219713287

theorem tailTrace_1952137 : CollatzResearch.WordTrace tailWord_1952137 prefixEnd_1952137 222752129872474219713287 := by
  unfold tailWord_1952137
  simp only [CollatzResearch.WordTrace]
  refine ⟨71200285728748522301502665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47466857152499014867668443 71200285728748522301502665)
  ·
    refine ⟨53400214296561391726126999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71200285728748522301502665 53400214296561391726126999)
    ·
      refine ⟨80100321444842087589190499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53400214296561391726126999 80100321444842087589190499)
      ·
        refine ⟨120150482167263131383785749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80100321444842087589190499 120150482167263131383785749)
        ·
          refine ⟨5632053851590459283614957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120150482167263131383785749 5632053851590459283614957)
          ·
            refine ⟨2112020194346422231355609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5632053851590459283614957 2112020194346422231355609)
            ·
              refine ⟨1584015145759816673516707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2112020194346422231355609 1584015145759816673516707)
              ·
                refine ⟨2376022718639725010275061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584015145759816673516707 2376022718639725010275061)
                ·
                  refine ⟨222752129872474219713287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2376022718639725010275061 222752129872474219713287)
                  ·
                    rfl

theorem cell22_1952137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 5].length) (baseStart_1952137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952137 prefixEnd_1952137 := by exact prefixLift 1952137
  have htrace : WordTrace (prefixWord ++ tailWord_1952137) baseStart_1952137 baseEnd_1952137 := by
    simpa [prefixWord, tailWord_1952137, baseEnd_1952137] using wordTrace_append hprefix tailTrace_1952137
  have hstable : (prefixWord ++ tailWord_1952137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952137).length < 2 ^ (prefixWord ++ tailWord_1952137).sum := by decide
  have hdescent : baseEnd_1952137 < baseStart_1952137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952163 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 3, 5]
def baseStart_1952163 : Nat := 118140960795 + 1952163 * 2 ^ 59
def prefixEnd_1952163 : Nat := 4983230072969 + 3 ^ 40 * 1952163 * 2
def baseEnd_1952163 : Nat := 668265289948767257989781

theorem tailTrace_1952163 : CollatzResearch.WordTrace tailWord_1952163 prefixEnd_1952163 668265289948767257989781 := by
  unfold tailWord_1952163
  simp only [CollatzResearch.WordTrace]
  refine ⟨71201234026654328741949143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47467489351102885827966095 71201234026654328741949143)
  ·
    refine ⟨106801851039981493112923715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71201234026654328741949143 106801851039981493112923715)
    ·
      refine ⟨160202776559972239669385573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106801851039981493112923715 160202776559972239669385573)
      ·
        refine ⟨30038020604994794938009795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160202776559972239669385573 30038020604994794938009795)
        ·
          refine ⟨45057030907492192407014693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30038020604994794938009795 45057030907492192407014693)
          ·
            refine ⟨8448193295154786076315255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45057030907492192407014693 8448193295154786076315255)
            ·
              refine ⟨12672289942732179114472883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8448193295154786076315255 12672289942732179114472883)
              ·
                refine ⟨19008434914098268671709325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12672289942732179114472883 19008434914098268671709325)
                ·
                  refine ⟨7128163092786850751890997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19008434914098268671709325 7128163092786850751890997)
                  ·
                    refine ⟨668265289948767257989781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7128163092786850751890997 668265289948767257989781)
                    ·
                      rfl

theorem cell22_1952163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_1952163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952163 prefixEnd_1952163 := by exact prefixLift 1952163
  have htrace : WordTrace (prefixWord ++ tailWord_1952163) baseStart_1952163 baseEnd_1952163 := by
    simpa [prefixWord, tailWord_1952163, baseEnd_1952163] using wordTrace_append hprefix tailTrace_1952163
  have hstable : (prefixWord ++ tailWord_1952163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952163).length < 2 ^ (prefixWord ++ tailWord_1952163).sum := by decide
  have hdescent : baseEnd_1952163 < baseStart_1952163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952165 : List Nat := [1, 3, 1, 2, 1, 1, 4, 5, 4]
def baseStart_1952165 : Nat := 118140960795 + 1952165 * 2 ^ 59
def prefixEnd_1952165 : Nat := 4983230072969 + 3 ^ 40 * 1952165 * 2
def baseEnd_1952165 : Nat := 222755324863213306479925

theorem tailTrace_1952165 : CollatzResearch.WordTrace tailWord_1952165 prefixEnd_1952165 222755324863213306479925 := by
  unfold tailWord_1952165
  simp only [CollatzResearch.WordTrace]
  refine ⟨71201306972647083083521949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47467537981764722055681299 71201306972647083083521949)
  ·
    refine ⟨26700490114742656156320731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71201306972647083083521949 26700490114742656156320731)
    ·
      refine ⟨40050735172113984234481097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26700490114742656156320731 40050735172113984234481097)
      ·
        refine ⟨30038051379085488175860823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40050735172113984234481097 30038051379085488175860823)
        ·
          refine ⟨45057077068628232263791235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30038051379085488175860823 45057077068628232263791235)
          ·
            refine ⟨67585615602942348395686853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45057077068628232263791235 67585615602942348395686853)
            ·
              refine ⟨12672302925551690324191285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67585615602942348395686853 12672302925551690324191285)
              ·
                refine ⟨1188028399270470967892933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12672302925551690324191285 1188028399270470967892933)
                ·
                  refine ⟨222755324863213306479925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188028399270470967892933 222755324863213306479925)
                  ·
                    rfl

theorem cell22_1952165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_1952165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952165 prefixEnd_1952165 := by exact prefixLift 1952165
  have htrace : WordTrace (prefixWord ++ tailWord_1952165) baseStart_1952165 baseEnd_1952165 := by
    simpa [prefixWord, tailWord_1952165, baseEnd_1952165] using wordTrace_append hprefix tailTrace_1952165
  have hstable : (prefixWord ++ tailWord_1952165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952165).length < 2 ^ (prefixWord ++ tailWord_1952165).sum := by decide
  have hdescent : baseEnd_1952165 < baseStart_1952165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952212 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_1952212 : Nat := 118140960795 + 1952212 * 2 ^ 59
def prefixEnd_1952212 : Nat := 4983230072969 + 3 ^ 40 * 1952212 * 2
def baseEnd_1952212 : Nat := 668282063650147463514631

theorem tailTrace_1952212 : CollatzResearch.WordTrace tailWord_1952212 prefixEnd_1952212 668282063650147463514631 := by
  unfold tailWord_1952212
  simp only [CollatzResearch.WordTrace]
  refine ⟨35601510601738405055241445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47468680802317873406988593 35601510601738405055241445)
  ·
    refine ⟨6675283237825950947857771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35601510601738405055241445 6675283237825950947857771)
    ·
      refine ⟨10012924856738926421786657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6675283237825950947857771 10012924856738926421786657)
      ·
        refine ⟨7509693642554194816339993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10012924856738926421786657 7509693642554194816339993)
        ·
          refine ⟨5632270231915646112254995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7509693642554194816339993 5632270231915646112254995)
          ·
            refine ⟨8448405347873469168382493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632270231915646112254995 8448405347873469168382493)
            ·
              refine ⟨3168152005452550938143435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8448405347873469168382493 3168152005452550938143435)
              ·
                refine ⟨4752228008178826407215153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168152005452550938143435 4752228008178826407215153)
                ·
                  refine ⟨3564171006134119805411365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4752228008178826407215153 3564171006134119805411365)
                  ·
                    refine ⟨668282063650147463514631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3564171006134119805411365 668282063650147463514631)
                    ·
                      rfl

theorem cell22_1952212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_1952212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952212 prefixEnd_1952212 := by exact prefixLift 1952212
  have htrace : WordTrace (prefixWord ++ tailWord_1952212) baseStart_1952212 baseEnd_1952212 := by
    simpa [prefixWord, tailWord_1952212, baseEnd_1952212] using wordTrace_append hprefix tailTrace_1952212
  have hstable : (prefixWord ++ tailWord_1952212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952212).length < 2 ^ (prefixWord ++ tailWord_1952212).sum := by decide
  have hdescent : baseEnd_1952212 < baseStart_1952212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952225 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 5, 3]
def baseStart_1952225 : Nat := 118140960795 + 1952225 * 2 ^ 59
def prefixEnd_1952225 : Nat := 4983230072969 + 3 ^ 40 * 1952225 * 2
def baseEnd_1952225 : Nat := 668286513815819762939591

theorem tailTrace_1952225 : CollatzResearch.WordTrace tailWord_1952225 prefixEnd_1952225 668286513815819762939591 := by
  unfold tailWord_1952225
  simp only [CollatzResearch.WordTrace]
  refine ⟨71203495352429713330706129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47468996901619808887137419 71203495352429713330706129)
  ·
    refine ⟨53402621514322284998029597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71203495352429713330706129 53402621514322284998029597)
    ·
      refine ⟨20025983067870856874261099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53402621514322284998029597 20025983067870856874261099)
      ·
        refine ⟨30038974601806285311391649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20025983067870856874261099 30038974601806285311391649)
        ·
          refine ⟨22529230951354713983543737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30038974601806285311391649 22529230951354713983543737)
          ·
            refine ⟨16896923213516035487657803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22529230951354713983543737 16896923213516035487657803)
            ·
              refine ⟨25345384820274053231486705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16896923213516035487657803 25345384820274053231486705)
              ·
                refine ⟨19009038615205539923615029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25345384820274053231486705 19009038615205539923615029)
                ·
                  refine ⟨1782097370175519367838909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19009038615205539923615029 1782097370175519367838909)
                  ·
                    refine ⟨668286513815819762939591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782097370175519367838909 668286513815819762939591)
                    ·
                      rfl

theorem cell22_1952225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_1952225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952225 prefixEnd_1952225 := by exact prefixLift 1952225
  have htrace : WordTrace (prefixWord ++ tailWord_1952225) baseStart_1952225 baseEnd_1952225 := by
    simpa [prefixWord, tailWord_1952225, baseEnd_1952225] using wordTrace_append hprefix tailTrace_1952225
  have hstable : (prefixWord ++ tailWord_1952225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952225).length < 2 ^ (prefixWord ++ tailWord_1952225).sum := by decide
  have hdescent : baseEnd_1952225 < baseStart_1952225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952377 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 5, 3]
def baseStart_1952377 : Nat := 118140960795 + 1952377 * 2 ^ 59
def prefixEnd_1952377 : Nat := 4983230072969 + 3 ^ 40 * 1952377 * 2
def baseEnd_1952377 : Nat := 668338546522142033139125

theorem tailTrace_1952377 : CollatzResearch.WordTrace tailWord_1952377 prefixEnd_1952377 668338546522142033139125 := by
  unfold tailWord_1952377
  simp only [CollatzResearch.WordTrace]
  refine ⟨71209039247879043290239385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47472692831919362193492923 71209039247879043290239385)
  ·
    refine ⟨53406779435909282467679539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71209039247879043290239385 53406779435909282467679539)
    ·
      refine ⟨80110169153863923701519309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53406779435909282467679539 80110169153863923701519309)
      ·
        refine ⟨30041313432698971388069741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80110169153863923701519309 30041313432698971388069741)
        ·
          refine ⟨11265492537262114270526153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30041313432698971388069741 11265492537262114270526153)
          ·
            refine ⟨8449119402946585702894615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11265492537262114270526153 8449119402946585702894615)
            ·
              refine ⟨12673679104419878554341923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8449119402946585702894615 12673679104419878554341923)
              ·
                refine ⟨19010518656629817831512885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12673679104419878554341923 19010518656629817831512885)
                ·
                  refine ⟨1782236124059045421704333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19010518656629817831512885 1782236124059045421704333)
                  ·
                    refine ⟨668338546522142033139125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782236124059045421704333 668338546522142033139125)
                    ·
                      rfl

theorem cell22_1952377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 3].length) (baseStart_1952377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952377 prefixEnd_1952377 := by exact prefixLift 1952377
  have htrace : WordTrace (prefixWord ++ tailWord_1952377) baseStart_1952377 baseEnd_1952377 := by
    simpa [prefixWord, tailWord_1952377, baseEnd_1952377] using wordTrace_append hprefix tailTrace_1952377
  have hstable : (prefixWord ++ tailWord_1952377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952377).length < 2 ^ (prefixWord ++ tailWord_1952377).sum := by decide
  have hdescent : baseEnd_1952377 < baseStart_1952377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952381 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_1952381 : Nat := 118140960795 + 1952381 * 2 ^ 59
def prefixEnd_1952381 : Nat := 4983230072969 + 3 ^ 40 * 1952381 * 2
def baseEnd_1952381 : Nat := 668339915803887356039113

theorem tailTrace_1952381 : CollatzResearch.WordTrace tailWord_1952381 prefixEnd_1952381 668339915803887356039113 := by
  unfold tailWord_1952381
  simp only [CollatzResearch.WordTrace]
  refine ⟨71209185139864551973384997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47472790093243034648923331 71209185139864551973384997)
  ·
    refine ⟨13351722213724603495009687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71209185139864551973384997 13351722213724603495009687)
    ·
      refine ⟨20027583320586905242514531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13351722213724603495009687 20027583320586905242514531)
      ·
        refine ⟨30041374980880357863771797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20027583320586905242514531 30041374980880357863771797)
        ·
          refine ⟨1408189452228766774864303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30041374980880357863771797 1408189452228766774864303)
          ·
            refine ⟨2112284178343150162296455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408189452228766774864303 2112284178343150162296455)
            ·
              refine ⟨3168426267514725243444683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112284178343150162296455 3168426267514725243444683)
              ·
                refine ⟨4752639401272087865167025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168426267514725243444683 4752639401272087865167025)
                ·
                  refine ⟨3564479550954065898875269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4752639401272087865167025 3564479550954065898875269)
                  ·
                    refine ⟨668339915803887356039113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3564479550954065898875269 668339915803887356039113)
                    ·
                      rfl

theorem cell22_1952381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_1952381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952381 prefixEnd_1952381 := by exact prefixLift 1952381
  have htrace : WordTrace (prefixWord ++ tailWord_1952381) baseStart_1952381 baseEnd_1952381 := by
    simpa [prefixWord, tailWord_1952381, baseEnd_1952381] using wordTrace_append hprefix tailTrace_1952381
  have hstable : (prefixWord ++ tailWord_1952381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952381).length < 2 ^ (prefixWord ++ tailWord_1952381).sum := by decide
  have hdescent : baseEnd_1952381 < baseStart_1952381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952488 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 1, 4]
def baseStart_1952488 : Nat := 118140960795 + 1952488 * 2 ^ 59
def prefixEnd_1952488 : Nat := 4983230072969 + 3 ^ 40 * 1952488 * 2
def baseEnd_1952488 : Nat := 668376544090574743613785

theorem tailTrace_1952488 : CollatzResearch.WordTrace tailWord_1952488 prefixEnd_1952488 668376544090574743613785 := by
  unfold tailWord_1952488
  simp only [CollatzResearch.WordTrace]
  refine ⟨35606543875238454623765059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47475391833651272831686745 35606543875238454623765059)
  ·
    refine ⟨53409815812857681935647589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35606543875238454623765059 53409815812857681935647589)
    ·
      refine ⟨10014340464910815362933923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53409815812857681935647589 10014340464910815362933923)
      ·
        refine ⟨15021510697366223044400885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10014340464910815362933923 15021510697366223044400885)
        ·
          refine ⟨1408266627878083410412583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15021510697366223044400885 1408266627878083410412583)
          ·
            refine ⟨2112399941817125115618875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408266627878083410412583 2112399941817125115618875)
            ·
              refine ⟨3168599912725687673428313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112399941817125115618875 3168599912725687673428313)
              ·
                refine ⟨2376449934544265755071235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168599912725687673428313 2376449934544265755071235)
                ·
                  refine ⟨3564674901816398632606853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376449934544265755071235 3564674901816398632606853)
                  ·
                    refine ⟨668376544090574743613785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3564674901816398632606853 668376544090574743613785)
                    ·
                      rfl

theorem cell22_1952488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_1952488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952488 prefixEnd_1952488 := by exact prefixLift 1952488
  have htrace : WordTrace (prefixWord ++ tailWord_1952488) baseStart_1952488 baseEnd_1952488 := by
    simpa [prefixWord, tailWord_1952488, baseEnd_1952488] using wordTrace_append hprefix tailTrace_1952488
  have hstable : (prefixWord ++ tailWord_1952488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952488).length < 2 ^ (prefixWord ++ tailWord_1952488).sum := by decide
  have hdescent : baseEnd_1952488 < baseStart_1952488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952546 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1952546 : Nat := 118140960795 + 1952546 * 2 ^ 59
def prefixEnd_1952546 : Nat := 4983230072969 + 3 ^ 40 * 1952546 * 2
def baseEnd_1952546 : Nat := 668396398675881925663607

theorem tailTrace_1952546 : CollatzResearch.WordTrace tailWord_1952546 prefixEnd_1952546 668396398675881925663607 := by
  unfold tailWord_1952546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17803800796066696288285373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47476802122844523435427661 17803800796066696288285373)
  ·
    refine ⟨6676425298525011108107015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17803800796066696288285373 6676425298525011108107015)
    ·
      refine ⟨10014637947787516662160523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6676425298525011108107015 10014637947787516662160523)
      ·
        refine ⟨15021956921681274993240785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10014637947787516662160523 15021956921681274993240785)
        ·
          refine ⟨11266467691260956244930589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15021956921681274993240785 11266467691260956244930589)
          ·
            refine ⟨4224925384222858591848971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11266467691260956244930589 4224925384222858591848971)
            ·
              refine ⟨6337388076334287887773457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224925384222858591848971 6337388076334287887773457)
              ·
                refine ⟨4753041057250715915830093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6337388076334287887773457 4753041057250715915830093)
                ·
                  refine ⟨1782390396469018468436285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4753041057250715915830093 1782390396469018468436285)
                  ·
                    refine ⟨668396398675881925663607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782390396469018468436285 668396398675881925663607)
                    ·
                      rfl

theorem cell22_1952546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1952546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952546 prefixEnd_1952546 := by exact prefixLift 1952546
  have htrace : WordTrace (prefixWord ++ tailWord_1952546) baseStart_1952546 baseEnd_1952546 := by
    simpa [prefixWord, tailWord_1952546, baseEnd_1952546] using wordTrace_append hprefix tailTrace_1952546
  have hstable : (prefixWord ++ tailWord_1952546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952546).length < 2 ^ (prefixWord ++ tailWord_1952546).sum := by decide
  have hdescent : baseEnd_1952546 < baseStart_1952546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952563 : List Nat := [1, 1, 1, 2, 6, 2, 2, 3, 1, 3]
def baseStart_1952563 : Nat := 118140960795 + 1952563 * 2 ^ 59
def prefixEnd_1952563 : Nat := 4983230072969 + 3 ^ 40 * 1952563 * 2
def baseEnd_1952563 : Nat := 668402218123299547988555

theorem tailTrace_1952563 : CollatzResearch.WordTrace tailWord_1952563 prefixEnd_1952563 668402218123299547988555 := by
  unfold tailWord_1952563
  simp only [CollatzResearch.WordTrace]
  refine ⟨71215823225205197056510343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47477215483470131371006895 71215823225205197056510343)
  ·
    refine ⟨106823734837807795584765515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71215823225205197056510343 106823734837807795584765515)
    ·
      refine ⟨160235602256711693377148273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106823734837807795584765515 160235602256711693377148273)
      ·
        refine ⟨120176701692533770032861205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160235602256711693377148273 120176701692533770032861205)
        ·
          refine ⟨5633282891837520470290369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120176701692533770032861205 5633282891837520470290369)
          ·
            refine ⟨4224962168878140352717777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5633282891837520470290369 4224962168878140352717777)
            ·
              refine ⟨3168721626658605264538333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224962168878140352717777 3168721626658605264538333)
              ·
                refine ⟨1188270609996976974201875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3168721626658605264538333 1188270609996976974201875)
                ·
                  refine ⟨1782405914995465461302813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188270609996976974201875 1782405914995465461302813)
                  ·
                    refine ⟨668402218123299547988555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782405914995465461302813 668402218123299547988555)
                    ·
                      rfl

theorem cell22_1952563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 1, 3].length) (baseStart_1952563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952563 prefixEnd_1952563 := by exact prefixLift 1952563
  have htrace : WordTrace (prefixWord ++ tailWord_1952563) baseStart_1952563 baseEnd_1952563 := by
    simpa [prefixWord, tailWord_1952563, baseEnd_1952563] using wordTrace_append hprefix tailTrace_1952563
  have hstable : (prefixWord ++ tailWord_1952563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952563).length < 2 ^ (prefixWord ++ tailWord_1952563).sum := by decide
  have hdescent : baseEnd_1952563 < baseStart_1952563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952580 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1952580 : Nat := 118140960795 + 1952580 * 2 ^ 59
def prefixEnd_1952580 : Nat := 4983230072969 + 3 ^ 40 * 1952580 * 2
def baseEnd_1952580 : Nat := 668408037570717170313503

theorem tailTrace_1952580 : CollatzResearch.WordTrace tailWord_1952580 prefixEnd_1952580 668408037570717170313503 := by
  unfold tailWord_1952580
  simp only [CollatzResearch.WordTrace]
  refine ⟨35608221633071804479939597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47477628844095739306586129 35608221633071804479939597)
  ·
    refine ⟨13353083112401926679977349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35608221633071804479939597 13353083112401926679977349)
    ·
      refine ⟨2503703083575361252495753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13353083112401926679977349 2503703083575361252495753)
      ·
        refine ⟨1877777312681520939371815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2503703083575361252495753 1877777312681520939371815)
        ·
          refine ⟨2816665969022281409057723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877777312681520939371815 2816665969022281409057723)
          ·
            refine ⟨4224998953533422113586585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816665969022281409057723 4224998953533422113586585)
            ·
              refine ⟨3168749215150066585189939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224998953533422113586585 3168749215150066585189939)
              ·
                refine ⟨4753123822725099877784909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168749215150066585189939 4753123822725099877784909)
                ·
                  refine ⟨1782421433521912454169341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4753123822725099877784909 1782421433521912454169341)
                  ·
                    refine ⟨668408037570717170313503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782421433521912454169341 668408037570717170313503)
                    ·
                      rfl

theorem cell22_1952580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1952580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952580 prefixEnd_1952580 := by exact prefixLift 1952580
  have htrace : WordTrace (prefixWord ++ tailWord_1952580) baseStart_1952580 baseEnd_1952580 := by
    simpa [prefixWord, tailWord_1952580, baseEnd_1952580] using wordTrace_append hprefix tailTrace_1952580
  have hstable : (prefixWord ++ tailWord_1952580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952580).length < 2 ^ (prefixWord ++ tailWord_1952580).sum := by decide
  have hdescent : baseEnd_1952580 < baseStart_1952580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952619 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 4, 3]
def baseStart_1952619 : Nat := 118140960795 + 1952619 * 2 ^ 59
def prefixEnd_1952619 : Nat := 4983230072969 + 3 ^ 40 * 1952619 * 2
def baseEnd_1952619 : Nat := 668421388067734068588383

theorem tailTrace_1952619 : CollatzResearch.WordTrace tailWord_1952619 prefixEnd_1952619 668421388067734068588383 := by
  unfold tailWord_1952619
  simp only [CollatzResearch.WordTrace]
  refine ⟨71217865713002318620548911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47478577142001545747032607 71217865713002318620548911)
  ·
    refine ⟨106826798569503477930823367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71217865713002318620548911 106826798569503477930823367)
    ·
      refine ⟨160240197854255216896235051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106826798569503477930823367 160240197854255216896235051)
      ·
        refine ⟨240360296781382825344352577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160240197854255216896235051 240360296781382825344352577)
        ·
          refine ⟨180270222586037119008264433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240360296781382825344352577 180270222586037119008264433)
          ·
            refine ⟨135202666939527839256198325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180270222586037119008264433 135202666939527839256198325)
            ·
              refine ⟨12675250025580734930268593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135202666939527839256198325 12675250025580734930268593)
              ·
                refine ⟨9506437519185551197701445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12675250025580734930268593 9506437519185551197701445)
                ·
                  refine ⟨1782457034847290849569021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9506437519185551197701445 1782457034847290849569021)
                  ·
                    refine ⟨668421388067734068588383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782457034847290849569021 668421388067734068588383)
                    ·
                      rfl

theorem cell22_1952619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 3].length) (baseStart_1952619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952619 prefixEnd_1952619 := by exact prefixLift 1952619
  have htrace : WordTrace (prefixWord ++ tailWord_1952619) baseStart_1952619 baseEnd_1952619 := by
    simpa [prefixWord, tailWord_1952619, baseEnd_1952619] using wordTrace_append hprefix tailTrace_1952619
  have hstable : (prefixWord ++ tailWord_1952619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952619).length < 2 ^ (prefixWord ++ tailWord_1952619).sum := by decide
  have hdescent : baseEnd_1952619 < baseStart_1952619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952649 : List Nat := [1, 2, 1, 1, 5, 3, 2, 7]
def baseStart_1952649 : Nat := 118140960795 + 1952649 * 2 ^ 59
def prefixEnd_1952649 : Nat := 4983230072969 + 3 ^ 40 * 1952649 * 2
def baseEnd_1952649 : Nat := 74270184186758221148699

theorem tailTrace_1952649 : CollatzResearch.WordTrace tailWord_1952649 prefixEnd_1952649 74270184186758221148699 := by
  unfold tailWord_1952649
  simp only [CollatzResearch.WordTrace]
  refine ⟨71218959902893633744141001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47479306601929089162760667 71218959902893633744141001)
  ·
    refine ⟨53414219927170225308105751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71218959902893633744141001 53414219927170225308105751)
    ·
      refine ⟨80121329890755337962158627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53414219927170225308105751 80121329890755337962158627)
      ·
        refine ⟨120181994836133006943237941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80121329890755337962158627 120181994836133006943237941)
        ·
          refine ⟨11267062015887469400928557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120181994836133006943237941 11267062015887469400928557)
          ·
            refine ⟨4225148255957801025348209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11267062015887469400928557 4225148255957801025348209)
            ·
              refine ⟨3168861191968350769011157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4225148255957801025348209 3168861191968350769011157)
              ·
                refine ⟨74270184186758221148699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3168861191968350769011157 74270184186758221148699)
                ·
                  rfl

theorem cell22_1952649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 7].length) (baseStart_1952649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952649 prefixEnd_1952649 := by exact prefixLift 1952649
  have htrace : WordTrace (prefixWord ++ tailWord_1952649) baseStart_1952649 baseEnd_1952649 := by
    simpa [prefixWord, tailWord_1952649, baseEnd_1952649] using wordTrace_append hprefix tailTrace_1952649
  have hstable : (prefixWord ++ tailWord_1952649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952649).length < 2 ^ (prefixWord ++ tailWord_1952649).sum := by decide
  have hdescent : baseEnd_1952649 < baseStart_1952649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952668 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_1952668 : Nat := 118140960795 + 1952668 * 2 ^ 59
def prefixEnd_1952668 : Nat := 4983230072969 + 3 ^ 40 * 1952668 * 2
def baseEnd_1952668 : Nat := 668438161769114274113233

theorem tailTrace_1952668 : CollatzResearch.WordTrace tailWord_1952668 prefixEnd_1952668 668438161769114274113233 := by
  unfold tailWord_1952668
  simp only [CollatzResearch.WordTrace]
  refine ⟨35609826444912399994541329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47479768593216533326055105 35609826444912399994541329)
  ·
    refine ⟨26707369833684299995905997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35609826444912399994541329 26707369833684299995905997)
    ·
      refine ⟨10015263687631612498464749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26707369833684299995905997 10015263687631612498464749)
      ·
        refine ⟨3755723882861854686924281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10015263687631612498464749 3755723882861854686924281)
        ·
          refine ⟨2816792912146391015193211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3755723882861854686924281 2816792912146391015193211)
          ·
            refine ⟨4225189368219586522789817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816792912146391015193211 4225189368219586522789817)
            ·
              refine ⟨3168892026164689892092363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4225189368219586522789817 3168892026164689892092363)
              ·
                refine ⟨4753338039247034838138545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168892026164689892092363 4753338039247034838138545)
                ·
                  refine ⟨3565003529435276128603909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4753338039247034838138545 3565003529435276128603909)
                  ·
                    refine ⟨668438161769114274113233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3565003529435276128603909 668438161769114274113233)
                    ·
                      rfl

theorem cell22_1952668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_1952668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952668 prefixEnd_1952668 := by exact prefixLift 1952668
  have htrace : WordTrace (prefixWord ++ tailWord_1952668) baseStart_1952668 baseEnd_1952668 := by
    simpa [prefixWord, tailWord_1952668, baseEnd_1952668] using wordTrace_append hprefix tailTrace_1952668
  have hstable : (prefixWord ++ tailWord_1952668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952668).length < 2 ^ (prefixWord ++ tailWord_1952668).sum := by decide
  have hdescent : baseEnd_1952668 < baseStart_1952668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952698 : List Nat := [3, 1, 1, 1, 2, 1, 5, 4, 1, 3]
def baseStart_1952698 : Nat := 118140960795 + 1952698 * 2 ^ 59
def prefixEnd_1952698 : Nat := 4983230072969 + 3 ^ 40 * 1952698 * 2
def baseEnd_1952698 : Nat := 668448431382204195863141

theorem tailTrace_1952698 : CollatzResearch.WordTrace tailWord_1952698 prefixEnd_1952698 668448431382204195863141 := by
  unfold tailWord_1952698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17805186769929028778168687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47480498053144076741783165 17805186769929028778168687)
  ·
    refine ⟨26707780154893543167253031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17805186769929028778168687 26707780154893543167253031)
    ·
      refine ⟨40061670232340314750879547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26707780154893543167253031 40061670232340314750879547)
      ·
        refine ⟨60092505348510472126319321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40061670232340314750879547 60092505348510472126319321)
        ·
          refine ⟨45069379011382854094739491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60092505348510472126319321 45069379011382854094739491)
          ·
            refine ⟨67604068517074281142109237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45069379011382854094739491 67604068517074281142109237)
            ·
              refine ⟨6337881423475713857072741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67604068517074281142109237 6337881423475713857072741)
              ·
                refine ⟨1188352766901696348201139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6337881423475713857072741 1188352766901696348201139)
                ·
                  refine ⟨1782529150352544522301709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188352766901696348201139 1782529150352544522301709)
                  ·
                    refine ⟨668448431382204195863141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782529150352544522301709 668448431382204195863141)
                    ·
                      rfl

theorem cell22_1952698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_1952698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952698 prefixEnd_1952698 := by exact prefixLift 1952698
  have htrace : WordTrace (prefixWord ++ tailWord_1952698) baseStart_1952698 baseEnd_1952698 := by
    simpa [prefixWord, tailWord_1952698, baseEnd_1952698] using wordTrace_append hprefix tailTrace_1952698
  have hstable : (prefixWord ++ tailWord_1952698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952698).length < 2 ^ (prefixWord ++ tailWord_1952698).sum := by decide
  have hdescent : baseEnd_1952698 < baseStart_1952698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952717 : List Nat := [1, 6, 3, 1, 1, 1, 3, 6]
def baseStart_1952717 : Nat := 118140960795 + 1952717 * 2 ^ 59
def prefixEnd_1952717 : Nat := 4983230072969 + 3 ^ 40 * 1952717 * 2
def baseEnd_1952717 : Nat := 74272770607832719959787

theorem tailTrace_1952717 : CollatzResearch.WordTrace tailWord_1952717 prefixEnd_1952717 74272770607832719959787 := by
  unfold tailWord_1952717
  simp only [CollatzResearch.WordTrace]
  refine ⟨71221440066647281357616405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47480960044431520905077603 71221440066647281357616405)
  ·
    refine ⟨3338505003124091313638269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71221440066647281357616405 3338505003124091313638269)
    ·
      refine ⟨1251939376171534242614351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3338505003124091313638269 1251939376171534242614351)
      ·
        refine ⟨1877909064257301363921527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251939376171534242614351 1877909064257301363921527)
        ·
          refine ⟨2816863596385952045882291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877909064257301363921527 2816863596385952045882291)
          ·
            refine ⟨4225295394578928068823437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816863596385952045882291 4225295394578928068823437)
            ·
              refine ⟨1584485772967098025808789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4225295394578928068823437 1584485772967098025808789)
              ·
                refine ⟨74272770607832719959787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1584485772967098025808789 74272770607832719959787)
                ·
                  rfl

theorem cell22_1952717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 6].length) (baseStart_1952717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952717 prefixEnd_1952717 := by exact prefixLift 1952717
  have htrace : WordTrace (prefixWord ++ tailWord_1952717) baseStart_1952717 baseEnd_1952717 := by
    simpa [prefixWord, tailWord_1952717, baseEnd_1952717] using wordTrace_append hprefix tailTrace_1952717
  have hstable : (prefixWord ++ tailWord_1952717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952717).length < 2 ^ (prefixWord ++ tailWord_1952717).sum := by decide
  have hdescent : baseEnd_1952717 < baseStart_1952717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952739 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 8]
def baseStart_1952739 : Nat := 118140960795 + 1952739 * 2 ^ 59
def prefixEnd_1952739 : Nat := 4983230072969 + 3 ^ 40 * 1952739 * 2
def baseEnd_1952739 : Nat := 222820822173364585196005

theorem tailTrace_1952739 : CollatzResearch.WordTrace tailWord_1952739 prefixEnd_1952739 222820822173364585196005 := by
  unfold tailWord_1952739
  simp only [CollatzResearch.WordTrace]
  refine ⟨71222242472567579114917271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47481494981711719409944847 71222242472567579114917271)
  ·
    refine ⟨106833363708851368672375907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71222242472567579114917271 106833363708851368672375907)
    ·
      refine ⟨160250045563277053008563861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106833363708851368672375907 160250045563277053008563861)
      ·
        refine ⟨7511720885778611859776431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160250045563277053008563861 7511720885778611859776431)
        ·
          refine ⟨11267581328667917789664647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7511720885778611859776431 11267581328667917789664647)
          ·
            refine ⟨16901371993001876684496971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11267581328667917789664647 16901371993001876684496971)
            ·
              refine ⟨25352057989502815026745457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16901371993001876684496971 25352057989502815026745457)
              ·
                refine ⟨19014043492127111270059093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25352057989502815026745457 19014043492127111270059093)
                ·
                  refine ⟨222820822173364585196005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19014043492127111270059093 222820822173364585196005)
                  ·
                    rfl

theorem cell22_1952739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 8].length) (baseStart_1952739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952739 prefixEnd_1952739 := by exact prefixLift 1952739
  have htrace : WordTrace (prefixWord ++ tailWord_1952739) baseStart_1952739 baseEnd_1952739 := by
    simpa [prefixWord, tailWord_1952739, baseEnd_1952739] using wordTrace_append hprefix tailTrace_1952739
  have hstable : (prefixWord ++ tailWord_1952739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952739).length < 2 ^ (prefixWord ++ tailWord_1952739).sum := by decide
  have hdescent : baseEnd_1952739 < baseStart_1952739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952801 : List Nat := [1, 2, 3, 2, 3, 3, 8]
def baseStart_1952801 : Nat := 118140960795 + 1952801 * 2 ^ 59
def prefixEnd_1952801 : Nat := 4983230072969 + 3 ^ 40 * 1952801 * 2
def baseEnd_1952801 : Nat := 24758655199523935575475

theorem tailTrace_1952801 : CollatzResearch.WordTrace tailWord_1952801 prefixEnd_1952801 24758655199523935575475 := by
  unfold tailWord_1952801
  simp only [CollatzResearch.WordTrace]
  refine ⟨71224503798342963703674257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47483002532228642469116171 71224503798342963703674257)
  ·
    refine ⟨53418377848757222777755693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71224503798342963703674257 53418377848757222777755693)
    ·
      refine ⟨20031891693283958541658385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53418377848757222777755693 20031891693283958541658385)
      ·
        refine ⟨15023918769962968906243789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20031891693283958541658385 15023918769962968906243789)
        ·
          refine ⟨5633969538736113339841421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15023918769962968906243789 5633969538736113339841421)
          ·
            refine ⟨2112738577026042502440533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5633969538736113339841421 2112738577026042502440533)
            ·
              refine ⟨24758655199523935575475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2112738577026042502440533 24758655199523935575475)
              ·
                rfl

theorem cell22_1952801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 8].length) (baseStart_1952801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952801 prefixEnd_1952801 := by exact prefixLift 1952801
  have htrace : WordTrace (prefixWord ++ tailWord_1952801) baseStart_1952801 baseEnd_1952801 := by
    simpa [prefixWord, tailWord_1952801, baseEnd_1952801] using wordTrace_append hprefix tailTrace_1952801
  have hstable : (prefixWord ++ tailWord_1952801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952801).length < 2 ^ (prefixWord ++ tailWord_1952801).sum := by decide
  have hdescent : baseEnd_1952801 < baseStart_1952801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952807 : List Nat := [1, 1, 7, 1, 1, 2, 3, 2, 4]
def baseStart_1952807 : Nat := 118140960795 + 1952807 * 2 ^ 59
def prefixEnd_1952807 : Nat := 4983230072969 + 3 ^ 40 * 1952807 * 2
def baseEnd_1952807 : Nat := 222828581436588081629269

theorem tailTrace_1952807 : CollatzResearch.WordTrace tailWord_1952807 prefixEnd_1952807 222828581436588081629269 := by
  unfold tailWord_1952807
  simp only [CollatzResearch.WordTrace]
  refine ⟨71224722636321226728392675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47483148424214151152261783 71224722636321226728392675)
  ·
    refine ⟨106837083954481840092589013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71224722636321226728392675 106837083954481840092589013)
    ·
      refine ⟨2503994155183168127170055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 106837083954481840092589013 2503994155183168127170055)
      ·
        refine ⟨3755991232774752190755083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503994155183168127170055 3755991232774752190755083)
        ·
          refine ⟨5633986849162128286132625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755991232774752190755083 5633986849162128286132625)
          ·
            refine ⟨4225490136871596214599469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5633986849162128286132625 4225490136871596214599469)
            ·
              refine ⟨1584558801326848580474801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4225490136871596214599469 1584558801326848580474801)
              ·
                refine ⟨1188419100995136435356101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584558801326848580474801 1188419100995136435356101)
                ·
                  refine ⟨222828581436588081629269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188419100995136435356101 222828581436588081629269)
                  ·
                    rfl

theorem cell22_1952807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 4].length) (baseStart_1952807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952807 prefixEnd_1952807 := by exact prefixLift 1952807
  have htrace : WordTrace (prefixWord ++ tailWord_1952807) baseStart_1952807 baseEnd_1952807 := by
    simpa [prefixWord, tailWord_1952807, baseEnd_1952807] using wordTrace_append hprefix tailTrace_1952807
  have hstable : (prefixWord ++ tailWord_1952807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952807).length < 2 ^ (prefixWord ++ tailWord_1952807).sum := by decide
  have hdescent : baseEnd_1952807 < baseStart_1952807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952822 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1952822 : Nat := 118140960795 + 1952822 * 2 ^ 59
def prefixEnd_1952822 : Nat := 4983230072969 + 3 ^ 40 * 1952822 * 2
def baseEnd_1952822 : Nat := 668490879116309205762761

theorem tailTrace_1952822 : CollatzResearch.WordTrace tailWord_1952822 prefixEnd_1952822 668490879116309205762761 := by
  unfold tailWord_1952822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4451579358204180268136795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47483513154177922860125813 4451579358204180268136795)
  ·
    refine ⟨6677369037306270402205193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4451579358204180268136795 6677369037306270402205193)
    ·
      refine ⟨5008026777979702801653895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6677369037306270402205193 5008026777979702801653895)
      ·
        refine ⟨7512040166969554202480843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5008026777979702801653895 7512040166969554202480843)
        ·
          refine ⟨11268060250454331303721265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7512040166969554202480843 11268060250454331303721265)
          ·
            refine ⟨8451045187840748477790949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11268060250454331303721265 8451045187840748477790949)
            ·
              refine ⟨1584570972720140339585803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8451045187840748477790949 1584570972720140339585803)
              ·
                refine ⟨2376856459080210509378705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584570972720140339585803 2376856459080210509378705)
                ·
                  refine ⟨1782642344310157882034029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2376856459080210509378705 1782642344310157882034029)
                  ·
                    refine ⟨668490879116309205762761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782642344310157882034029 668490879116309205762761)
                    ·
                      rfl

theorem cell22_1952822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1952822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952822 prefixEnd_1952822 := by exact prefixLift 1952822
  have htrace : WordTrace (prefixWord ++ tailWord_1952822) baseStart_1952822 baseEnd_1952822 := by
    simpa [prefixWord, tailWord_1952822, baseEnd_1952822] using wordTrace_append hprefix tailTrace_1952822
  have hstable : (prefixWord ++ tailWord_1952822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952822).length < 2 ^ (prefixWord ++ tailWord_1952822).sum := by decide
  have hdescent : baseEnd_1952822 < baseStart_1952822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952876 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_1952876 : Nat := 118140960795 + 1952876 * 2 ^ 59
def prefixEnd_1952876 : Nat := 4983230072969 + 3 ^ 40 * 1952876 * 2
def baseEnd_1952876 : Nat := 668509364419871064912595

theorem tailTrace_1952876 : CollatzResearch.WordTrace tailWord_1952876 prefixEnd_1952876 668509364419871064912595 := by
  unfold tailWord_1952876
  simp only [CollatzResearch.WordTrace]
  refine ⟨35613619636535625756327241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47484826182047501008436321 35613619636535625756327241)
  ·
    refine ⟨26710214727401719317245431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35613619636535625756327241 26710214727401719317245431)
    ·
      refine ⟨40065322091102578975868147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26710214727401719317245431 40065322091102578975868147)
      ·
        refine ⟨60097983136653868463802221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40065322091102578975868147 60097983136653868463802221)
        ·
          refine ⟨22536743676245200673925833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60097983136653868463802221 22536743676245200673925833)
          ·
            refine ⟨16902557757183900505444375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22536743676245200673925833 16902557757183900505444375)
            ·
              refine ⟨25353836635775850758166563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16902557757183900505444375 25353836635775850758166563)
              ·
                refine ⟨38030754953663776137249845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25353836635775850758166563 38030754953663776137249845)
                ·
                  refine ⟨3565383276905979012867173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38030754953663776137249845 3565383276905979012867173)
                  ·
                    refine ⟨668509364419871064912595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3565383276905979012867173 668509364419871064912595)
                    ·
                      rfl

theorem cell22_1952876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_1952876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952876 prefixEnd_1952876 := by exact prefixLift 1952876
  have htrace : WordTrace (prefixWord ++ tailWord_1952876) baseStart_1952876 baseEnd_1952876 := by
    simpa [prefixWord, tailWord_1952876, baseEnd_1952876] using wordTrace_append hprefix tailTrace_1952876
  have hstable : (prefixWord ++ tailWord_1952876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952876).length < 2 ^ (prefixWord ++ tailWord_1952876).sum := by decide
  have hdescent : baseEnd_1952876 < baseStart_1952876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952878 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1952878 : Nat := 118140960795 + 1952878 * 2 ^ 59
def prefixEnd_1952878 : Nat := 4983230072969 + 3 ^ 40 * 1952878 * 2
def baseEnd_1952878 : Nat := 668510049060743726362589

theorem tailTrace_1952878 : CollatzResearch.WordTrace tailWord_1952878 prefixEnd_1952878 668510049060743726362589 := by
  unfold tailWord_1952878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903414027383000731778411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47484874812709337236151525 8903414027383000731778411)
  ·
    refine ⟨13355121041074501097667617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8903414027383000731778411 13355121041074501097667617)
    ·
      refine ⟨10016340780805875823250713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13355121041074501097667617 10016340780805875823250713)
      ·
        refine ⟨7512255585604406867438035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10016340780805875823250713 7512255585604406867438035)
        ·
          refine ⟨11268383378406610301157053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7512255585604406867438035 11268383378406610301157053)
          ·
            refine ⟨4225643766902478862933895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11268383378406610301157053 4225643766902478862933895)
            ·
              refine ⟨6338465650353718294400843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225643766902478862933895 6338465650353718294400843)
              ·
                refine ⟨9507698475530577441601265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6338465650353718294400843 9507698475530577441601265)
                ·
                  refine ⟨7130773856647933081200949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9507698475530577441601265 7130773856647933081200949)
                  ·
                    refine ⟨668510049060743726362589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7130773856647933081200949 668510049060743726362589)
                    ·
                      rfl

theorem cell22_1952878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1952878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952878 prefixEnd_1952878 := by exact prefixLift 1952878
  have htrace : WordTrace (prefixWord ++ tailWord_1952878) baseStart_1952878 baseEnd_1952878 := by
    simpa [prefixWord, tailWord_1952878, baseEnd_1952878] using wordTrace_append hprefix tailTrace_1952878
  have hstable : (prefixWord ++ tailWord_1952878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952878).length < 2 ^ (prefixWord ++ tailWord_1952878).sum := by decide
  have hdescent : baseEnd_1952878 < baseStart_1952878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952893 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_1952893 : Nat := 118140960795 + 1952893 * 2 ^ 59
def prefixEnd_1952893 : Nat := 4983230072969 + 3 ^ 40 * 1952893 * 2
def baseEnd_1952893 : Nat := 668515183867288687237543

theorem tailTrace_1952893 : CollatzResearch.WordTrace tailWord_1952893 prefixEnd_1952893 668515183867288687237543 := by
  unfold tailWord_1952893
  simp only [CollatzResearch.WordTrace]
  refine ⟨71227859314009663416023333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47485239542673108944015555 71227859314009663416023333)
  ·
    refine ⟨13355223621376811890504375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71227859314009663416023333 13355223621376811890504375)
    ·
      refine ⟨20032835432065217835756563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13355223621376811890504375 20032835432065217835756563)
      ·
        refine ⟨30049253148097826753634845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20032835432065217835756563 30049253148097826753634845)
        ·
          refine ⟨11268469930536685032613067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30049253148097826753634845 11268469930536685032613067)
          ·
            refine ⟨16902704895805027548919601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11268469930536685032613067 16902704895805027548919601)
            ·
              refine ⟨12677028671853770661689701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16902704895805027548919601 12677028671853770661689701)
              ·
                refine ⟨2376942875972581999066819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12677028671853770661689701 2376942875972581999066819)
                ·
                  refine ⟨3565414313958872998600229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376942875972581999066819 3565414313958872998600229)
                  ·
                    refine ⟨668515183867288687237543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3565414313958872998600229 668515183867288687237543)
                    ·
                      rfl

theorem cell22_1952893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_1952893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952893 prefixEnd_1952893 := by exact prefixLift 1952893
  have htrace : WordTrace (prefixWord ++ tailWord_1952893) baseStart_1952893 baseEnd_1952893 := by
    simpa [prefixWord, tailWord_1952893, baseEnd_1952893] using wordTrace_append hprefix tailTrace_1952893
  have hstable : (prefixWord ++ tailWord_1952893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952893).length < 2 ^ (prefixWord ++ tailWord_1952893).sum := by decide
  have hdescent : baseEnd_1952893 < baseStart_1952893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952910 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_1952910 : Nat := 118140960795 + 1952910 * 2 ^ 59
def prefixEnd_1952910 : Nat := 4983230072969 + 3 ^ 40 * 1952910 * 2
def baseEnd_1952910 : Nat := 668521003314706309562491

theorem tailTrace_1952910 : CollatzResearch.WordTrace tailWord_1952910 prefixEnd_1952910 668521003314706309562491 := by
  unfold tailWord_1952910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903559919368509414924023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47485652903298716879594789 8903559919368509414924023)
  ·
    refine ⟨13355339879052764122386035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8903559919368509414924023 13355339879052764122386035)
    ·
      refine ⟨20033009818579146183579053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13355339879052764122386035 20033009818579146183579053)
      ·
        refine ⟨7512378681967179818842145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20033009818579146183579053 7512378681967179818842145)
        ·
          refine ⟨5634284011475384864131609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7512378681967179818842145 5634284011475384864131609)
          ·
            refine ⟨4225713008606538648098707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5634284011475384864131609 4225713008606538648098707)
            ·
              refine ⟨6338569512909807972148061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225713008606538648098707 6338569512909807972148061)
              ·
                refine ⟨2376963567341177989555523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6338569512909807972148061 2376963567341177989555523)
                ·
                  refine ⟨3565445351011766984333285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376963567341177989555523 3565445351011766984333285)
                  ·
                    refine ⟨668521003314706309562491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3565445351011766984333285 668521003314706309562491)
                    ·
                      rfl

theorem cell22_1952910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_1952910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952910 prefixEnd_1952910 := by exact prefixLift 1952910
  have htrace : WordTrace (prefixWord ++ tailWord_1952910) baseStart_1952910 baseEnd_1952910 := by
    simpa [prefixWord, tailWord_1952910, baseEnd_1952910] using wordTrace_append hprefix tailTrace_1952910
  have hstable : (prefixWord ++ tailWord_1952910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952910).length < 2 ^ (prefixWord ++ tailWord_1952910).sum := by decide
  have hdescent : baseEnd_1952910 < baseStart_1952910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952951 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 2, 7]
def baseStart_1952951 : Nat := 118140960795 + 1952951 * 2 ^ 59
def prefixEnd_1952951 : Nat := 4983230072969 + 3 ^ 40 * 1952951 * 2
def baseEnd_1952951 : Nat := 668535038452595869287365

theorem tailTrace_1952951 : CollatzResearch.WordTrace tailWord_1952951 prefixEnd_1952951 668535038452595869287365 := by
  unfold tailWord_1952951
  simp only [CollatzResearch.WordTrace]
  refine ⟨71229974747799539321634707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47486649831866359547756471 71229974747799539321634707)
  ·
    refine ⟨106844962121699308982452061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71229974747799539321634707 106844962121699308982452061)
    ·
      refine ⟨40066860795637240868419523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106844962121699308982452061 40066860795637240868419523)
      ·
        refine ⟨60100291193455861302629285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40066860795637240868419523 60100291193455861302629285)
        ·
          refine ⟨11268804598772973994242991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60100291193455861302629285 11268804598772973994242991)
          ·
            refine ⟨16903206898159460991364487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11268804598772973994242991 16903206898159460991364487)
            ·
              refine ⟨25354810347239191487046731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16903206898159460991364487 25354810347239191487046731)
              ·
                refine ⟨38032215520858787230570097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25354810347239191487046731 38032215520858787230570097)
                ·
                  refine ⟨28524161640644090422927573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38032215520858787230570097 28524161640644090422927573)
                  ·
                    refine ⟨668535038452595869287365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28524161640644090422927573 668535038452595869287365)
                    ·
                      rfl

theorem cell22_1952951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_1952951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952951 prefixEnd_1952951 := by exact prefixLift 1952951
  have htrace : WordTrace (prefixWord ++ tailWord_1952951) baseStart_1952951 baseEnd_1952951 := by
    simpa [prefixWord, tailWord_1952951, baseEnd_1952951] using wordTrace_append hprefix tailTrace_1952951
  have hstable : (prefixWord ++ tailWord_1952951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952951).length < 2 ^ (prefixWord ++ tailWord_1952951).sum := by decide
  have hdescent : baseEnd_1952951 < baseStart_1952951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952953 : List Nat := [1, 2, 1, 4, 1, 3, 4, 6]
def baseStart_1952953 : Nat := 118140960795 + 1952953 * 2 ^ 59
def prefixEnd_1952953 : Nat := 4983230072969 + 3 ^ 40 * 1952953 * 2
def baseEnd_1952953 : Nat := 74281747010385392304151

theorem tailTrace_1952953 : CollatzResearch.WordTrace tailWord_1952953 prefixEnd_1952953 74281747010385392304151 := by
  unfold tailWord_1952953
  simp only [CollatzResearch.WordTrace]
  refine ⟨71230047693792293663207513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47486698462528195775471675 71230047693792293663207513)
  ·
    refine ⟨53422535770344220247405635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71230047693792293663207513 53422535770344220247405635)
    ·
      refine ⟨80133803655516330371108453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53422535770344220247405635 80133803655516330371108453)
      ·
        refine ⟨15025088185409311944582835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80133803655516330371108453 15025088185409311944582835)
        ·
          refine ⟨22537632278113967916874253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15025088185409311944582835 22537632278113967916874253)
          ·
            refine ⟨8451612104292737968827845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22537632278113967916874253 8451612104292737968827845)
            ·
              refine ⟨1584677269554888369155221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8451612104292737968827845 1584677269554888369155221)
              ·
                refine ⟨74281747010385392304151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1584677269554888369155221 74281747010385392304151)
                ·
                  rfl

theorem cell22_1952953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 6].length) (baseStart_1952953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952953 prefixEnd_1952953 := by exact prefixLift 1952953
  have htrace : WordTrace (prefixWord ++ tailWord_1952953) baseStart_1952953 baseEnd_1952953 := by
    simpa [prefixWord, tailWord_1952953, baseEnd_1952953] using wordTrace_append hprefix tailTrace_1952953
  have hstable : (prefixWord ++ tailWord_1952953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952953).length < 2 ^ (prefixWord ++ tailWord_1952953).sum := by decide
  have hdescent : baseEnd_1952953 < baseStart_1952953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952968 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 5, 3]
def baseStart_1952968 : Nat := 118140960795 + 1952968 * 2 ^ 59
def prefixEnd_1952968 : Nat := 4983230072969 + 3 ^ 40 * 1952968 * 2
def baseEnd_1952968 : Nat := 668540857900013491612313

theorem tailTrace_1952968 : CollatzResearch.WordTrace tailWord_1952968 prefixEnd_1952968 668540857900013491612313 := by
  unfold tailWord_1952968
  simp only [CollatzResearch.WordTrace]
  refine ⟨35615297394368975612501779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47487063192491967483335705 35615297394368975612501779)
  ·
    refine ⟨53422946091553463418752669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35615297394368975612501779 53422946091553463418752669)
    ·
      refine ⟨20033604784332548782032251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53422946091553463418752669 20033604784332548782032251)
      ·
        refine ⟨30050407176498823173048377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20033604784332548782032251 30050407176498823173048377)
        ·
          refine ⟨22537805382374117379786283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30050407176498823173048377 22537805382374117379786283)
          ·
            refine ⟨33806708073561176069679425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22537805382374117379786283 33806708073561176069679425)
            ·
              refine ⟨25355031055170882052259569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33806708073561176069679425 25355031055170882052259569)
              ·
                refine ⟨19016273291378161539194677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25355031055170882052259569 19016273291378161539194677)
                ·
                  refine ⟨1782775621066702644299501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19016273291378161539194677 1782775621066702644299501)
                  ·
                    refine ⟨668540857900013491612313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782775621066702644299501 668540857900013491612313)
                    ·
                      rfl

theorem cell22_1952968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_1952968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952968 prefixEnd_1952968 := by exact prefixLift 1952968
  have htrace : WordTrace (prefixWord ++ tailWord_1952968) baseStart_1952968 baseEnd_1952968 := by
    simpa [prefixWord, tailWord_1952968, baseEnd_1952968] using wordTrace_append hprefix tailTrace_1952968
  have hstable : (prefixWord ++ tailWord_1952968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952968).length < 2 ^ (prefixWord ++ tailWord_1952968).sum := by decide
  have hdescent : baseEnd_1952968 < baseStart_1952968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953077 : List Nat := [1, 3, 3, 1, 2, 3, 2, 3, 4]
def baseStart_1953077 : Nat := 118140960795 + 1953077 * 2 ^ 59
def prefixEnd_1953077 : Nat := 4983230072969 + 3 ^ 40 * 1953077 * 2
def baseEnd_1953077 : Nat := 222859390275857846878993

theorem tailTrace_1953077 : CollatzResearch.WordTrace tailWord_1953077 prefixEnd_1953077 222859390275857846878993 := by
  unfold tailWord_1953077
  simp only [CollatzResearch.WordTrace]
  refine ⟨71234570345343062840721485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47489713563562041893814323 71234570345343062840721485)
  ·
    refine ⟨26712963879503648565270557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71234570345343062840721485 26712963879503648565270557)
    ·
      refine ⟨10017361454813868211976459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26712963879503648565270557 10017361454813868211976459)
      ·
        refine ⟨15026042182220802317964689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017361454813868211976459 15026042182220802317964689)
        ·
          refine ⟨11269531636665601738473517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15026042182220802317964689 11269531636665601738473517)
          ·
            refine ⟨4226074363749600651927569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11269531636665601738473517 4226074363749600651927569)
            ·
              refine ⟨3169555772812200488945677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4226074363749600651927569 3169555772812200488945677)
              ·
                refine ⟨1188583414804575183354629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3169555772812200488945677 1188583414804575183354629)
                ·
                  refine ⟨222859390275857846878993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188583414804575183354629 222859390275857846878993)
                  ·
                    rfl

theorem cell22_1953077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_1953077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953077 prefixEnd_1953077 := by exact prefixLift 1953077
  have htrace : WordTrace (prefixWord ++ tailWord_1953077) baseStart_1953077 baseEnd_1953077 := by
    simpa [prefixWord, tailWord_1953077, baseEnd_1953077] using wordTrace_append hprefix tailTrace_1953077
  have hstable : (prefixWord ++ tailWord_1953077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953077).length < 2 ^ (prefixWord ++ tailWord_1953077).sum := by decide
  have hdescent : baseEnd_1953077 < baseStart_1953077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953109 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 2, 3]
def baseStart_1953109 : Nat := 118140960795 + 1953109 * 2 ^ 59
def prefixEnd_1953109 : Nat := 4983230072969 + 3 ^ 40 * 1953109 * 2
def baseEnd_1953109 : Nat := 668589125081536123836881

theorem tailTrace_1953109 : CollatzResearch.WordTrace tailWord_1953109 prefixEnd_1953109 668589125081536123836881 := by
  unfold tailWord_1953109
  simp only [CollatzResearch.WordTrace]
  refine ⟨71235737481227132305886381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47490491654151421537257587 71235737481227132305886381)
  ·
    refine ⟨26713401555460174614707393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71235737481227132305886381 26713401555460174614707393)
    ·
      refine ⟨20035051166595130961030545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26713401555460174614707393 20035051166595130961030545)
      ·
        refine ⟨15026288374946348220772909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20035051166595130961030545 15026288374946348220772909)
        ·
          refine ⟨5634858140604880582789841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15026288374946348220772909 5634858140604880582789841)
          ·
            refine ⟨4226143605453660437092381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5634858140604880582789841 4226143605453660437092381)
            ·
              refine ⟨1584803852045122663909643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4226143605453660437092381 1584803852045122663909643)
              ·
                refine ⟨2377205778067683995864465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584803852045122663909643 2377205778067683995864465)
                ·
                  refine ⟨1782904333550762996898349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2377205778067683995864465 1782904333550762996898349)
                  ·
                    refine ⟨668589125081536123836881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782904333550762996898349 668589125081536123836881)
                    ·
                      rfl

theorem cell22_1953109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_1953109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953109 prefixEnd_1953109 := by exact prefixLift 1953109
  have htrace : WordTrace (prefixWord ++ tailWord_1953109) baseStart_1953109 baseEnd_1953109 := by
    simpa [prefixWord, tailWord_1953109, baseEnd_1953109] using wordTrace_append hprefix tailTrace_1953109
  have hstable : (prefixWord ++ tailWord_1953109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953109).length < 2 ^ (prefixWord ++ tailWord_1953109).sum := by decide
  have hdescent : baseEnd_1953109 < baseStart_1953109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953227 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 2, 3]
def baseStart_1953227 : Nat := 118140960795 + 1953227 * 2 ^ 59
def prefixEnd_1953227 : Nat := 4983230072969 + 3 ^ 40 * 1953227 * 2
def baseEnd_1953227 : Nat := 668629518893023149386519

theorem tailTrace_1953227 : CollatzResearch.WordTrace tailWord_1953227 prefixEnd_1953227 668629518893023149386519 := by
  unfold tailWord_1953227
  simp only [CollatzResearch.WordTrace]
  refine ⟨71240041294799638458681935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47493360863199758972454623 71240041294799638458681935)
  ·
    refine ⟨106860061942199457688022903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71240041294799638458681935 106860061942199457688022903)
    ·
      refine ⟨160290092913299186532034355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106860061942199457688022903 160290092913299186532034355)
      ·
        refine ⟨240435139369948779798051533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160290092913299186532034355 240435139369948779798051533)
        ·
          refine ⟨90163177263730792424269325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240435139369948779798051533 90163177263730792424269325)
          ·
            refine ⟨33811191473899047159100997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90163177263730792424269325 33811191473899047159100997)
            ·
              refine ⟨6339598401356071342331437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33811191473899047159100997 6339598401356071342331437)
              ·
                refine ⟨2377349400508526753374289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6339598401356071342331437 2377349400508526753374289)
                ·
                  refine ⟨1783012050381395065030717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2377349400508526753374289 1783012050381395065030717)
                  ·
                    refine ⟨668629518893023149386519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783012050381395065030717 668629518893023149386519)
                    ·
                      rfl

theorem cell22_1953227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 3].length) (baseStart_1953227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953227 prefixEnd_1953227 := by exact prefixLift 1953227
  have htrace : WordTrace (prefixWord ++ tailWord_1953227) baseStart_1953227 baseEnd_1953227 := by
    simpa [prefixWord, tailWord_1953227, baseEnd_1953227] using wordTrace_append hprefix tailTrace_1953227
  have hstable : (prefixWord ++ tailWord_1953227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953227).length < 2 ^ (prefixWord ++ tailWord_1953227).sum := by decide
  have hdescent : baseEnd_1953227 < baseStart_1953227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953242 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_1953242 : Nat := 118140960795 + 1953242 * 2 ^ 59
def prefixEnd_1953242 : Nat := 4983230072969 + 3 ^ 40 * 1953242 * 2
def baseEnd_1953242 : Nat := 668634653699568110261473

theorem tailTrace_1953242 : CollatzResearch.WordTrace tailWord_1953242 prefixEnd_1953242 668634653699568110261473 := by
  unfold tailWord_1953242
  simp only [CollatzResearch.WordTrace]
  refine ⟨17810147097436324005119495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47493725593163530680318653 17810147097436324005119495)
  ·
    refine ⟨26715220646154486007679243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17810147097436324005119495 26715220646154486007679243)
    ·
      refine ⟨40072830969231729011518865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26715220646154486007679243 40072830969231729011518865)
      ·
        refine ⟨30054623226923796758639149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40072830969231729011518865 30054623226923796758639149)
        ·
          refine ⟨11270483710096423784489681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30054623226923796758639149 11270483710096423784489681)
          ·
            refine ⟨8452862782572317838367261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11270483710096423784489681 8452862782572317838367261)
            ·
              refine ⟨3169823543464619189387723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8452862782572317838367261 3169823543464619189387723)
              ·
                refine ⟨4754735315196928784081585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169823543464619189387723 4754735315196928784081585)
                ·
                  refine ⟨3566051486397696588061189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4754735315196928784081585 3566051486397696588061189)
                  ·
                    refine ⟨668634653699568110261473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3566051486397696588061189 668634653699568110261473)
                    ·
                      rfl

theorem cell22_1953242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_1953242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953242 prefixEnd_1953242 := by exact prefixLift 1953242
  have htrace : WordTrace (prefixWord ++ tailWord_1953242) baseStart_1953242 baseEnd_1953242 := by
    simpa [prefixWord, tailWord_1953242, baseEnd_1953242] using wordTrace_append hprefix tailTrace_1953242
  have hstable : (prefixWord ++ tailWord_1953242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953242).length < 2 ^ (prefixWord ++ tailWord_1953242).sum := by decide
  have hdescent : baseEnd_1953242 < baseStart_1953242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953272 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 3, 3]
def baseStart_1953272 : Nat := 118140960795 + 1953272 * 2 ^ 59
def prefixEnd_1953272 : Nat := 4983230072969 + 3 ^ 40 * 1953272 * 2
def baseEnd_1953272 : Nat := 668644923312658032011381

theorem tailTrace_1953272 : CollatzResearch.WordTrace tailWord_1953272 prefixEnd_1953272 668644923312658032011381 := by
  unfold tailWord_1953272
  simp only [CollatzResearch.WordTrace]
  refine ⟨35620841289818305572035035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47494455053091074096046713 35620841289818305572035035)
  ·
    refine ⟨53431261934727458358052553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35620841289818305572035035 53431261934727458358052553)
    ·
      refine ⟨40073446451045593768539415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53431261934727458358052553 40073446451045593768539415)
      ·
        refine ⟨60110169676568390652809123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40073446451045593768539415 60110169676568390652809123)
        ·
          refine ⟨90165254514852585979213685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60110169676568390652809123 90165254514852585979213685)
          ·
            refine ⟨8452992610767429935551283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90165254514852585979213685 8452992610767429935551283)
            ·
              refine ⟨12679488916151144903326925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452992610767429935551283 12679488916151144903326925)
              ·
                refine ⟨4754808343556679338747597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12679488916151144903326925 4754808343556679338747597)
                ·
                  refine ⟨1783053128833754752030349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4754808343556679338747597 1783053128833754752030349)
                  ·
                    refine ⟨668644923312658032011381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783053128833754752030349 668644923312658032011381)
                    ·
                      rfl

theorem cell22_1953272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_1953272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953272 prefixEnd_1953272 := by exact prefixLift 1953272
  have htrace : WordTrace (prefixWord ++ tailWord_1953272) baseStart_1953272 baseEnd_1953272 := by
    simpa [prefixWord, tailWord_1953272, baseEnd_1953272] using wordTrace_append hprefix tailTrace_1953272
  have hstable : (prefixWord ++ tailWord_1953272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953272).length < 2 ^ (prefixWord ++ tailWord_1953272).sum := by decide
  have hdescent : baseEnd_1953272 < baseStart_1953272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953278 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1953278 : Nat := 118140960795 + 1953278 * 2 ^ 59
def prefixEnd_1953278 : Nat := 4983230072969 + 3 ^ 40 * 1953278 * 2
def baseEnd_1953278 : Nat := 668646977235276016361363

theorem tailTrace_1953278 : CollatzResearch.WordTrace tailWord_1953278 prefixEnd_1953278 668646977235276016361363 := by
  unfold tailWord_1953278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8905237677201859271098561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47494600945076582779192325 8905237677201859271098561)
  ·
    refine ⟨6678928257901394453323921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8905237677201859271098561 6678928257901394453323921)
    ·
      refine ⟨5009196193426045839992941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6678928257901394453323921 5009196193426045839992941)
      ·
        refine ⟨1878448572534767189997353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5009196193426045839992941 1878448572534767189997353)
        ·
          refine ⟨1408836429401075392498015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1878448572534767189997353 1408836429401075392498015)
          ·
            refine ⟨2113254644101613088747023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408836429401075392498015 2113254644101613088747023)
            ·
              refine ⟨3169881966152419633120535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113254644101613088747023 3169881966152419633120535)
              ·
                refine ⟨4754822949228629449680803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169881966152419633120535 4754822949228629449680803)
                ·
                  refine ⟨7132234423842944174521205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754822949228629449680803 7132234423842944174521205)
                  ·
                    refine ⟨668646977235276016361363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7132234423842944174521205 668646977235276016361363)
                    ·
                      rfl

theorem cell22_1953278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1953278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953278 prefixEnd_1953278 := by exact prefixLift 1953278
  have htrace : WordTrace (prefixWord ++ tailWord_1953278) baseStart_1953278 baseEnd_1953278 := by
    simpa [prefixWord, tailWord_1953278, baseEnd_1953278] using wordTrace_append hprefix tailTrace_1953278
  have hstable : (prefixWord ++ tailWord_1953278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953278).length < 2 ^ (prefixWord ++ tailWord_1953278).sum := by decide
  have hdescent : baseEnd_1953278 < baseStart_1953278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953362 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1953362 : Nat := 118140960795 + 1953362 * 2 ^ 59
def prefixEnd_1953362 : Nat := 4983230072969 + 3 ^ 40 * 1953362 * 2
def baseEnd_1953362 : Nat := 668675732151927797261105

theorem tailTrace_1953362 : CollatzResearch.WordTrace tailWord_1953362 prefixEnd_1953362 668675732151927797261105 := by
  unfold tailWord_1953362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17811241287327639128711585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47496643432873704343230893 17811241287327639128711585)
  ·
    refine ⟨13358430965495729346533689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17811241287327639128711585 13358430965495729346533689)
    ·
      refine ⟨10018823224121797009900267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13358430965495729346533689 10018823224121797009900267)
      ·
        refine ⟨15028234836182695514850401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10018823224121797009900267 15028234836182695514850401)
        ·
          refine ⟨11271176127137021636137801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15028234836182695514850401 11271176127137021636137801)
          ·
            refine ⟨8453382095352766227103351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11271176127137021636137801 8453382095352766227103351)
            ·
              refine ⟨12680073143029149340655027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8453382095352766227103351 12680073143029149340655027)
              ·
                refine ⟨19020109714543724010982541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12680073143029149340655027 19020109714543724010982541)
                ·
                  refine ⟨7132541142953896504118453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19020109714543724010982541 7132541142953896504118453)
                  ·
                    refine ⟨668675732151927797261105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7132541142953896504118453 668675732151927797261105)
                    ·
                      rfl

theorem cell22_1953362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1953362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953362 prefixEnd_1953362 := by exact prefixLift 1953362
  have htrace : WordTrace (prefixWord ++ tailWord_1953362) baseStart_1953362 baseEnd_1953362 := by
    simpa [prefixWord, tailWord_1953362, baseEnd_1953362] using wordTrace_append hprefix tailTrace_1953362
  have hstable : (prefixWord ++ tailWord_1953362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953362).length < 2 ^ (prefixWord ++ tailWord_1953362).sum := by decide
  have hdescent : baseEnd_1953362 < baseStart_1953362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953364 : List Nat := [2, 4, 1, 1, 1, 2, 2, 5, 4]
def baseStart_1953364 : Nat := 118140960795 + 1953364 * 2 ^ 59
def prefixEnd_1953364 : Nat := 4983230072969 + 3 ^ 40 * 1953364 * 2
def baseEnd_1953364 : Nat := 222892138930933486237033

theorem tailTrace_1953364 : CollatzResearch.WordTrace tailWord_1953364 prefixEnd_1953364 222892138930933486237033 := by
  unfold tailWord_1953364
  simp only [CollatzResearch.WordTrace]
  refine ⟨35622519047651655428209573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47496692063535540570946097 35622519047651655428209573)
  ·
    refine ⟨6679222321434685392789295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35622519047651655428209573 6679222321434685392789295)
    ·
      refine ⟨10018833482152028089183943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6679222321434685392789295 10018833482152028089183943)
      ·
        refine ⟨15028250223228042133775915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10018833482152028089183943 15028250223228042133775915)
        ·
          refine ⟨22542375334842063200663873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15028250223228042133775915 22542375334842063200663873)
          ·
            refine ⟨16906781501131547400497905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22542375334842063200663873 16906781501131547400497905)
            ·
              refine ⟨12680086125848660550373429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16906781501131547400497905 12680086125848660550373429)
              ·
                refine ⟨1188758074298311926597509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12680086125848660550373429 1188758074298311926597509)
                ·
                  refine ⟨222892138930933486237033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188758074298311926597509 222892138930933486237033)
                  ·
                    rfl

theorem cell22_1953364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_1953364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953364 prefixEnd_1953364 := by exact prefixLift 1953364
  have htrace : WordTrace (prefixWord ++ tailWord_1953364) baseStart_1953364 baseEnd_1953364 := by
    simpa [prefixWord, tailWord_1953364, baseEnd_1953364] using wordTrace_append hprefix tailTrace_1953364
  have hstable : (prefixWord ++ tailWord_1953364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953364).length < 2 ^ (prefixWord ++ tailWord_1953364).sum := by decide
  have hdescent : baseEnd_1953364 < baseStart_1953364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953377 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1953377 : Nat := 118140960795 + 1953377 * 2 ^ 59
def prefixEnd_1953377 : Nat := 4983230072969 + 3 ^ 40 * 1953377 * 2
def baseEnd_1953377 : Nat := 668680866958472758136059

theorem tailTrace_1953377 : CollatzResearch.WordTrace tailWord_1953377 prefixEnd_1953377 668680866958472758136059 := by
  unfold tailWord_1953377
  simp only [CollatzResearch.WordTrace]
  refine ⟨71245512244256214076642385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47497008162837476051094923 71245512244256214076642385)
  ·
    refine ⟨53434134183192160557481789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71245512244256214076642385 53434134183192160557481789)
    ·
      refine ⟨20037800318697060209055671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53434134183192160557481789 20037800318697060209055671)
      ·
        refine ⟨30056700478045590313583507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20037800318697060209055671 30056700478045590313583507)
        ·
          refine ⟨45085050717068385470375261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30056700478045590313583507 45085050717068385470375261)
          ·
            refine ⟨16906894018900644551390723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45085050717068385470375261 16906894018900644551390723)
            ·
              refine ⟨25360341028350966827086085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16906894018900644551390723 25360341028350966827086085)
              ·
                refine ⟨4755063942815806280078641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25360341028350966827086085 4755063942815806280078641)
                ·
                  refine ⟨3566297957111854710058981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4755063942815806280078641 3566297957111854710058981)
                  ·
                    refine ⟨668680866958472758136059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3566297957111854710058981 668680866958472758136059)
                    ·
                      rfl

theorem cell22_1953377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1953377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953377 prefixEnd_1953377 := by exact prefixLift 1953377
  have htrace : WordTrace (prefixWord ++ tailWord_1953377) baseStart_1953377 baseEnd_1953377 := by
    simpa [prefixWord, tailWord_1953377, baseEnd_1953377] using wordTrace_append hprefix tailTrace_1953377
  have hstable : (prefixWord ++ tailWord_1953377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953377).length < 2 ^ (prefixWord ++ tailWord_1953377).sum := by decide
  have hdescent : baseEnd_1953377 < baseStart_1953377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953379 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 2, 3]
def baseStart_1953379 : Nat := 118140960795 + 1953379 * 2 ^ 59
def prefixEnd_1953379 : Nat := 4983230072969 + 3 ^ 40 * 1953379 * 2
def baseEnd_1953379 : Nat := 668681551599345419586053

theorem tailTrace_1953379 : CollatzResearch.WordTrace tailWord_1953379 prefixEnd_1953379 668681551599345419586053 := by
  unfold tailWord_1953379
  simp only [CollatzResearch.WordTrace]
  refine ⟨71245585190248968418215191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47497056793499312278810127 71245585190248968418215191)
  ·
    refine ⟨106868377785373452627322787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71245585190248968418215191 106868377785373452627322787)
    ·
      refine ⟨160302566678060178940984181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106868377785373452627322787 160302566678060178940984181)
      ·
        refine ⟨15028365626068141775717267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160302566678060178940984181 15028365626068141775717267)
        ·
          refine ⟨22542548439102212663575901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15028365626068141775717267 22542548439102212663575901)
          ·
            refine ⟨8453455664663329748840963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22542548439102212663575901 8453455664663329748840963)
            ·
              refine ⟨12680183496994994623261445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8453455664663329748840963 12680183496994994623261445)
              ·
                refine ⟨2377534405686561491861521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12680183496994994623261445 2377534405686561491861521)
                ·
                  refine ⟨1783150804264921118896141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2377534405686561491861521 1783150804264921118896141)
                  ·
                    refine ⟨668681551599345419586053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783150804264921118896141 668681551599345419586053)
                    ·
                      rfl

theorem cell22_1953379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 3].length) (baseStart_1953379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953379 prefixEnd_1953379 := by exact prefixLift 1953379
  have htrace : WordTrace (prefixWord ++ tailWord_1953379) baseStart_1953379 baseEnd_1953379 := by
    simpa [prefixWord, tailWord_1953379, baseEnd_1953379] using wordTrace_append hprefix tailTrace_1953379
  have hstable : (prefixWord ++ tailWord_1953379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953379).length < 2 ^ (prefixWord ++ tailWord_1953379).sum := by decide
  have hdescent : baseEnd_1953379 < baseStart_1953379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953381 : List Nat := [1, 3, 1, 3, 3, 1, 4, 2, 4]
def baseStart_1953381 : Nat := 118140960795 + 1953381 * 2 ^ 59
def prefixEnd_1953381 : Nat := 4983230072969 + 3 ^ 40 * 1953381 * 2
def baseEnd_1953381 : Nat := 222894078746739360345349

theorem tailTrace_1953381 : CollatzResearch.WordTrace tailWord_1953381 prefixEnd_1953381 222894078746739360345349 := by
  unfold tailWord_1953381
  simp only [CollatzResearch.WordTrace]
  refine ⟨71245658136241722759787997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47497105424161148506525331 71245658136241722759787997)
  ·
    refine ⟨26717121801090646034920499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71245658136241722759787997 26717121801090646034920499)
    ·
      refine ⟨40075682701635969052380749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26717121801090646034920499 40075682701635969052380749)
      ·
        refine ⟨15028381013113488394642781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40075682701635969052380749 15028381013113488394642781)
        ·
          refine ⟨5635642879917558147991043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15028381013113488394642781 5635642879917558147991043)
          ·
            refine ⟨8453464319876337221986565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635642879917558147991043 8453464319876337221986565)
            ·
              refine ⟨1585024559976813229122481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8453464319876337221986565 1585024559976813229122481)
              ·
                refine ⟨1188768419982609921841861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585024559976813229122481 1188768419982609921841861)
                ·
                  refine ⟨222894078746739360345349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188768419982609921841861 222894078746739360345349)
                  ·
                    rfl

theorem cell22_1953381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_1953381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953381 prefixEnd_1953381 := by exact prefixLift 1953381
  have htrace : WordTrace (prefixWord ++ tailWord_1953381) baseStart_1953381 baseEnd_1953381 := by
    simpa [prefixWord, tailWord_1953381, baseEnd_1953381] using wordTrace_append hprefix tailTrace_1953381
  have hstable : (prefixWord ++ tailWord_1953381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953381).length < 2 ^ (prefixWord ++ tailWord_1953381).sum := by decide
  have hdescent : baseEnd_1953381 < baseStart_1953381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953392 : List Nat := [2, 1, 1, 1, 6, 1, 3, 7]
def baseStart_1953392 : Nat := 118140960795 + 1953392 * 2 ^ 59
def prefixEnd_1953392 : Nat := 4983230072969 + 3 ^ 40 * 1953392 * 2
def baseEnd_1953392 : Nat := 74298444640557524334557

theorem tailTrace_1953392 : CollatzResearch.WordTrace tailWord_1953392 prefixEnd_1953392 74298444640557524334557 := by
  unfold tailWord_1953392
  simp only [CollatzResearch.WordTrace]
  refine ⟨35623029669600935819219215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47497372892801247758958953 35623029669600935819219215)
  ·
    refine ⟨53434544504401403728828823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35623029669600935819219215 53434544504401403728828823)
    ·
      refine ⟨80151816756602105593243235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53434544504401403728828823 80151816756602105593243235)
      ·
        refine ⟨120227725134903158389864853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80151816756602105593243235 120227725134903158389864853)
        ·
          refine ⟨5635674615698585549524915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120227725134903158389864853 5635674615698585549524915)
          ·
            refine ⟨8453511923547878324287373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635674615698585549524915 8453511923547878324287373)
            ·
              refine ⟨3170066971330454371607765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8453511923547878324287373 3170066971330454371607765)
              ·
                refine ⟨74298444640557524334557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3170066971330454371607765 74298444640557524334557)
                ·
                  rfl

theorem cell22_1953392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 7].length) (baseStart_1953392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953392 prefixEnd_1953392 := by exact prefixLift 1953392
  have htrace : WordTrace (prefixWord ++ tailWord_1953392) baseStart_1953392 baseEnd_1953392 := by
    simpa [prefixWord, tailWord_1953392, baseEnd_1953392] using wordTrace_append hprefix tailTrace_1953392
  have hstable : (prefixWord ++ tailWord_1953392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953392).length < 2 ^ (prefixWord ++ tailWord_1953392).sum := by decide
  have hdescent : baseEnd_1953392 < baseStart_1953392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953409 : List Nat := [1, 2, 4, 2, 1, 3, 3, 6]
def baseStart_1953409 : Nat := 118140960795 + 1953409 * 2 ^ 59
def prefixEnd_1953409 : Nat := 4983230072969 + 3 ^ 40 * 1953409 * 2
def baseEnd_1953409 : Nat := 74299091245826149037329

theorem tailTrace_1953409 : CollatzResearch.WordTrace tailWord_1953409 prefixEnd_1953409 74299091245826149037329 := by
  unfold tailWord_1953409
  simp only [CollatzResearch.WordTrace]
  refine ⟨71246679380140283541807281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47497786253426855694538187 71246679380140283541807281)
  ·
    refine ⟨53435009535105212656355461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71246679380140283541807281 53435009535105212656355461)
    ·
      refine ⟨10019064287832227373066649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53435009535105212656355461 10019064287832227373066649)
      ·
        refine ⟨7514298215874170529799987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10019064287832227373066649 7514298215874170529799987)
        ·
          refine ⟨11271447323811255794699981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7514298215874170529799987 11271447323811255794699981)
          ·
            refine ⟨4226792746429220923012493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11271447323811255794699981 4226792746429220923012493)
            ·
              refine ⟨1585047279910957846129685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4226792746429220923012493 1585047279910957846129685)
              ·
                refine ⟨74299091245826149037329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1585047279910957846129685 74299091245826149037329)
                ·
                  rfl

theorem cell22_1953409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 6].length) (baseStart_1953409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953409 prefixEnd_1953409 := by exact prefixLift 1953409
  have htrace : WordTrace (prefixWord ++ tailWord_1953409) baseStart_1953409 baseEnd_1953409 := by
    simpa [prefixWord, tailWord_1953409, baseEnd_1953409] using wordTrace_append hprefix tailTrace_1953409
  have hstable : (prefixWord ++ tailWord_1953409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953409).length < 2 ^ (prefixWord ++ tailWord_1953409).sum := by decide
  have hdescent : baseEnd_1953409 < baseStart_1953409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953441 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 3, 3]
def baseStart_1953441 : Nat := 118140960795 + 1953441 * 2 ^ 59
def prefixEnd_1953441 : Nat := 4983230072969 + 3 ^ 40 * 1953441 * 2
def baseEnd_1953441 : Nat := 668702775466397924535863

theorem tailTrace_1953441 : CollatzResearch.WordTrace tailWord_1953441 prefixEnd_1953441 668702775466397924535863 := by
  unfold tailWord_1953441
  simp only [CollatzResearch.WordTrace]
  refine ⟨71247846516024353006972177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47498564344016235337981451 71247846516024353006972177)
  ·
    refine ⟨53435884887018264755229133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71247846516024353006972177 53435884887018264755229133)
    ·
      refine ⟨20038456832631849283210925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53435884887018264755229133 20038456832631849283210925)
      ·
        refine ⟨7514421312236943481204097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20038456832631849283210925 7514421312236943481204097)
        ·
          refine ⟨5635815984177707610903073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7514421312236943481204097 5635815984177707610903073)
          ·
            refine ⟨4226861988133280708177305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5635815984177707610903073 4226861988133280708177305)
            ·
              refine ⟨3170146491099960531132979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4226861988133280708177305 3170146491099960531132979)
              ·
                refine ⟨4755219736649940796699469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3170146491099960531132979 4755219736649940796699469)
                ·
                  refine ⟨1783207401243727798762301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4755219736649940796699469 1783207401243727798762301)
                  ·
                    refine ⟨668702775466397924535863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783207401243727798762301 668702775466397924535863)
                    ·
                      rfl

theorem cell22_1953441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_1953441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953441 prefixEnd_1953441 := by exact prefixLift 1953441
  have htrace : WordTrace (prefixWord ++ tailWord_1953441) baseStart_1953441 baseEnd_1953441 := by
    simpa [prefixWord, tailWord_1953441, baseEnd_1953441] using wordTrace_append hprefix tailTrace_1953441
  have hstable : (prefixWord ++ tailWord_1953441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953441).length < 2 ^ (prefixWord ++ tailWord_1953441).sum := by decide
  have hdescent : baseEnd_1953441 < baseStart_1953441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953467 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 3, 4]
def baseStart_1953467 : Nat := 118140960795 + 1953467 * 2 ^ 59
def prefixEnd_1953467 : Nat := 4983230072969 + 3 ^ 40 * 1953467 * 2
def baseEnd_1953467 : Nat := 668711675797742523385783

theorem tailTrace_1953467 : CollatzResearch.WordTrace tailWord_1953467 prefixEnd_1953467 668711675797742523385783 := by
  unfold tailWord_1953467
  simp only [CollatzResearch.WordTrace]
  refine ⟨71248794813930159447418655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47499196542620106298279103 71248794813930159447418655)
  ·
    refine ⟨106873192220895239171127983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71248794813930159447418655 106873192220895239171127983)
    ·
      refine ⟨160309788331342858756691975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106873192220895239171127983 160309788331342858756691975)
      ·
        refine ⟨240464682497014288135037963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160309788331342858756691975 240464682497014288135037963)
        ·
          refine ⟨360697023745521432202556945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240464682497014288135037963 360697023745521432202556945)
          ·
            refine ⟨270522767809141074151917709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360697023745521432202556945 270522767809141074151917709)
            ·
              refine ⟨101446037928427902806969141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270522767809141074151917709 101446037928427902806969141)
              ·
                refine ⟨9510566055790115888153357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101446037928427902806969141 9510566055790115888153357)
                ·
                  refine ⟨3566462270921293458057509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9510566055790115888153357 3566462270921293458057509)
                  ·
                    refine ⟨668711675797742523385783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3566462270921293458057509 668711675797742523385783)
                    ·
                      rfl

theorem cell22_1953467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 4].length) (baseStart_1953467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953467 prefixEnd_1953467 := by exact prefixLift 1953467
  have htrace : WordTrace (prefixWord ++ tailWord_1953467) baseStart_1953467 baseEnd_1953467 := by
    simpa [prefixWord, tailWord_1953467, baseEnd_1953467] using wordTrace_append hprefix tailTrace_1953467
  have hstable : (prefixWord ++ tailWord_1953467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953467).length < 2 ^ (prefixWord ++ tailWord_1953467).sum := by decide
  have hdescent : baseEnd_1953467 < baseStart_1953467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953527 : List Nat := [1, 1, 3, 1, 1, 1, 6, 8]
def baseStart_1953527 : Nat := 118140960795 + 1953527 * 2 ^ 59
def prefixEnd_1953527 : Nat := 4983230072969 + 3 ^ 40 * 1953527 * 2
def baseEnd_1953527 : Nat := 74303579447102485209511

theorem tailTrace_1953527 : CollatzResearch.WordTrace tailWord_1953527 prefixEnd_1953527 74303579447102485209511 := by
  unfold tailWord_1953527
  simp only [CollatzResearch.WordTrace]
  refine ⟨71250983193712789694602835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47500655462475193129735223 71250983193712789694602835)
  ·
    refine ⟨106876474790569184541904253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71250983193712789694602835 106876474790569184541904253)
    ·
      refine ⟨40078678046463444203214095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106876474790569184541904253 40078678046463444203214095)
      ·
        refine ⟨60118017069695166304821143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40078678046463444203214095 60118017069695166304821143)
        ·
          refine ⟨90177025604542749457231715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60118017069695166304821143 90177025604542749457231715)
          ·
            refine ⟨135265538406814124185847573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90177025604542749457231715 135265538406814124185847573)
            ·
              refine ⟨6340572112819412071211605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135265538406814124185847573 6340572112819412071211605)
              ·
                refine ⟨74303579447102485209511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6340572112819412071211605 74303579447102485209511)
                ·
                  rfl

theorem cell22_1953527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 8].length) (baseStart_1953527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953527 prefixEnd_1953527 := by exact prefixLift 1953527
  have htrace : WordTrace (prefixWord ++ tailWord_1953527) baseStart_1953527 baseEnd_1953527 := by
    simpa [prefixWord, tailWord_1953527, baseEnd_1953527] using wordTrace_append hprefix tailTrace_1953527
  have hstable : (prefixWord ++ tailWord_1953527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953527).length < 2 ^ (prefixWord ++ tailWord_1953527).sum := by decide
  have hdescent : baseEnd_1953527 < baseStart_1953527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953576 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1953576 : Nat := 118140960795 + 1953576 * 2 ^ 59
def prefixEnd_1953576 : Nat := 4983230072969 + 3 ^ 40 * 1953576 * 2
def baseEnd_1953576 : Nat := 668748988725302572410449

theorem tailTrace_1953576 : CollatzResearch.WordTrace tailWord_1953576 prefixEnd_1953576 668748988725302572410449 := by
  unfold tailWord_1953576
  simp only [CollatzResearch.WordTrace]
  refine ⟨35626385185267635531568291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47501846913690180708757721 35626385185267635531568291)
  ·
    refine ⟨53439577777901453297352437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35626385185267635531568291 53439577777901453297352437)
    ·
      refine ⟨5009960416678261246626791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53439577777901453297352437 5009960416678261246626791)
      ·
        refine ⟨7514940625017391869940187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5009960416678261246626791 7514940625017391869940187)
        ·
          refine ⟨11272410937526087804910281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7514940625017391869940187 11272410937526087804910281)
          ·
            refine ⟨8454308203144565853682711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11272410937526087804910281 8454308203144565853682711)
            ·
              refine ⟨12681462304716848780524067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454308203144565853682711 12681462304716848780524067)
              ·
                refine ⟨19022193457075273170786101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12681462304716848780524067 19022193457075273170786101)
                ·
                  refine ⟨1783330636600806859761197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19022193457075273170786101 1783330636600806859761197)
                  ·
                    refine ⟨668748988725302572410449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783330636600806859761197 668748988725302572410449)
                    ·
                      rfl

theorem cell22_1953576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1953576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953576 prefixEnd_1953576 := by exact prefixLift 1953576
  have htrace : WordTrace (prefixWord ++ tailWord_1953576) baseStart_1953576 baseEnd_1953576 := by
    simpa [prefixWord, tailWord_1953576, baseEnd_1953576] using wordTrace_append hprefix tailTrace_1953576
  have hstable : (prefixWord ++ tailWord_1953576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953576).length < 2 ^ (prefixWord ++ tailWord_1953576).sum := by decide
  have hdescent : baseEnd_1953576 < baseStart_1953576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953623 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 5]
def baseStart_1953623 : Nat := 118140960795 + 1953623 * 2 ^ 59
def prefixEnd_1953623 : Nat := 4983230072969 + 3 ^ 40 * 1953623 * 2
def baseEnd_1953623 : Nat := 222921692595270038828435

theorem tailTrace_1953623 : CollatzResearch.WordTrace tailWord_1953623 prefixEnd_1953623 222921692595270038828435 := by
  unfold tailWord_1953623
  simp only [CollatzResearch.WordTrace]
  refine ⟨71254484601364998090097523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47502989734243332060065015 71254484601364998090097523)
  ·
    refine ⟨106881726902047497135146285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71254484601364998090097523 106881726902047497135146285)
    ·
      refine ⟨40080647588267811425679857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106881726902047497135146285 40080647588267811425679857)
      ·
        refine ⟨30060485691200858569259893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40080647588267811425679857 30060485691200858569259893)
        ·
          refine ⟨2818170533550080490868115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30060485691200858569259893 2818170533550080490868115)
          ·
            refine ⟨4227255800325120736302173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818170533550080490868115 4227255800325120736302173)
            ·
              refine ⟨1585220925121920276113315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4227255800325120736302173 1585220925121920276113315)
              ·
                refine ⟨2377831387682880414169973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585220925121920276113315 2377831387682880414169973)
                ·
                  refine ⟨222921692595270038828435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2377831387682880414169973 222921692595270038828435)
                  ·
                    rfl

theorem cell22_1953623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 5].length) (baseStart_1953623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953623 prefixEnd_1953623 := by exact prefixLift 1953623
  have htrace : WordTrace (prefixWord ++ tailWord_1953623) baseStart_1953623 baseEnd_1953623 := by
    simpa [prefixWord, tailWord_1953623, baseEnd_1953623] using wordTrace_append hprefix tailTrace_1953623
  have hstable : (prefixWord ++ tailWord_1953623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953623).length < 2 ^ (prefixWord ++ tailWord_1953623).sum := by decide
  have hdescent : baseEnd_1953623 < baseStart_1953623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953649 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_1953649 : Nat := 118140960795 + 1953649 * 2 ^ 59
def prefixEnd_1953649 : Nat := 4983230072969 + 3 ^ 40 * 1953649 * 2
def baseEnd_1953649 : Nat := 668773978117154715335225

theorem tailTrace_1953649 : CollatzResearch.WordTrace tailWord_1953649 prefixEnd_1953649 668773978117154715335225 := by
  unfold tailWord_1953649
  simp only [CollatzResearch.WordTrace]
  refine ⟨71255432899270804530544001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47503621932847203020362667 71255432899270804530544001)
  ·
    refine ⟨53441574674453103397908001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71255432899270804530544001 53441574674453103397908001)
    ·
      refine ⟨40081181005839827548431001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53441574674453103397908001 40081181005839827548431001)
      ·
        refine ⟨30060885754379870661323251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40081181005839827548431001 30060885754379870661323251)
        ·
          refine ⟨45091328631569805991984877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30060885754379870661323251 45091328631569805991984877)
          ·
            refine ⟨16909248236838677246994329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45091328631569805991984877 16909248236838677246994329)
            ·
              refine ⟨12681936177629007935245747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16909248236838677246994329 12681936177629007935245747)
              ·
                refine ⟨19022904266443511902868621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12681936177629007935245747 19022904266443511902868621)
                ·
                  refine ⟨7133589099916316963575733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19022904266443511902868621 7133589099916316963575733)
                  ·
                    refine ⟨668773978117154715335225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7133589099916316963575733 668773978117154715335225)
                    ·
                      rfl

theorem cell22_1953649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_1953649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953649 prefixEnd_1953649 := by exact prefixLift 1953649
  have htrace : WordTrace (prefixWord ++ tailWord_1953649) baseStart_1953649 baseEnd_1953649 := by
    simpa [prefixWord, tailWord_1953649, baseEnd_1953649] using wordTrace_append hprefix tailTrace_1953649
  have hstable : (prefixWord ++ tailWord_1953649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953649).length < 2 ^ (prefixWord ++ tailWord_1953649).sum := by decide
  have hdescent : baseEnd_1953649 < baseStart_1953649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953726 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1953726 : Nat := 118140960795 + 1953726 * 2 ^ 59
def prefixEnd_1953726 : Nat := 4983230072969 + 3 ^ 40 * 1953726 * 2
def baseEnd_1953726 : Nat := 668800336790752181159989

theorem tailTrace_1953726 : CollatzResearch.WordTrace tailWord_1953726 prefixEnd_1953726 668800336790752181159989 := by
  unfold tailWord_1953726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8907280164998980835137129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47505494213327897787398021 8907280164998980835137129)
  ·
    refine ⟨6680460123749235626352847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8907280164998980835137129 6680460123749235626352847)
    ·
      refine ⟨10020690185623853439529271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6680460123749235626352847 10020690185623853439529271)
      ·
        refine ⟨15031035278435780159293907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10020690185623853439529271 15031035278435780159293907)
        ·
          refine ⟨22546552917653670238940861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15031035278435780159293907 22546552917653670238940861)
          ·
            refine ⟨8454957344120126339602823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22546552917653670238940861 8454957344120126339602823)
            ·
              refine ⟨12682436016180189509404235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454957344120126339602823 12682436016180189509404235)
              ·
                refine ⟨19023654024270284264106353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12682436016180189509404235 19023654024270284264106353)
                ·
                  refine ⟨14267740518202713198079765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19023654024270284264106353 14267740518202713198079765)
                  ·
                    refine ⟨668800336790752181159989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14267740518202713198079765 668800336790752181159989)
                    ·
                      rfl

theorem cell22_1953726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1953726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953726 prefixEnd_1953726 := by exact prefixLift 1953726
  have htrace : WordTrace (prefixWord ++ tailWord_1953726) baseStart_1953726 baseEnd_1953726 := by
    simpa [prefixWord, tailWord_1953726, baseEnd_1953726] using wordTrace_append hprefix tailTrace_1953726
  have hstable : (prefixWord ++ tailWord_1953726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953726).length < 2 ^ (prefixWord ++ tailWord_1953726).sum := by decide
  have hdescent : baseEnd_1953726 < baseStart_1953726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953816 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_1953816 : Nat := 118140960795 + 1953816 * 2 ^ 59
def prefixEnd_1953816 : Nat := 4983230072969 + 3 ^ 40 * 1953816 * 2
def baseEnd_1953816 : Nat := 668831145630021946409713

theorem tailTrace_1953816 : CollatzResearch.WordTrace tailWord_1953816 prefixEnd_1953816 668831145630021946409713 := by
  unfold tailWord_1953816
  simp only [CollatzResearch.WordTrace]
  refine ⟨35630761944832896025936651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47507682593110528034582201 35630761944832896025936651)
  ·
    refine ⟨53446142917249344038904977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35630761944832896025936651 53446142917249344038904977)
    ·
      refine ⟨40084607187937008029178733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53446142917249344038904977 40084607187937008029178733)
      ·
        refine ⟨15031727695476378010942025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40084607187937008029178733 15031727695476378010942025)
        ·
          refine ⟨11273795771607283508206519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15031727695476378010942025 11273795771607283508206519)
          ·
            refine ⟨16910693657410925262309779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11273795771607283508206519 16910693657410925262309779)
            ·
              refine ⟨25366040486116387893464669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16910693657410925262309779 25366040486116387893464669)
              ·
                refine ⟨9512265182293645460049251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25366040486116387893464669 9512265182293645460049251)
                ·
                  refine ⟨14268397773440468190073877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9512265182293645460049251 14268397773440468190073877)
                  ·
                    refine ⟨668831145630021946409713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14268397773440468190073877 668831145630021946409713)
                    ·
                      rfl

theorem cell22_1953816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_1953816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953816 prefixEnd_1953816 := by exact prefixLift 1953816
  have htrace : WordTrace (prefixWord ++ tailWord_1953816) baseStart_1953816 baseEnd_1953816 := by
    simpa [prefixWord, tailWord_1953816, baseEnd_1953816] using wordTrace_append hprefix tailTrace_1953816
  have hstable : (prefixWord ++ tailWord_1953816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953816).length < 2 ^ (prefixWord ++ tailWord_1953816).sum := by decide
  have hdescent : baseEnd_1953816 < baseStart_1953816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953818 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 4, 3]
def baseStart_1953818 : Nat := 118140960795 + 1953818 * 2 ^ 59
def prefixEnd_1953818 : Nat := 4983230072969 + 3 ^ 40 * 1953818 * 2
def baseEnd_1953818 : Nat := 668831830270894607859707

theorem tailTrace_1953818 : CollatzResearch.WordTrace tailWord_1953818 prefixEnd_1953818 668831830270894607859707 := by
  unfold tailWord_1953818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17815399208914636598361527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47507731223772364262297405 17815399208914636598361527)
  ·
    refine ⟨26723098813371954897542291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17815399208914636598361527 26723098813371954897542291)
    ·
      refine ⟨40084648220057932346313437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26723098813371954897542291 40084648220057932346313437)
      ·
        refine ⟨15031743082521724629867539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40084648220057932346313437 15031743082521724629867539)
        ·
          refine ⟨22547614623782586944801309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15031743082521724629867539 22547614623782586944801309)
          ·
            refine ⟨8455355483918470104300491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22547614623782586944801309 8455355483918470104300491)
            ·
              refine ⟨12683033225877705156450737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8455355483918470104300491 12683033225877705156450737)
              ·
                refine ⟨9512274919408278867338053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12683033225877705156450737 9512274919408278867338053)
                ·
                  refine ⟨1783551547389052287625885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9512274919408278867338053 1783551547389052287625885)
                  ·
                    refine ⟨668831830270894607859707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783551547389052287625885 668831830270894607859707)
                    ·
                      rfl

theorem cell22_1953818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_1953818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953818 prefixEnd_1953818 := by exact prefixLift 1953818
  have htrace : WordTrace (prefixWord ++ tailWord_1953818) baseStart_1953818 baseEnd_1953818 := by
    simpa [prefixWord, tailWord_1953818, baseEnd_1953818] using wordTrace_append hprefix tailTrace_1953818
  have hstable : (prefixWord ++ tailWord_1953818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953818).length < 2 ^ (prefixWord ++ tailWord_1953818).sum := by decide
  have hdescent : baseEnd_1953818 < baseStart_1953818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953820 : List Nat := [2, 2, 3, 1, 3, 1, 3, 3, 4]
def baseStart_1953820 : Nat := 118140960795 + 1953820 * 2 ^ 59
def prefixEnd_1953820 : Nat := 4983230072969 + 3 ^ 40 * 1953820 * 2
def baseEnd_1953820 : Nat := 222944171637255756436567

theorem tailTrace_1953820 : CollatzResearch.WordTrace tailWord_1953820 prefixEnd_1953820 222944171637255756436567 := by
  unfold tailWord_1953820
  simp only [CollatzResearch.WordTrace]
  refine ⟨35630834890825650367509457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47507779854434200490012609 35630834890825650367509457)
  ·
    refine ⟨26723126168119237775632093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35630834890825650367509457 26723126168119237775632093)
    ·
      refine ⟨10021172313044714165862035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26723126168119237775632093 10021172313044714165862035)
      ·
        refine ⟨15031758469567071248793053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10021172313044714165862035 15031758469567071248793053)
        ·
          refine ⟨5636909426087651718297395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15031758469567071248793053 5636909426087651718297395)
          ·
            refine ⟨8455364139131477577446093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636909426087651718297395 8455364139131477577446093)
            ·
              refine ⟨3170761552174304091542285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8455364139131477577446093 3170761552174304091542285)
              ·
                refine ⟨1189035582065364034328357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3170761552174304091542285 1189035582065364034328357)
                ·
                  refine ⟨222944171637255756436567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1189035582065364034328357 222944171637255756436567)
                  ·
                    rfl

theorem cell22_1953820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_1953820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953820 prefixEnd_1953820 := by exact prefixLift 1953820
  have htrace : WordTrace (prefixWord ++ tailWord_1953820) baseStart_1953820 baseEnd_1953820 := by
    simpa [prefixWord, tailWord_1953820, baseEnd_1953820] using wordTrace_append hprefix tailTrace_1953820
  have hstable : (prefixWord ++ tailWord_1953820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953820).length < 2 ^ (prefixWord ++ tailWord_1953820).sum := by decide
  have hdescent : baseEnd_1953820 < baseStart_1953820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953848 : List Nat := [2, 1, 2, 1, 6, 1, 2, 7]
def baseStart_1953848 : Nat := 118140960795 + 1953848 * 2 ^ 59
def prefixEnd_1953848 : Nat := 4983230072969 + 3 ^ 40 * 1953848 * 2
def baseEnd_1953848 : Nat := 74315788875998281067735

theorem tailTrace_1953848 : CollatzResearch.WordTrace tailWord_1953848 prefixEnd_1953848 74315788875998281067735 := by
  unfold tailWord_1953848
  simp only [CollatzResearch.WordTrace]
  refine ⟨35631345512774930758519099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47508460683699907678025465 35631345512774930758519099)
  ·
    refine ⟨53447018269162396137778649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35631345512774930758519099 53447018269162396137778649)
    ·
      refine ⟨40085263701871797103333987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53447018269162396137778649 40085263701871797103333987)
      ·
        refine ⟨60127895552807695655000981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40085263701871797103333987 60127895552807695655000981)
        ·
          refine ⟨2818495104037860733828171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60127895552807695655000981 2818495104037860733828171)
          ·
            refine ⟨4227742656056791100742257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818495104037860733828171 4227742656056791100742257)
            ·
              refine ⟨3170806992042593325556693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4227742656056791100742257 3170806992042593325556693)
              ·
                refine ⟨74315788875998281067735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3170806992042593325556693 74315788875998281067735)
                ·
                  rfl

theorem cell22_1953848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 7].length) (baseStart_1953848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953848 prefixEnd_1953848 := by exact prefixLift 1953848
  have htrace : WordTrace (prefixWord ++ tailWord_1953848) baseStart_1953848 baseEnd_1953848 := by
    simpa [prefixWord, tailWord_1953848, baseEnd_1953848] using wordTrace_append hprefix tailTrace_1953848
  have hstable : (prefixWord ++ tailWord_1953848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953848).length < 2 ^ (prefixWord ++ tailWord_1953848).sum := by decide
  have hdescent : baseEnd_1953848 < baseStart_1953848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953863 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 5, 3]
def baseStart_1953863 : Nat := 118140960795 + 1953863 * 2 ^ 59
def prefixEnd_1953863 : Nat := 4983230072969 + 3 ^ 40 * 1953863 * 2
def baseEnd_1953863 : Nat := 668847234690529490484569

theorem tailTrace_1953863 : CollatzResearch.WordTrace tailWord_1953863 prefixEnd_1953863 668847234690529490484569 := by
  unfold tailWord_1953863
  simp only [CollatzResearch.WordTrace]
  refine ⟨71263238120495519078834243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47508825413663679385889495 71263238120495519078834243)
  ·
    refine ⟨106894857180743278618251365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71263238120495519078834243 106894857180743278618251365)
    ·
      refine ⟨20042785721389364740922131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106894857180743278618251365 20042785721389364740922131)
      ·
        refine ⟨30064178582084047111383197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20042785721389364740922131 30064178582084047111383197)
        ·
          refine ⟨11274066968281517666768699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30064178582084047111383197 11274066968281517666768699)
          ·
            refine ⟨16911100452422276500153049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274066968281517666768699 16911100452422276500153049)
            ·
              refine ⟨12683325339316707375114787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16911100452422276500153049 12683325339316707375114787)
              ·
                refine ⟨19024988008975061062672181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12683325339316707375114787 19024988008975061062672181)
                ·
                  refine ⟨1783592625841411974625517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19024988008975061062672181 1783592625841411974625517)
                  ·
                    refine ⟨668847234690529490484569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783592625841411974625517 668847234690529490484569)
                    ·
                      rfl

theorem cell22_1953863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_1953863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953863 prefixEnd_1953863 := by exact prefixLift 1953863
  have htrace : WordTrace (prefixWord ++ tailWord_1953863) baseStart_1953863 baseEnd_1953863 := by
    simpa [prefixWord, tailWord_1953863, baseEnd_1953863] using wordTrace_append hprefix tailTrace_1953863
  have hstable : (prefixWord ++ tailWord_1953863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953863).length < 2 ^ (prefixWord ++ tailWord_1953863).sum := by decide
  have hdescent : baseEnd_1953863 < baseStart_1953863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953886 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1953886 : Nat := 118140960795 + 1953886 * 2 ^ 59
def prefixEnd_1953886 : Nat := 4983230072969 + 3 ^ 40 * 1953886 * 2
def baseEnd_1953886 : Nat := 668855108060565097159499

theorem tailTrace_1953886 : CollatzResearch.WordTrace tailWord_1953886 prefixEnd_1953886 668855108060565097159499 := by
  unfold tailWord_1953886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908009624926524250865189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47509384666274796004614341 8908009624926524250865189)
  ·
    refine ⟨1670251804673723297037223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8908009624926524250865189 1670251804673723297037223)
    ·
      refine ⟨2505377707010584945555835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670251804673723297037223 2505377707010584945555835)
      ·
        refine ⟨3758066560515877418333753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505377707010584945555835 3758066560515877418333753)
        ·
          refine ⟨2818549920386908063750315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3758066560515877418333753 2818549920386908063750315)
          ·
            refine ⟨4227824880580362095625473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818549920386908063750315 4227824880580362095625473)
            ·
              refine ⟨3170868660435271571719105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4227824880580362095625473 3170868660435271571719105)
              ·
                refine ⟨2378151495326453678789329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3170868660435271571719105 2378151495326453678789329)
                ·
                  refine ⟨1783613621494840259091997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2378151495326453678789329 1783613621494840259091997)
                  ·
                    refine ⟨668855108060565097159499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783613621494840259091997 668855108060565097159499)
                    ·
                      rfl

theorem cell22_1953886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1953886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953886 prefixEnd_1953886 := by exact prefixLift 1953886
  have htrace : WordTrace (prefixWord ++ tailWord_1953886) baseStart_1953886 baseEnd_1953886 := by
    simpa [prefixWord, tailWord_1953886, baseEnd_1953886] using wordTrace_append hprefix tailTrace_1953886
  have hstable : (prefixWord ++ tailWord_1953886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953886).length < 2 ^ (prefixWord ++ tailWord_1953886).sum := by decide
  have hdescent : baseEnd_1953886 < baseStart_1953886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953893 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 5]
def baseStart_1953893 : Nat := 118140960795 + 1953893 * 2 ^ 59
def prefixEnd_1953893 : Nat := 4983230072969 + 3 ^ 40 * 1953893 * 2
def baseEnd_1953893 : Nat := 222952501434539804078159

theorem tailTrace_1953893 : CollatzResearch.WordTrace tailWord_1953893 prefixEnd_1953893 222952501434539804078159 := by
  unfold tailWord_1953893
  simp only [CollatzResearch.WordTrace]
  refine ⟨71264332310386834202426333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47509554873591222801617555 71264332310386834202426333)
  ·
    refine ⟨26724124616395062825909875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71264332310386834202426333 26724124616395062825909875)
    ·
      refine ⟨40086186924592594238864813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26724124616395062825909875 40086186924592594238864813)
      ·
        refine ⟨15032320096722222839574305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40086186924592594238864813 15032320096722222839574305)
        ·
          refine ⟨11274240072541667129680729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15032320096722222839574305 11274240072541667129680729)
          ·
            refine ⟨8455680054406250347260547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11274240072541667129680729 8455680054406250347260547)
            ·
              refine ⟨12683520081609375520890821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8455680054406250347260547 12683520081609375520890821)
              ·
                refine ⟨2378160015301757910167029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12683520081609375520890821 2378160015301757910167029)
                ·
                  refine ⟨222952501434539804078159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2378160015301757910167029 222952501434539804078159)
                  ·
                    rfl

theorem cell22_1953893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_1953893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953893 prefixEnd_1953893 := by exact prefixLift 1953893
  have htrace : WordTrace (prefixWord ++ tailWord_1953893) baseStart_1953893 baseEnd_1953893 := by
    simpa [prefixWord, tailWord_1953893, baseEnd_1953893] using wordTrace_append hprefix tailTrace_1953893
  have hstable : (prefixWord ++ tailWord_1953893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953893).length < 2 ^ (prefixWord ++ tailWord_1953893).sum := by decide
  have hdescent : baseEnd_1953893 < baseStart_1953893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953910 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_1953910 : Nat := 118140960795 + 1953910 * 2 ^ 59
def prefixEnd_1953910 : Nat := 4983230072969 + 3 ^ 40 * 1953910 * 2
def baseEnd_1953910 : Nat := 222954441250345678186475

theorem tailTrace_1953910 : CollatzResearch.WordTrace tailWord_1953910 prefixEnd_1953910 222954441250345678186475 := by
  unfold tailWord_1953910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4454059521957827881612199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47509968234216830737196789 4454059521957827881612199)
  ·
    refine ⟨6681089282936741822418299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4454059521957827881612199 6681089282936741822418299)
    ·
      refine ⟨10021633924405112733627449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6681089282936741822418299 10021633924405112733627449)
      ·
        refine ⟨7516225443303834550220587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10021633924405112733627449 7516225443303834550220587)
        ·
          refine ⟨11274338164955751825330881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7516225443303834550220587 11274338164955751825330881)
          ·
            refine ⟨8455753623716813868998161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11274338164955751825330881 8455753623716813868998161)
            ·
              refine ⟨6341815217787610401748621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8455753623716813868998161 6341815217787610401748621)
              ·
                refine ⟨2378180706670353900655733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6341815217787610401748621 2378180706670353900655733)
                ·
                  refine ⟨222954441250345678186475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2378180706670353900655733 222954441250345678186475)
                  ·
                    rfl

theorem cell22_1953910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_1953910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953910 prefixEnd_1953910 := by exact prefixLift 1953910
  have htrace : WordTrace (prefixWord ++ tailWord_1953910) baseStart_1953910 baseEnd_1953910 := by
    simpa [prefixWord, tailWord_1953910, baseEnd_1953910] using wordTrace_append hprefix tailTrace_1953910
  have hstable : (prefixWord ++ tailWord_1953910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953910).length < 2 ^ (prefixWord ++ tailWord_1953910).sum := by decide
  have hdescent : baseEnd_1953910 < baseStart_1953910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953923 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 3, 4]
def baseStart_1953923 : Nat := 118140960795 + 1953923 * 2 ^ 59
def prefixEnd_1953923 : Nat := 4983230072969 + 3 ^ 40 * 1953923 * 2
def baseEnd_1953923 : Nat := 668867773916709333984385

theorem tailTrace_1953923 : CollatzResearch.WordTrace tailWord_1953923 prefixEnd_1953923 668867773916709333984385 := by
  unfold tailWord_1953923
  simp only [CollatzResearch.WordTrace]
  refine ⟨71265426500278149326018423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47510284333518766217345615 71265426500278149326018423)
  ·
    refine ⟨106898139750417223989027635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71265426500278149326018423 106898139750417223989027635)
    ·
      refine ⟨160347209625625835983541453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106898139750417223989027635 160347209625625835983541453)
      ·
        refine ⟨60130203609609688493828045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160347209625625835983541453 60130203609609688493828045)
        ·
          refine ⟨22548826353603633185185517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60130203609609688493828045 22548826353603633185185517)
          ·
            refine ⟨8455809882601362444444569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22548826353603633185185517 8455809882601362444444569)
            ·
              refine ⟨6341857411951021833333427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8455809882601362444444569 6341857411951021833333427)
              ·
                refine ⟨9512786117926532750000141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341857411951021833333427 9512786117926532750000141)
                ·
                  refine ⟨3567294794222449781250053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9512786117926532750000141 3567294794222449781250053)
                  ·
                    refine ⟨668867773916709333984385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3567294794222449781250053 668867773916709333984385)
                    ·
                      rfl

theorem cell22_1953923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 4].length) (baseStart_1953923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953923 prefixEnd_1953923 := by exact prefixLift 1953923
  have htrace : WordTrace (prefixWord ++ tailWord_1953923) baseStart_1953923 baseEnd_1953923 := by
    simpa [prefixWord, tailWord_1953923, baseEnd_1953923] using wordTrace_append hprefix tailTrace_1953923
  have hstable : (prefixWord ++ tailWord_1953923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953923).length < 2 ^ (prefixWord ++ tailWord_1953923).sum := by decide
  have hdescent : baseEnd_1953923 < baseStart_1953923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953938 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_1953938 : Nat := 118140960795 + 1953938 * 2 ^ 59
def prefixEnd_1953938 : Nat := 4983230072969 + 3 ^ 40 * 1953938 * 2
def baseEnd_1953938 : Nat := 222957636241084764953113

theorem tailTrace_1953938 : CollatzResearch.WordTrace tailWord_1953938 prefixEnd_1953938 222957636241084764953113 := by
  unfold tailWord_1953938
  simp only [CollatzResearch.WordTrace]
  refine ⟨17816493398805951721953617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47510649063482537925209645 17816493398805951721953617)
  ·
    refine ⟨13362370049104463791465213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17816493398805951721953617 13362370049104463791465213)
    ·
      refine ⟨5010888768414173921799455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13362370049104463791465213 5010888768414173921799455)
      ·
        refine ⟨7516333152621260882699183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5010888768414173921799455 7516333152621260882699183)
        ·
          refine ⟨11274499728931891324048775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7516333152621260882699183 11274499728931891324048775)
          ·
            refine ⟨16911749593397836986073163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274499728931891324048775 16911749593397836986073163)
            ·
              refine ⟨25367624390096755479109745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16911749593397836986073163 25367624390096755479109745)
              ·
                refine ⟨19025718292572566609332309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25367624390096755479109745 19025718292572566609332309)
                ·
                  refine ⟨222957636241084764953113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19025718292572566609332309 222957636241084764953113)
                  ·
                    rfl

theorem cell22_1953938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_1953938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1953938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1953938 prefixEnd_1953938 := by exact prefixLift 1953938
  have htrace : WordTrace (prefixWord ++ tailWord_1953938) baseStart_1953938 baseEnd_1953938 := by
    simpa [prefixWord, tailWord_1953938, baseEnd_1953938] using wordTrace_append hprefix tailTrace_1953938
  have hstable : (prefixWord ++ tailWord_1953938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953938).length < 2 ^ (prefixWord ++ tailWord_1953938).sum := by decide
  have hdescent : baseEnd_1953938 < baseStart_1953938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954006 : List Nat := [5, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_1954006 : Nat := 118140960795 + 1954006 * 2 ^ 59
def prefixEnd_1954006 : Nat := 4983230072969 + 3 ^ 40 * 1954006 * 2
def baseEnd_1954006 : Nat := 222965395504308261386377

theorem tailTrace_1954006 : CollatzResearch.WordTrace tailWord_1954006 prefixEnd_1954006 222965395504308261386377 := by
  unfold tailWord_1954006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4454278359936090906330617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47512302505984969667526581 4454278359936090906330617)
  ·
    refine ⟨3340708769952068179747963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4454278359936090906330617 3340708769952068179747963)
    ·
      refine ⟨5011063154928102269621945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3340708769952068179747963 5011063154928102269621945)
      ·
        refine ⟨3758297366196076702216459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5011063154928102269621945 3758297366196076702216459)
        ·
          refine ⟨5637446049294115053324689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758297366196076702216459 5637446049294115053324689)
          ·
            refine ⟨4228084536970586289993517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5637446049294115053324689 4228084536970586289993517)
            ·
              refine ⟨1585531701363969858747569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4228084536970586289993517 1585531701363969858747569)
              ·
                refine ⟨1189148776022977394060677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585531701363969858747569 1189148776022977394060677)
                ·
                  refine ⟨222965395504308261386377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1189148776022977394060677 222965395504308261386377)
                  ·
                    rfl

theorem cell22_1954006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_1954006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954006 prefixEnd_1954006 := by exact prefixLift 1954006
  have htrace : WordTrace (prefixWord ++ tailWord_1954006) baseStart_1954006 baseEnd_1954006 := by
    simpa [prefixWord, tailWord_1954006, baseEnd_1954006] using wordTrace_append hprefix tailTrace_1954006
  have hstable : (prefixWord ++ tailWord_1954006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954006).length < 2 ^ (prefixWord ++ tailWord_1954006).sum := by decide
  have hdescent : baseEnd_1954006 < baseStart_1954006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954077 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1954077 : Nat := 118140960795 + 1954077 * 2 ^ 59
def prefixEnd_1954077 : Nat := 4983230072969 + 3 ^ 40 * 1954077 * 2
def baseEnd_1954077 : Nat := 668920491263904265633913

theorem tailTrace_1954077 : CollatzResearch.WordTrace tailWord_1954077 prefixEnd_1954077 668920491263904265633913 := by
  unfold tailWord_1954077
  simp only [CollatzResearch.WordTrace]
  refine ⟨71271043341720233627124485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47514028894480155751416323 71271043341720233627124485)
  ·
    refine ⟨13363320626572543805085841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71271043341720233627124485 13363320626572543805085841)
    ·
      refine ⟨10022490469929407853814381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13363320626572543805085841 10022490469929407853814381)
      ·
        refine ⟨3758433926223527945180393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10022490469929407853814381 3758433926223527945180393)
        ·
          refine ⟨2818825444667645958885295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3758433926223527945180393 2818825444667645958885295)
          ·
            refine ⟨4228238167001468938327943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818825444667645958885295 4228238167001468938327943)
            ·
              refine ⟨6342357250502203407491915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4228238167001468938327943 6342357250502203407491915)
              ·
                refine ⟨9513535875753305111237873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6342357250502203407491915 9513535875753305111237873)
                ·
                  refine ⟨7135151906814978833428405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9513535875753305111237873 7135151906814978833428405)
                  ·
                    refine ⟨668920491263904265633913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7135151906814978833428405 668920491263904265633913)
                    ·
                      rfl

theorem cell22_1954077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1954077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954077 prefixEnd_1954077 := by exact prefixLift 1954077
  have htrace : WordTrace (prefixWord ++ tailWord_1954077) baseStart_1954077 baseEnd_1954077 := by
    simpa [prefixWord, tailWord_1954077, baseEnd_1954077] using wordTrace_append hprefix tailTrace_1954077
  have hstable : (prefixWord ++ tailWord_1954077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954077).length < 2 ^ (prefixWord ++ tailWord_1954077).sum := by decide
  have hdescent : baseEnd_1954077 < baseStart_1954077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954120 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_1954120 : Nat := 118140960795 + 1954120 * 2 ^ 59
def prefixEnd_1954120 : Nat := 4983230072969 + 3 ^ 40 * 1954120 * 2
def baseEnd_1954120 : Nat := 668935211042666486808781

theorem tailTrace_1954120 : CollatzResearch.WordTrace tailWord_1954120 prefixEnd_1954120 668935211042666486808781 := by
  unfold tailWord_1954120
  simp only [CollatzResearch.WordTrace]
  refine ⟨35636305840282225985469907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47515074453709634647293209 35636305840282225985469907)
  ·
    refine ⟨53454458760423338978204861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35636305840282225985469907 53454458760423338978204861)
    ·
      refine ⟨20045422035158752116826823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53454458760423338978204861 20045422035158752116826823)
      ·
        refine ⟨30068133052738128175240235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20045422035158752116826823 30068133052738128175240235)
        ·
          refine ⟨45102199579107192262860353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30068133052738128175240235 45102199579107192262860353)
          ·
            refine ⟨33826649684330394197145265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45102199579107192262860353 33826649684330394197145265)
            ·
              refine ⟨25369987263247795647858949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33826649684330394197145265 25369987263247795647858949)
              ·
                refine ⟨4756872611858961683973553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25369987263247795647858949 4756872611858961683973553)
                ·
                  refine ⟨3567654458894221262980165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4756872611858961683973553 3567654458894221262980165)
                  ·
                    refine ⟨668935211042666486808781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3567654458894221262980165 668935211042666486808781)
                    ·
                      rfl

theorem cell22_1954120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_1954120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954120 prefixEnd_1954120 := by exact prefixLift 1954120
  have htrace : WordTrace (prefixWord ++ tailWord_1954120) baseStart_1954120 baseEnd_1954120 := by
    simpa [prefixWord, tailWord_1954120, baseEnd_1954120] using wordTrace_append hprefix tailTrace_1954120
  have hstable : (prefixWord ++ tailWord_1954120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954120).length < 2 ^ (prefixWord ++ tailWord_1954120).sum := by decide
  have hdescent : baseEnd_1954120 < baseStart_1954120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954152 : List Nat := [2, 1, 4, 2, 2, 1, 4, 6]
def baseStart_1954152 : Nat := 118140960795 + 1954152 * 2 ^ 59
def prefixEnd_1954152 : Nat := 4983230072969 + 3 ^ 40 * 1954152 * 2
def baseEnd_1954152 : Nat := 74327351699625452223187

theorem tailTrace_1954152 : CollatzResearch.WordTrace tailWord_1954152 prefixEnd_1954152 74327351699625452223187 := by
  unfold tailWord_1954152
  simp only [CollatzResearch.WordTrace]
  refine ⟨35636889408224260718052355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47515852544299014290736473 35636889408224260718052355)
  ·
    refine ⟨53455334112336391077078533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35636889408224260718052355 53455334112336391077078533)
    ·
      refine ⟨10022875146063073326952225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53455334112336391077078533 10022875146063073326952225)
      ·
        refine ⟨7517156359547304995214169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10022875146063073326952225 7517156359547304995214169)
        ·
          refine ⟨5637867269660478746410627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7517156359547304995214169 5637867269660478746410627)
          ·
            refine ⟨8456800904490718119615941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637867269660478746410627 8456800904490718119615941)
            ·
              refine ⟨1585650169592009647427989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8456800904490718119615941 1585650169592009647427989)
              ·
                refine ⟨74327351699625452223187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1585650169592009647427989 74327351699625452223187)
                ·
                  rfl

theorem cell22_1954152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 6].length) (baseStart_1954152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954152 prefixEnd_1954152 := by exact prefixLift 1954152
  have htrace : WordTrace (prefixWord ++ tailWord_1954152) baseStart_1954152 baseEnd_1954152 := by
    simpa [prefixWord, tailWord_1954152, baseEnd_1954152] using wordTrace_append hprefix tailTrace_1954152
  have hstable : (prefixWord ++ tailWord_1954152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954152).length < 2 ^ (prefixWord ++ tailWord_1954152).sum := by decide
  have hdescent : baseEnd_1954152 < baseStart_1954152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954180 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 7]
def baseStart_1954180 : Nat := 118140960795 + 1954180 * 2 ^ 59
def prefixEnd_1954180 : Nat := 4983230072969 + 3 ^ 40 * 1954180 * 2
def baseEnd_1954180 : Nat := 222985250089615443436199

theorem tailTrace_1954180 : CollatzResearch.WordTrace tailWord_1954180 prefixEnd_1954180 222985250089615443436199 := by
  unfold tailWord_1954180
  simp only [CollatzResearch.WordTrace]
  refine ⟨35637400030173541109061997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47516533373564721478749329 35637400030173541109061997)
  ·
    refine ⟨13364025011315077915898249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35637400030173541109061997 13364025011315077915898249)
    ·
      refine ⟨10023018758486308436923687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13364025011315077915898249 10023018758486308436923687)
      ·
        refine ⟨15034528137729462655385531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10023018758486308436923687 15034528137729462655385531)
        ·
          refine ⟨22551792206594193983078297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15034528137729462655385531 22551792206594193983078297)
          ·
            refine ⟨16913844154945645487308723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22551792206594193983078297 16913844154945645487308723)
            ·
              refine ⟨25370766232418468230963085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16913844154945645487308723 25370766232418468230963085)
              ·
                refine ⟨9514037337156925586611157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25370766232418468230963085 9514037337156925586611157)
                ·
                  refine ⟨222985250089615443436199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9514037337156925586611157 222985250089615443436199)
                  ·
                    rfl

theorem cell22_1954180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_1954180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954180 prefixEnd_1954180 := by exact prefixLift 1954180
  have htrace : WordTrace (prefixWord ++ tailWord_1954180) baseStart_1954180 baseEnd_1954180 := by
    simpa [prefixWord, tailWord_1954180, baseEnd_1954180] using wordTrace_append hprefix tailTrace_1954180
  have hstable : (prefixWord ++ tailWord_1954180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954180).length < 2 ^ (prefixWord ++ tailWord_1954180).sum := by decide
  have hdescent : baseEnd_1954180 < baseStart_1954180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954240 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_1954240 : Nat := 118140960795 + 1954240 * 2 ^ 59
def prefixEnd_1954240 : Nat := 4983230072969 + 3 ^ 40 * 1954240 * 2
def baseEnd_1954240 : Nat := 668976289495026173808413

theorem tailTrace_1954240 : CollatzResearch.WordTrace tailWord_1954240 prefixEnd_1954240 668976289495026173808413 := by
  unfold tailWord_1954240
  simp only [CollatzResearch.WordTrace]
  refine ⟨35638494220064856232654087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47517992293419808310205449 35638494220064856232654087)
  ·
    refine ⟨53457741330097284348981131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35638494220064856232654087 53457741330097284348981131)
    ·
      refine ⟨80186611995145926523471697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53457741330097284348981131 80186611995145926523471697)
      ·
        refine ⟨60139958996359444892603773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80186611995145926523471697 60139958996359444892603773)
        ·
          refine ⟨22552484623634791834726415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60139958996359444892603773 22552484623634791834726415)
          ·
            refine ⟨33828726935452187752089623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22552484623634791834726415 33828726935452187752089623)
            ·
              refine ⟨50743090403178281628134435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33828726935452187752089623 50743090403178281628134435)
              ·
                refine ⟨76114635604767422442201653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50743090403178281628134435 76114635604767422442201653)
                ·
                  refine ⟨7135747087946945853956405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76114635604767422442201653 7135747087946945853956405)
                  ·
                    refine ⟨668976289495026173808413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7135747087946945853956405 668976289495026173808413)
                    ·
                      rfl

theorem cell22_1954240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_1954240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954240 prefixEnd_1954240 := by exact prefixLift 1954240
  have htrace : WordTrace (prefixWord ++ tailWord_1954240) baseStart_1954240 baseEnd_1954240 := by
    simpa [prefixWord, tailWord_1954240, baseEnd_1954240] using wordTrace_append hprefix tailTrace_1954240
  have hstable : (prefixWord ++ tailWord_1954240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954240).length < 2 ^ (prefixWord ++ tailWord_1954240).sum := by decide
  have hdescent : baseEnd_1954240 < baseStart_1954240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954255 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 1, 6]
def baseStart_1954255 : Nat := 118140960795 + 1954255 * 2 ^ 59
def prefixEnd_1954255 : Nat := 4983230072969 + 3 ^ 40 * 1954255 * 2
def baseEnd_1954255 : Nat := 668981424301571134683367

theorem tailTrace_1954255 : CollatzResearch.WordTrace tailWord_1954255 prefixEnd_1954255 668981424301571134683367 := by
  unfold tailWord_1954255
  simp only [CollatzResearch.WordTrace]
  refine ⟨71277535535075370027104219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47518357023383580018069479 71277535535075370027104219)
  ·
    refine ⟨106916303302613055040656329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71277535535075370027104219 106916303302613055040656329)
    ·
      refine ⟨80187227476959791280492247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106916303302613055040656329 80187227476959791280492247)
      ·
        refine ⟨120280841215439686920738371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80187227476959791280492247 120280841215439686920738371)
        ·
          refine ⟨180421261823159530381107557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120280841215439686920738371 180421261823159530381107557)
          ·
            refine ⟨33828986591842411946457667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180421261823159530381107557 33828986591842411946457667)
            ·
              refine ⟨50743479887763617919686501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33828986591842411946457667 50743479887763617919686501)
              ·
                refine ⟨9514402478955678359941219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50743479887763617919686501 9514402478955678359941219)
                ·
                  refine ⟨14271603718433517539911829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9514402478955678359941219 14271603718433517539911829)
                  ·
                    refine ⟨668981424301571134683367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14271603718433517539911829 668981424301571134683367)
                    ·
                      rfl

theorem cell22_1954255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_1954255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954255 prefixEnd_1954255 := by exact prefixLift 1954255
  have htrace : WordTrace (prefixWord ++ tailWord_1954255) baseStart_1954255 baseEnd_1954255 := by
    simpa [prefixWord, tailWord_1954255, baseEnd_1954255] using wordTrace_append hprefix tailTrace_1954255
  have hstable : (prefixWord ++ tailWord_1954255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954255).length < 2 ^ (prefixWord ++ tailWord_1954255).sum := by decide
  have hdescent : baseEnd_1954255 < baseStart_1954255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954308 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_1954308 : Nat := 118140960795 + 1954308 * 2 ^ 59
def prefixEnd_1954308 : Nat := 4983230072969 + 3 ^ 40 * 1954308 * 2
def baseEnd_1954308 : Nat := 668999567284696663108205

theorem tailTrace_1954308 : CollatzResearch.WordTrace tailWord_1954308 prefixEnd_1954308 668999567284696663108205 := by
  unfold tailWord_1954308
  simp only [CollatzResearch.WordTrace]
  refine ⟨35639734301941680039391789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47519645735922240052522385 35639734301941680039391789)
  ·
    refine ⟨13364900363228130014771921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35639734301941680039391789 13364900363228130014771921)
    ·
      refine ⟨10023675272421097511078941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13364900363228130014771921 10023675272421097511078941)
      ·
        refine ⟨3758878227157911566654603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10023675272421097511078941 3758878227157911566654603)
        ·
          refine ⟨5638317340736867349981905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758878227157911566654603 5638317340736867349981905)
          ·
            refine ⟨4228738005552650512486429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5638317340736867349981905 4228738005552650512486429)
            ·
              refine ⟨1585776752082243942182411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4228738005552650512486429 1585776752082243942182411)
              ·
                refine ⟨2378665128123365913273617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585776752082243942182411 2378665128123365913273617)
                ·
                  refine ⟨1783998846092524434955213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2378665128123365913273617 1783998846092524434955213)
                  ·
                    refine ⟨668999567284696663108205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783998846092524434955213 668999567284696663108205)
                    ·
                      rfl

theorem cell22_1954308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_1954308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954308 prefixEnd_1954308 := by exact prefixLift 1954308
  have htrace : WordTrace (prefixWord ++ tailWord_1954308) baseStart_1954308 baseEnd_1954308 := by
    simpa [prefixWord, tailWord_1954308, baseEnd_1954308] using wordTrace_append hprefix tailTrace_1954308
  have hstable : (prefixWord ++ tailWord_1954308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954308).length < 2 ^ (prefixWord ++ tailWord_1954308).sum := by decide
  have hdescent : baseEnd_1954308 < baseStart_1954308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954332 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 7]
def baseStart_1954332 : Nat := 118140960795 + 1954332 * 2 ^ 59
def prefixEnd_1954332 : Nat := 4983230072969 + 3 ^ 40 * 1954332 * 2
def baseEnd_1954332 : Nat := 223002594325056200169377

theorem tailTrace_1954332 : CollatzResearch.WordTrace tailWord_1954332 prefixEnd_1954332 223002594325056200169377 := by
  unfold tailWord_1954332
  simp only [CollatzResearch.WordTrace]
  refine ⟨35640171977898206088828625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47520229303864274785104833 35640171977898206088828625)
  ·
    refine ⟨26730128983423654566621469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35640171977898206088828625 26730128983423654566621469)
    ·
      refine ⟨10023798368783870462483051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26730128983423654566621469 10023798368783870462483051)
      ·
        refine ⟨15035697553175805693724577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10023798368783870462483051 15035697553175805693724577)
        ·
          refine ⟨11276773164881854270293433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15035697553175805693724577 11276773164881854270293433)
          ·
            refine ⟨8457579873661390702720075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11276773164881854270293433 8457579873661390702720075)
            ·
              refine ⟨12686369810492086054080113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8457579873661390702720075 12686369810492086054080113)
              ·
                refine ⟨9514777357869064540560085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12686369810492086054080113 9514777357869064540560085)
                ·
                  refine ⟨223002594325056200169377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9514777357869064540560085 223002594325056200169377)
                  ·
                    rfl

theorem cell22_1954332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_1954332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954332 prefixEnd_1954332 := by exact prefixLift 1954332
  have htrace : WordTrace (prefixWord ++ tailWord_1954332) baseStart_1954332 baseEnd_1954332 := by
    simpa [prefixWord, tailWord_1954332, baseEnd_1954332] using wordTrace_append hprefix tailTrace_1954332
  have hstable : (prefixWord ++ tailWord_1954332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954332).length < 2 ^ (prefixWord ++ tailWord_1954332).sum := by decide
  have hdescent : baseEnd_1954332 < baseStart_1954332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954379 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 1, 4]
def baseStart_1954379 : Nat := 118140960795 + 1954379 * 2 ^ 59
def prefixEnd_1954379 : Nat := 4983230072969 + 3 ^ 40 * 1954379 * 2
def baseEnd_1954379 : Nat := 669023872035676144582987

theorem tailTrace_1954379 : CollatzResearch.WordTrace tailWord_1954379 prefixEnd_1954379 669023872035676144582987 := by
  unfold tailWord_1954379
  simp only [CollatzResearch.WordTrace]
  refine ⟨71282058186626139204618191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47521372124417426136412127 71282058186626139204618191)
  ·
    refine ⟨106923087279939208806927287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71282058186626139204618191 106923087279939208806927287)
    ·
      refine ⟨160384630919908813210390931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106923087279939208806927287 160384630919908813210390931)
      ·
        refine ⟨240576946379863219815586397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160384630919908813210390931 240576946379863219815586397)
        ·
          refine ⟨90216354892448707430844899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240576946379863219815586397 90216354892448707430844899)
          ·
            refine ⟨135324532338673061146267349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90216354892448707430844899 135324532338673061146267349)
            ·
              refine ⟨3171668726687649870615641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 135324532338673061146267349 3171668726687649870615641)
              ·
                refine ⟨2378751545015737402961731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3171668726687649870615641 2378751545015737402961731)
                ·
                  refine ⟨3568127317523606104442597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378751545015737402961731 3568127317523606104442597)
                  ·
                    refine ⟨669023872035676144582987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3568127317523606104442597 669023872035676144582987)
                    ·
                      rfl

theorem cell22_1954379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 4].length) (baseStart_1954379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954379 prefixEnd_1954379 := by exact prefixLift 1954379
  have htrace : WordTrace (prefixWord ++ tailWord_1954379) baseStart_1954379 baseEnd_1954379 := by
    simpa [prefixWord, tailWord_1954379, baseEnd_1954379] using wordTrace_append hprefix tailTrace_1954379
  have hstable : (prefixWord ++ tailWord_1954379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954379).length < 2 ^ (prefixWord ++ tailWord_1954379).sum := by decide
  have hdescent : baseEnd_1954379 < baseStart_1954379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954392 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_1954392 : Nat := 118140960795 + 1954392 * 2 ^ 59
def prefixEnd_1954392 : Nat := 4983230072969 + 3 ^ 40 * 1954392 * 2
def baseEnd_1954392 : Nat := 669028322201348444007947

theorem tailTrace_1954392 : CollatzResearch.WordTrace tailWord_1954392 prefixEnd_1954392 669028322201348444007947 := by
  unfold tailWord_1954392
  simp only [CollatzResearch.WordTrace]
  refine ⟨35641266167789521212420715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47521688223719361616560953 35641266167789521212420715)
  ·
    refine ⟨53461899251684281818631073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35641266167789521212420715 53461899251684281818631073)
    ·
      refine ⟨40096424438763211363973305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53461899251684281818631073 40096424438763211363973305)
      ·
        refine ⟨30072318329072408522979979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40096424438763211363973305 30072318329072408522979979)
        ·
          refine ⟨45108477493608612784469969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30072318329072408522979979 45108477493608612784469969)
          ·
            refine ⟨33831358120206459588352477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45108477493608612784469969 33831358120206459588352477)
            ·
              refine ⟨12686759295077422345632179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33831358120206459588352477 12686759295077422345632179)
              ·
                refine ⟨19030138942616133518448269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12686759295077422345632179 19030138942616133518448269)
                ·
                  refine ⟨7136302103481050069418101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19030138942616133518448269 7136302103481050069418101)
                  ·
                    refine ⟨669028322201348444007947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7136302103481050069418101 669028322201348444007947)
                    ·
                      rfl

theorem cell22_1954392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_1954392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954392 prefixEnd_1954392 := by exact prefixLift 1954392
  have htrace : WordTrace (prefixWord ++ tailWord_1954392) baseStart_1954392 baseEnd_1954392 := by
    simpa [prefixWord, tailWord_1954392, baseEnd_1954392] using wordTrace_append hprefix tailTrace_1954392
  have hstable : (prefixWord ++ tailWord_1954392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954392).length < 2 ^ (prefixWord ++ tailWord_1954392).sum := by decide
  have hdescent : baseEnd_1954392 < baseStart_1954392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954407 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1954407 : Nat := 118140960795 + 1954407 * 2 ^ 59
def prefixEnd_1954407 : Nat := 4983230072969 + 3 ^ 40 * 1954407 * 2
def baseEnd_1954407 : Nat := 669033457007893404882901

theorem tailTrace_1954407 : CollatzResearch.WordTrace tailWord_1954407 prefixEnd_1954407 669033457007893404882901 := by
  unfold tailWord_1954407
  simp only [CollatzResearch.WordTrace]
  refine ⟨71283079430524699986637475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47522052953683133324424983 71283079430524699986637475)
  ·
    refine ⟨106924619145787049979956213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71283079430524699986637475 106924619145787049979956213)
    ·
      refine ⟨10024183044917535935620895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106924619145787049979956213 10024183044917535935620895)
      ·
        refine ⟨15036274567376303903431343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10024183044917535935620895 15036274567376303903431343)
        ·
          refine ⟨22554411851064455855147015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15036274567376303903431343 22554411851064455855147015)
          ·
            refine ⟨33831617776596683782720523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22554411851064455855147015 33831617776596683782720523)
            ·
              refine ⟨50747426664895025674080785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33831617776596683782720523 50747426664895025674080785)
              ·
                refine ⟨38060569998671269255560589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50747426664895025674080785 38060569998671269255560589)
                ·
                  refine ⟨14272713749501725970835221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38060569998671269255560589 14272713749501725970835221)
                  ·
                    refine ⟨669033457007893404882901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14272713749501725970835221 669033457007893404882901)
                    ·
                      rfl

theorem cell22_1954407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1954407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954407 prefixEnd_1954407 := by exact prefixLift 1954407
  have htrace : WordTrace (prefixWord ++ tailWord_1954407) baseStart_1954407 baseEnd_1954407 := by
    simpa [prefixWord, tailWord_1954407, baseEnd_1954407] using wordTrace_append hprefix tailTrace_1954407
  have hstable : (prefixWord ++ tailWord_1954407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954407).length < 2 ^ (prefixWord ++ tailWord_1954407).sum := by decide
  have hdescent : baseEnd_1954407 < baseStart_1954407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954439 : List Nat := [1, 1, 4, 2, 1, 2, 5, 6]
def baseStart_1954439 : Nat := 118140960795 + 1954439 * 2 ^ 59
def prefixEnd_1954439 : Nat := 4983230072969 + 3 ^ 40 * 1954439 * 2
def baseEnd_1954439 : Nat := 74338267917983998675867

theorem tailTrace_1954439 : CollatzResearch.WordTrace tailWord_1954439 prefixEnd_1954439 74338267917983998675867 := by
  unfold tailWord_1954439
  simp only [CollatzResearch.WordTrace]
  refine ⟨71284246566408769451802371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47522831044272512967868247 71284246566408769451802371)
  ·
    refine ⟨106926369849613154177703557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71284246566408769451802371 106926369849613154177703557)
    ·
      refine ⟨20048694346802466408319417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106926369849613154177703557 20048694346802466408319417)
      ·
        refine ⟨15036520760101849806239563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20048694346802466408319417 15036520760101849806239563)
        ·
          refine ⟨22554781140152774709359345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15036520760101849806239563 22554781140152774709359345)
          ·
            refine ⟨16916085855114581032019509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22554781140152774709359345 16916085855114581032019509)
            ·
              refine ⟨1585883048916991971751829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16916085855114581032019509 1585883048916991971751829)
              ·
                refine ⟨74338267917983998675867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1585883048916991971751829 74338267917983998675867)
                ·
                  rfl

theorem cell22_1954439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 6].length) (baseStart_1954439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954439 prefixEnd_1954439 := by exact prefixLift 1954439
  have htrace : WordTrace (prefixWord ++ tailWord_1954439) baseStart_1954439 baseEnd_1954439 := by
    simpa [prefixWord, tailWord_1954439, baseEnd_1954439] using wordTrace_append hprefix tailTrace_1954439
  have hstable : (prefixWord ++ tailWord_1954439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954439).length < 2 ^ (prefixWord ++ tailWord_1954439).sum := by decide
  have hdescent : baseEnd_1954439 < baseStart_1954439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954544 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_1954544 : Nat := 118140960795 + 1954544 * 2 ^ 59
def prefixEnd_1954544 : Nat := 4983230072969 + 3 ^ 40 * 1954544 * 2
def baseEnd_1954544 : Nat := 669080354907670714207481

theorem tailTrace_1954544 : CollatzResearch.WordTrace tailWord_1954544 prefixEnd_1954544 669080354907670714207481 := by
  unfold tailWord_1954544
  simp only [CollatzResearch.WordTrace]
  refine ⟨35644038115514186192187343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47525384154018914922916457 35644038115514186192187343)
  ·
    refine ⟨53466057173271279288281015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35644038115514186192187343 53466057173271279288281015)
    ·
      refine ⟨80199085759906918932421523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53466057173271279288281015 80199085759906918932421523)
      ·
        refine ⟨120298628639860378398632285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80199085759906918932421523 120298628639860378398632285)
        ·
          refine ⟨45111985739947641899487107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120298628639860378398632285 45111985739947641899487107)
          ·
            refine ⟨67667978609921462849230661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45111985739947641899487107 67667978609921462849230661)
            ·
              refine ⟨12687745989360274284230749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67667978609921462849230661 12687745989360274284230749)
              ·
                refine ⟨4757904746010102856586531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12687745989360274284230749 4757904746010102856586531)
                ·
                  refine ⟨7136857119015154284879797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757904746010102856586531 7136857119015154284879797)
                  ·
                    refine ⟨669080354907670714207481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7136857119015154284879797 669080354907670714207481)
                    ·
                      rfl

theorem cell22_1954544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_1954544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954544 prefixEnd_1954544 := by exact prefixLift 1954544
  have htrace : WordTrace (prefixWord ++ tailWord_1954544) baseStart_1954544 baseEnd_1954544 := by
    simpa [prefixWord, tailWord_1954544, baseEnd_1954544] using wordTrace_append hprefix tailTrace_1954544
  have hstable : (prefixWord ++ tailWord_1954544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954544).length < 2 ^ (prefixWord ++ tailWord_1954544).sum := by decide
  have hdescent : baseEnd_1954544 < baseStart_1954544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954591 : List Nat := [1, 1, 2, 4, 2, 4, 1, 7]
def baseStart_1954591 : Nat := 118140960795 + 1954591 * 2 ^ 59
def prefixEnd_1954591 : Nat := 4983230072969 + 3 ^ 40 * 1954591 * 2
def baseEnd_1954591 : Nat := 74344049329797584253593

theorem tailTrace_1954591 : CollatzResearch.WordTrace tailWord_1954591 prefixEnd_1954591 74344049329797584253593 := by
  unfold tailWord_1954591
  simp only [CollatzResearch.WordTrace]
  refine ⟨71289790461858099411335627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47526526974572066274223751 71289790461858099411335627)
  ·
    refine ⟨106934685692787149117003441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71289790461858099411335627 106934685692787149117003441)
    ·
      refine ⟨80201014269590361837752581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106934685692787149117003441 80201014269590361837752581)
      ·
        refine ⟨15037690175548192844578609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80201014269590361837752581 15037690175548192844578609)
        ·
          refine ⟨11278267631661144633433957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15037690175548192844578609 11278267631661144633433957)
          ·
            refine ⟨2114675180936464618768867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11278267631661144633433957 2114675180936464618768867)
            ·
              refine ⟨3172012771404696928153301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114675180936464618768867 3172012771404696928153301)
              ·
                refine ⟨74344049329797584253593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3172012771404696928153301 74344049329797584253593)
                ·
                  rfl

theorem cell22_1954591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 7].length) (baseStart_1954591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954591 prefixEnd_1954591 := by exact prefixLift 1954591
  have htrace : WordTrace (prefixWord ++ tailWord_1954591) baseStart_1954591 baseEnd_1954591 := by
    simpa [prefixWord, tailWord_1954591, baseEnd_1954591] using wordTrace_append hprefix tailTrace_1954591
  have hstable : (prefixWord ++ tailWord_1954591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954591).length < 2 ^ (prefixWord ++ tailWord_1954591).sum := by decide
  have hdescent : baseEnd_1954591 < baseStart_1954591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954604 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_1954604 : Nat := 118140960795 + 1954604 * 2 ^ 59
def prefixEnd_1954604 : Nat := 4983230072969 + 3 ^ 40 * 1954604 * 2
def baseEnd_1954604 : Nat := 669100894133850557707297

theorem tailTrace_1954604 : CollatzResearch.WordTrace tailWord_1954604 prefixEnd_1954604 669100894133850557707297 := by
  unfold tailWord_1954604
  simp only [CollatzResearch.WordTrace]
  refine ⟨35645132305405501315779433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47526843073874001754372577 35645132305405501315779433)
  ·
    refine ⟨26733849229054125986834575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35645132305405501315779433 26733849229054125986834575)
    ·
      refine ⟨40100773843581188980251863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26733849229054125986834575 40100773843581188980251863)
      ·
        refine ⟨60151160765371783470377795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40100773843581188980251863 60151160765371783470377795)
        ·
          refine ⟨90226741148057675205566693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60151160765371783470377795 90226741148057675205566693)
          ·
            refine ⟨16917513965260814101043755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90226741148057675205566693 16917513965260814101043755)
            ·
              refine ⟨25376270947891221151565633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16917513965260814101043755 25376270947891221151565633)
              ·
                refine ⟨19032203210918415863674225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25376270947891221151565633 19032203210918415863674225)
                ·
                  refine ⟨14274152408188811897755669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19032203210918415863674225 14274152408188811897755669)
                  ·
                    refine ⟨669100894133850557707297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14274152408188811897755669 669100894133850557707297)
                    ·
                      rfl

theorem cell22_1954604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_1954604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954604 prefixEnd_1954604 := by exact prefixLift 1954604
  have htrace : WordTrace (prefixWord ++ tailWord_1954604) baseStart_1954604 baseEnd_1954604 := by
    simpa [prefixWord, tailWord_1954604, baseEnd_1954604] using wordTrace_append hprefix tailTrace_1954604
  have hstable : (prefixWord ++ tailWord_1954604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954604).length < 2 ^ (prefixWord ++ tailWord_1954604).sum := by decide
  have hdescent : baseEnd_1954604 < baseStart_1954604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954636 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 7]
def baseStart_1954636 : Nat := 118140960795 + 1954636 * 2 ^ 59
def prefixEnd_1954636 : Nat := 4983230072969 + 3 ^ 40 * 1954636 * 2
def baseEnd_1954636 : Nat := 223037282795937713635733

theorem tailTrace_1954636 : CollatzResearch.WordTrace tailWord_1954636 prefixEnd_1954636 223037282795937713635733 := by
  unfold tailWord_1954636
  simp only [CollatzResearch.WordTrace]
  refine ⟨35645715873347536048361881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47527621164463381397815841 35645715873347536048361881)
  ·
    refine ⟨26734286905010652036271411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35645715873347536048361881 26734286905010652036271411)
    ·
      refine ⟨40101430357515978054407117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26734286905010652036271411 40101430357515978054407117)
      ·
        refine ⟨15038036384068491770402669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40101430357515978054407117 15038036384068491770402669)
        ·
          refine ⟨5639263644025684413901001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15038036384068491770402669 5639263644025684413901001)
          ·
            refine ⟨4229447733019263310425751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5639263644025684413901001 4229447733019263310425751)
            ·
              refine ⟨6344171599528894965638627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4229447733019263310425751 6344171599528894965638627)
              ·
                refine ⟨9516257399293342448457941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6344171599528894965638627 9516257399293342448457941)
                ·
                  refine ⟨223037282795937713635733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9516257399293342448457941 223037282795937713635733)
                  ·
                    rfl

theorem cell22_1954636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_1954636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954636 prefixEnd_1954636 := by exact prefixLift 1954636
  have htrace : WordTrace (prefixWord ++ tailWord_1954636) baseStart_1954636 baseEnd_1954636 := by
    simpa [prefixWord, tailWord_1954636, baseEnd_1954636] using wordTrace_append hprefix tailTrace_1954636
  have hstable : (prefixWord ++ tailWord_1954636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954636).length < 2 ^ (prefixWord ++ tailWord_1954636).sum := by decide
  have hdescent : baseEnd_1954636 < baseStart_1954636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954698 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_1954698 : Nat := 118140960795 + 1954698 * 2 ^ 59
def prefixEnd_1954698 : Nat := 4983230072969 + 3 ^ 40 * 1954698 * 2
def baseEnd_1954698 : Nat := 223044357418288548619003

theorem tailTrace_1954698 : CollatzResearch.WordTrace tailWord_1954698 prefixEnd_1954698 223044357418288548619003 := by
  unfold tailWord_1954698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17823423268117614171370187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47529128714980304456987165 17823423268117614171370187)
  ·
    refine ⟨26735134902176421257055281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17823423268117614171370187 26735134902176421257055281)
    ·
      refine ⟨20051351176632315942791461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26735134902176421257055281 20051351176632315942791461)
      ·
        refine ⟨3759628345618559239273399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20051351176632315942791461 3759628345618559239273399)
        ·
          refine ⟨5639442518427838858910099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3759628345618559239273399 5639442518427838858910099)
          ·
            refine ⟨8459163777641758288365149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639442518427838858910099 8459163777641758288365149)
            ·
              refine ⟨3172186416615659358136931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8459163777641758288365149 3172186416615659358136931)
              ·
                refine ⟨4758279624923489037205397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172186416615659358136931 4758279624923489037205397)
                ·
                  refine ⟨223044357418288548619003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4758279624923489037205397 223044357418288548619003)
                  ·
                    rfl

theorem cell22_1954698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_1954698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954698 prefixEnd_1954698 := by exact prefixLift 1954698
  have htrace : WordTrace (prefixWord ++ tailWord_1954698) baseStart_1954698 baseEnd_1954698 := by
    simpa [prefixWord, tailWord_1954698, baseEnd_1954698] using wordTrace_append hprefix tailTrace_1954698
  have hstable : (prefixWord ++ tailWord_1954698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954698).length < 2 ^ (prefixWord ++ tailWord_1954698).sum := by decide
  have hdescent : baseEnd_1954698 < baseStart_1954698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954711 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 4, 4]
def baseStart_1954711 : Nat := 118140960795 + 1954711 * 2 ^ 59
def prefixEnd_1954711 : Nat := 4983230072969 + 3 ^ 40 * 1954711 * 2
def baseEnd_1954711 : Nat := 669137522420537945281969

theorem tailTrace_1954711 : CollatzResearch.WordTrace tailWord_1954711 prefixEnd_1954711 669137522420537945281969 := by
  unfold tailWord_1954711
  simp only [CollatzResearch.WordTrace]
  refine ⟨71294167221423359905703987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47529444814282239937135991 71294167221423359905703987)
  ·
    refine ⟨106941250832135039858555981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71294167221423359905703987 106941250832135039858555981)
    ·
      refine ⟨40102969062050639946958493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106941250832135039858555981 40102969062050639946958493)
      ·
        refine ⟨15038613398268989980109435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40102969062050639946958493 15038613398268989980109435)
        ·
          refine ⟨22557920097403484970164153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15038613398268989980109435 22557920097403484970164153)
          ·
            refine ⟨16918440073052613727623115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22557920097403484970164153 16918440073052613727623115)
            ·
              refine ⟨25377660109578920591434673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16918440073052613727623115 25377660109578920591434673)
              ·
                refine ⟨19033245082184190443576005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25377660109578920591434673 19033245082184190443576005)
                ·
                  refine ⟨3568733452909535708170501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19033245082184190443576005 3568733452909535708170501)
                  ·
                    refine ⟨669137522420537945281969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3568733452909535708170501 669137522420537945281969)
                    ·
                      rfl

theorem cell22_1954711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_1954711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954711 prefixEnd_1954711 := by exact prefixLift 1954711
  have htrace : WordTrace (prefixWord ++ tailWord_1954711) baseStart_1954711 baseEnd_1954711 := by
    simpa [prefixWord, tailWord_1954711, baseEnd_1954711] using wordTrace_append hprefix tailTrace_1954711
  have hstable : (prefixWord ++ tailWord_1954711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954711).length < 2 ^ (prefixWord ++ tailWord_1954711).sum := by decide
  have hdescent : baseEnd_1954711 < baseStart_1954711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954749 : List Nat := [1, 4, 1, 2, 5, 1, 2, 2, 4]
def baseStart_1954749 : Nat := 118140960795 + 1954749 * 2 ^ 59
def prefixEnd_1954749 : Nat := 4983230072969 + 3 ^ 40 * 1954749 * 2
def baseEnd_1954749 : Nat := 223050176865706170943951

theorem tailTrace_1954749 : CollatzResearch.WordTrace tailWord_1954749 prefixEnd_1954749 223050176865706170943951 := by
  unfold tailWord_1954749
  simp only [CollatzResearch.WordTrace]
  refine ⟨71295553195285692395587301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47530368796857128263724867 71295553195285692395587301)
  ·
    refine ⟨13367916224116067324172619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71295553195285692395587301 13367916224116067324172619)
    ·
      refine ⟨20051874336174100986258929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13367916224116067324172619 20051874336174100986258929)
      ·
        refine ⟨15038905752130575739694197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20051874336174100986258929 15038905752130575739694197)
        ·
          refine ⟨1409897414262241475596331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15038905752130575739694197 1409897414262241475596331)
          ·
            refine ⟨2114846121393362213394497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409897414262241475596331 2114846121393362213394497)
            ·
              refine ⟨1586134591045021660045873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2114846121393362213394497 1586134591045021660045873)
              ·
                refine ⟨1189600943283766245034405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586134591045021660045873 1189600943283766245034405)
                ·
                  refine ⟨223050176865706170943951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1189600943283766245034405 223050176865706170943951)
                  ·
                    rfl

theorem cell22_1954749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_1954749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954749 prefixEnd_1954749 := by exact prefixLift 1954749
  have htrace : WordTrace (prefixWord ++ tailWord_1954749) baseStart_1954749 baseEnd_1954749 := by
    simpa [prefixWord, tailWord_1954749, baseEnd_1954749] using wordTrace_append hprefix tailTrace_1954749
  have hstable : (prefixWord ++ tailWord_1954749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954749).length < 2 ^ (prefixWord ++ tailWord_1954749).sum := by decide
  have hdescent : baseEnd_1954749 < baseStart_1954749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954760 : List Nat := [2, 1, 3, 1, 6, 1, 1, 7]
def baseStart_1954760 : Nat := 118140960795 + 1954760 * 2 ^ 59
def prefixEnd_1954760 : Nat := 4983230072969 + 3 ^ 40 * 1954760 * 2
def baseEnd_1954760 : Nat := 74350477346879794534091

theorem tailTrace_1954760 : CollatzResearch.WordTrace tailWord_1954760 prefixEnd_1954760 74350477346879794534091 := by
  unfold tailWord_1954760
  simp only [CollatzResearch.WordTrace]
  refine ⟨35647977199122920637118867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47530636265497227516158489 35647977199122920637118867)
  ·
    refine ⟨53471965798684380955678301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35647977199122920637118867 53471965798684380955678301)
    ·
      refine ⟨20051987174506642858379363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53471965798684380955678301 20051987174506642858379363)
      ·
        refine ⟨30077980761759964287569045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20051987174506642858379363 30077980761759964287569045)
        ·
          refine ⟨1409905348207498325979799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30077980761759964287569045 1409905348207498325979799)
          ·
            refine ⟨2114858022311247488969699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409905348207498325979799 2114858022311247488969699)
            ·
              refine ⟨3172287033466871233454549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114858022311247488969699 3172287033466871233454549)
              ·
                refine ⟨74350477346879794534091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3172287033466871233454549 74350477346879794534091)
                ·
                  rfl

theorem cell22_1954760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 7].length) (baseStart_1954760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954760 prefixEnd_1954760 := by exact prefixLift 1954760
  have htrace : WordTrace (prefixWord ++ tailWord_1954760) baseStart_1954760 baseEnd_1954760 := by
    simpa [prefixWord, tailWord_1954760, baseEnd_1954760] using wordTrace_append hprefix tailTrace_1954760
  have hstable : (prefixWord ++ tailWord_1954760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954760).length < 2 ^ (prefixWord ++ tailWord_1954760).sum := by decide
  have hdescent : baseEnd_1954760 < baseStart_1954760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954831 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 7, 5]
def baseStart_1954831 : Nat := 118140960795 + 1954831 * 2 ^ 59
def prefixEnd_1954831 : Nat := 4983230072969 + 3 ^ 40 * 1954831 * 2
def baseEnd_1954831 : Nat := 669178600872897632281601

theorem tailTrace_1954831 : CollatzResearch.WordTrace tailWord_1954831 prefixEnd_1954831 669178600872897632281601 := by
  unfold tailWord_1954831
  simp only [CollatzResearch.WordTrace]
  refine ⟨71298543980988620400072347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47532362653992413600048231 71298543980988620400072347)
  ·
    refine ⟨106947815971482930600108521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71298543980988620400072347 106947815971482930600108521)
    ·
      refine ⟨80210861978612197950081391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106947815971482930600108521 80210861978612197950081391)
      ·
        refine ⟨120316292967918296925122087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80210861978612197950081391 120316292967918296925122087)
        ·
          refine ⟨180474439451877445387683131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120316292967918296925122087 180474439451877445387683131)
          ·
            refine ⟨270711659177816168081524697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180474439451877445387683131 270711659177816168081524697)
            ·
              refine ⟨203033744383362126061143523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270711659177816168081524697 203033744383362126061143523)
              ·
                refine ⟨304550616575043189091715285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203033744383362126061143523 304550616575043189091715285)
                ·
                  refine ⟨7137905075977574744337077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 304550616575043189091715285 7137905075977574744337077)
                  ·
                    refine ⟨669178600872897632281601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7137905075977574744337077 669178600872897632281601)
                    ·
                      rfl

theorem cell22_1954831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_1954831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954831 prefixEnd_1954831 := by exact prefixLift 1954831
  have htrace : WordTrace (prefixWord ++ tailWord_1954831) baseStart_1954831 baseEnd_1954831 := by
    simpa [prefixWord, tailWord_1954831, baseEnd_1954831] using wordTrace_append hprefix tailTrace_1954831
  have hstable : (prefixWord ++ tailWord_1954831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954831).length < 2 ^ (prefixWord ++ tailWord_1954831).sum := by decide
  have hdescent : baseEnd_1954831 < baseStart_1954831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954865 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 2, 3]
def baseStart_1954865 : Nat := 118140960795 + 1954865 * 2 ^ 59
def prefixEnd_1954865 : Nat := 4983230072969 + 3 ^ 40 * 1954865 * 2
def baseEnd_1954865 : Nat := 669190239767732876931497

theorem tailTrace_1954865 : CollatzResearch.WordTrace tailWord_1954865 prefixEnd_1954865 669190239767732876931497 := by
  unfold tailWord_1954865
  simp only [CollatzResearch.WordTrace]
  refine ⟨71299784062865444206810049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47533189375243629471206699 71299784062865444206810049)
  ·
    refine ⟨53474838047149083155107537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71299784062865444206810049 53474838047149083155107537)
    ·
      refine ⟨40106128535361812366330653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53474838047149083155107537 40106128535361812366330653)
      ·
        refine ⟨15039798200760679637373995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40106128535361812366330653 15039798200760679637373995)
        ·
          refine ⟨22559697301141019456060993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15039798200760679637373995 22559697301141019456060993)
          ·
            refine ⟨16919772975855764592045745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22559697301141019456060993 16919772975855764592045745)
            ·
              refine ⟨12689829731891823444034309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16919772975855764592045745 12689829731891823444034309)
              ·
                refine ⟨2379343074729716895756433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12689829731891823444034309 2379343074729716895756433)
                ·
                  refine ⟨1784507306047287671817325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2379343074729716895756433 1784507306047287671817325)
                  ·
                    refine ⟨669190239767732876931497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1784507306047287671817325 669190239767732876931497)
                    ·
                      rfl

theorem cell22_1954865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_1954865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954865 prefixEnd_1954865 := by exact prefixLift 1954865
  have htrace : WordTrace (prefixWord ++ tailWord_1954865) baseStart_1954865 baseEnd_1954865 := by
    simpa [prefixWord, tailWord_1954865, baseEnd_1954865] using wordTrace_append hprefix tailTrace_1954865
  have hstable : (prefixWord ++ tailWord_1954865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954865).length < 2 ^ (prefixWord ++ tailWord_1954865).sum := by decide
  have hdescent : baseEnd_1954865 < baseStart_1954865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954927 : List Nat := [1, 1, 2, 1, 3, 3, 3, 4, 1, 3]
def baseStart_1954927 : Nat := 118140960795 + 1954927 * 2 ^ 59
def prefixEnd_1954927 : Nat := 4983230072969 + 3 ^ 40 * 1954927 * 2
def baseEnd_1954927 : Nat := 669211463634785381881307

theorem tailTrace_1954927 : CollatzResearch.WordTrace tailWord_1954927 prefixEnd_1954927 669211463634785381881307 := by
  unfold tailWord_1954927
  simp only [CollatzResearch.WordTrace]
  refine ⟨71302045388640828795567035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47534696925760552530378023 71302045388640828795567035)
  ·
    refine ⟨106953068082961243193350553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71302045388640828795567035 106953068082961243193350553)
    ·
      refine ⟨80214801062220932395012915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106953068082961243193350553 80214801062220932395012915)
      ·
        refine ⟨120322201593331398592519373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80214801062220932395012915 120322201593331398592519373)
        ·
          refine ⟨45120825597499274472194765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120322201593331398592519373 45120825597499274472194765)
          ·
            refine ⟨16920309599062227927073037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45120825597499274472194765 16920309599062227927073037)
            ·
              refine ⟨6345116099648335472652389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16920309599062227927073037 6345116099648335472652389)
              ·
                refine ⟨1189709268684062901122323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6345116099648335472652389 1189709268684062901122323)
                ·
                  refine ⟨1784563903026094351683485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189709268684062901122323 1784563903026094351683485)
                  ·
                    refine ⟨669211463634785381881307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1784563903026094351683485 669211463634785381881307)
                    ·
                      rfl

theorem cell22_1954927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 1, 3].length) (baseStart_1954927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954927 prefixEnd_1954927 := by exact prefixLift 1954927
  have htrace : WordTrace (prefixWord ++ tailWord_1954927) baseStart_1954927 baseEnd_1954927 := by
    simpa [prefixWord, tailWord_1954927, baseEnd_1954927] using wordTrace_append hprefix tailTrace_1954927
  have hstable : (prefixWord ++ tailWord_1954927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954927).length < 2 ^ (prefixWord ++ tailWord_1954927).sum := by decide
  have hdescent : baseEnd_1954927 < baseStart_1954927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954974 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1954974 : Nat := 118140960795 + 1954974 * 2 ^ 59
def prefixEnd_1954974 : Nat := 4983230072969 + 3 ^ 40 * 1954974 * 2
def baseEnd_1954974 : Nat := 223075850898430975318721

theorem tailTrace_1954974 : CollatzResearch.WordTrace tailWord_1954974 prefixEnd_1954974 223075850898430975318721 := by
  unfold tailWord_1954974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8912969952433819477815997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47535839746313703881685317 8912969952433819477815997)
  ·
    refine ⟨3342363732162682304180999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8912969952433819477815997 3342363732162682304180999)
    ·
      refine ⟨5013545598244023456271499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3342363732162682304180999 5013545598244023456271499)
      ·
        refine ⟨7520318397366035184407249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5013545598244023456271499 7520318397366035184407249)
        ·
          refine ⟨5640238798024526388305437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7520318397366035184407249 5640238798024526388305437)
          ·
            refine ⟨2115089549259197395614539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5640238798024526388305437 2115089549259197395614539)
            ·
              refine ⟨3172634323888796093421809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115089549259197395614539 3172634323888796093421809)
              ·
                refine ⟨2379475742916597070066357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3172634323888796093421809 2379475742916597070066357)
                ·
                  refine ⟨223075850898430975318721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2379475742916597070066357 223075850898430975318721)
                  ·
                    rfl

theorem cell22_1954974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1954974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1954974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1954974 prefixEnd_1954974 := by exact prefixLift 1954974
  have htrace : WordTrace (prefixWord ++ tailWord_1954974) baseStart_1954974 baseEnd_1954974 := by
    simpa [prefixWord, tailWord_1954974, baseEnd_1954974] using wordTrace_append hprefix tailTrace_1954974
  have hstable : (prefixWord ++ tailWord_1954974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954974).length < 2 ^ (prefixWord ++ tailWord_1954974).sum := by decide
  have hdescent : baseEnd_1954974 < baseStart_1954974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955032 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 2, 4]
def baseStart_1955032 : Nat := 118140960795 + 1955032 * 2 ^ 59
def prefixEnd_1955032 : Nat := 4983230072969 + 3 ^ 40 * 1955032 * 2
def baseEnd_1955032 : Nat := 669247407280600108005985

theorem tailTrace_1955032 : CollatzResearch.WordTrace tailWord_1955032 prefixEnd_1955032 669247407280600108005985 := by
  unfold tailWord_1955032
  simp only [CollatzResearch.WordTrace]
  refine ⟨35652937526630215864069675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47537250035506954485426233 35652937526630215864069675)
  ·
    refine ⟨53479406289945323796104513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35652937526630215864069675 53479406289945323796104513)
    ·
      refine ⟨40109554717458992847078385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53479406289945323796104513 40109554717458992847078385)
      ·
        refine ⟨30082166038094244635308789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40109554717458992847078385 30082166038094244635308789)
        ·
          refine ⟨2820203066071335434560199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30082166038094244635308789 2820203066071335434560199)
          ·
            refine ⟨4230304599107003151840299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820203066071335434560199 4230304599107003151840299)
            ·
              refine ⟨6345456898660504727760449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4230304599107003151840299 6345456898660504727760449)
              ·
                refine ⟨4759092673995378545820337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6345456898660504727760449 4759092673995378545820337)
                ·
                  refine ⟨3569319505496533909365253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4759092673995378545820337 3569319505496533909365253)
                  ·
                    refine ⟨669247407280600108005985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3569319505496533909365253 669247407280600108005985)
                    ·
                      rfl

theorem cell22_1955032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_1955032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955032 prefixEnd_1955032 := by exact prefixLift 1955032
  have htrace : WordTrace (prefixWord ++ tailWord_1955032) baseStart_1955032 baseEnd_1955032 := by
    simpa [prefixWord, tailWord_1955032, baseEnd_1955032] using wordTrace_append hprefix tailTrace_1955032
  have hstable : (prefixWord ++ tailWord_1955032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955032).length < 2 ^ (prefixWord ++ tailWord_1955032).sum := by decide
  have hdescent : baseEnd_1955032 < baseStart_1955032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955047 : List Nat := [1, 1, 5, 3, 2, 1, 2, 7]
def baseStart_1955047 : Nat := 118140960795 + 1955047 * 2 ^ 59
def prefixEnd_1955047 : Nat := 4983230072969 + 3 ^ 40 * 1955047 * 2
def baseEnd_1955047 : Nat := 74361393565238340986771

theorem tailTrace_1955047 : CollatzResearch.WordTrace tailWord_1955047 prefixEnd_1955047 74361393565238340986771 := by
  unfold tailWord_1955047
  simp only [CollatzResearch.WordTrace]
  refine ⟨71306422148206089289935395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47537614765470726193290263 71306422148206089289935395)
  ·
    refine ⟨106959633222309133934903093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71306422148206089289935395 106959633222309133934903093)
    ·
      refine ⟨10027465614591481306397165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106959633222309133934903093 10027465614591481306397165)
      ·
        refine ⟨3760299605471805489898937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10027465614591481306397165 3760299605471805489898937)
        ·
          refine ⟨2820224704103854117424203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3760299605471805489898937 2820224704103854117424203)
          ·
            refine ⟨4230337056155781176136305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820224704103854117424203 4230337056155781176136305)
            ·
              refine ⟨3172752792116835882102229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4230337056155781176136305 3172752792116835882102229)
              ·
                refine ⟨74361393565238340986771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3172752792116835882102229 74361393565238340986771)
                ·
                  rfl

theorem cell22_1955047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 7].length) (baseStart_1955047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955047 prefixEnd_1955047 := by exact prefixLift 1955047
  have htrace : WordTrace (prefixWord ++ tailWord_1955047) baseStart_1955047 baseEnd_1955047 := by
    simpa [prefixWord, tailWord_1955047, baseEnd_1955047] using wordTrace_append hprefix tailTrace_1955047
  have hstable : (prefixWord ++ tailWord_1955047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955047).length < 2 ^ (prefixWord ++ tailWord_1955047).sum := by decide
  have hdescent : baseEnd_1955047 < baseStart_1955047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955062 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_1955062 : Nat := 118140960795 + 1955062 * 2 ^ 59
def prefixEnd_1955062 : Nat := 4983230072969 + 3 ^ 40 * 1955062 * 2
def baseEnd_1955062 : Nat := 669257676893690029755893

theorem tailTrace_1955062 : CollatzResearch.WordTrace tailWord_1955062 prefixEnd_1955062 669257676893690029755893 := by
  unfold tailWord_1955062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456685577696984178233215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47537979495434497901154293 4456685577696984178233215)
  ·
    refine ⟨6685028366545476267349823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4456685577696984178233215 6685028366545476267349823)
    ·
      refine ⟨10027542549818214401024735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6685028366545476267349823 10027542549818214401024735)
      ·
        refine ⟨15041313824727321601537103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10027542549818214401024735 15041313824727321601537103)
        ·
          refine ⟨22561970737090982402305655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15041313824727321601537103 22561970737090982402305655)
          ·
            refine ⟨33842956105636473603458483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22561970737090982402305655 33842956105636473603458483)
            ·
              refine ⟨50764434158454710405187725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33842956105636473603458483 50764434158454710405187725)
              ·
                refine ⟨19036662809420516401945397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50764434158454710405187725 19036662809420516401945397)
                ·
                  refine ⟨1784687138383173412682381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19036662809420516401945397 1784687138383173412682381)
                  ·
                    refine ⟨669257676893690029755893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1784687138383173412682381 669257676893690029755893)
                    ·
                      rfl

theorem cell22_1955062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_1955062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955062 prefixEnd_1955062 := by exact prefixLift 1955062
  have htrace : WordTrace (prefixWord ++ tailWord_1955062) baseStart_1955062 baseEnd_1955062 := by
    simpa [prefixWord, tailWord_1955062, baseEnd_1955062] using wordTrace_append hprefix tailTrace_1955062
  have hstable : (prefixWord ++ tailWord_1955062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955062).length < 2 ^ (prefixWord ++ tailWord_1955062).sum := by decide
  have hdescent : baseEnd_1955062 < baseStart_1955062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955096 : List Nat := [2, 1, 2, 3, 1, 3, 4, 2, 1, 3]
def baseStart_1955096 : Nat := 118140960795 + 1955096 * 2 ^ 59
def prefixEnd_1955096 : Nat := 4983230072969 + 3 ^ 40 * 1955096 * 2
def baseEnd_1955096 : Nat := 669269315788525274405789

theorem tailTrace_1955096 : CollatzResearch.WordTrace tailWord_1955096 prefixEnd_1955096 669269315788525274405789 := by
  unfold tailWord_1955096
  simp only [CollatzResearch.WordTrace]
  refine ⟨35654104662514285329234571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47538806216685713772312761 35654104662514285329234571)
  ·
    refine ⟨53481156993771427993851857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35654104662514285329234571 53481156993771427993851857)
    ·
      refine ⟨40110867745328570995388893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53481156993771427993851857 40110867745328570995388893)
      ·
        refine ⟨15041575404498214123270835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40110867745328570995388893 15041575404498214123270835)
        ·
          refine ⟨22562363106747321184906253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15041575404498214123270835 22562363106747321184906253)
          ·
            refine ⟨8460886165030245444339845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22562363106747321184906253 8460886165030245444339845)
            ·
              refine ⟨1586416155943171020813721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8460886165030245444339845 1586416155943171020813721)
              ·
                refine ⟨1189812116957378265610291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586416155943171020813721 1189812116957378265610291)
                ·
                  refine ⟨1784718175436067398415437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189812116957378265610291 1784718175436067398415437)
                  ·
                    refine ⟨669269315788525274405789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1784718175436067398415437 669269315788525274405789)
                    ·
                      rfl

theorem cell22_1955096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_1955096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955096 prefixEnd_1955096 := by exact prefixLift 1955096
  have htrace : WordTrace (prefixWord ++ tailWord_1955096) baseStart_1955096 baseEnd_1955096 := by
    simpa [prefixWord, tailWord_1955096, baseEnd_1955096] using wordTrace_append hprefix tailTrace_1955096
  have hstable : (prefixWord ++ tailWord_1955096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955096).length < 2 ^ (prefixWord ++ tailWord_1955096).sum := by decide
  have hdescent : baseEnd_1955096 < baseStart_1955096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955120 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 6]
def baseStart_1955120 : Nat := 118140960795 + 1955120 * 2 ^ 59
def prefixEnd_1955120 : Nat := 4983230072969 + 3 ^ 40 * 1955120 * 2
def baseEnd_1955120 : Nat := 223092510492999070601905

theorem tailTrace_1955120 : CollatzResearch.WordTrace tailWord_1955120 prefixEnd_1955120 223092510492999070601905 := by
  unfold tailWord_1955120
  simp only [CollatzResearch.WordTrace]
  refine ⟨35654542338470811378671407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47539389784627748504895209 35654542338470811378671407)
  ·
    refine ⟨53481813507706217068007111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35654542338470811378671407 53481813507706217068007111)
    ·
      refine ⟨80222720261559325602010667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53481813507706217068007111 80222720261559325602010667)
      ·
        refine ⟨120334080392338988403016001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80222720261559325602010667 120334080392338988403016001)
        ·
          refine ⟨90250560294254241302262001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120334080392338988403016001 90250560294254241302262001)
          ·
            refine ⟨67687920220690680976696501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90250560294254241302262001 67687920220690680976696501)
            ·
              refine ⟨6345742520689751341565297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67687920220690680976696501 6345742520689751341565297)
              ·
                refine ⟨4759306890517313506173973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6345742520689751341565297 4759306890517313506173973)
                ·
                  refine ⟨223092510492999070601905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4759306890517313506173973 223092510492999070601905)
                  ·
                    rfl

theorem cell22_1955120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_1955120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955120 prefixEnd_1955120 := by exact prefixLift 1955120
  have htrace : WordTrace (prefixWord ++ tailWord_1955120) baseStart_1955120 baseEnd_1955120 := by
    simpa [prefixWord, tailWord_1955120, baseEnd_1955120] using wordTrace_append hprefix tailTrace_1955120
  have hstable : (prefixWord ++ tailWord_1955120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955120).length < 2 ^ (prefixWord ++ tailWord_1955120).sum := by decide
  have hdescent : baseEnd_1955120 < baseStart_1955120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955122 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_1955122 : Nat := 118140960795 + 1955122 * 2 ^ 59
def prefixEnd_1955122 : Nat := 4983230072969 + 3 ^ 40 * 1955122 * 2
def baseEnd_1955122 : Nat := 669278216119869873255709

theorem tailTrace_1955122 : CollatzResearch.WordTrace tailWord_1955122 prefixEnd_1955122 669278216119869873255709 := by
  unfold tailWord_1955122
  simp only [CollatzResearch.WordTrace]
  refine ⟨17827289405733594274728905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47539438415289584732610413 17827289405733594274728905)
  ·
    refine ⟨13370467054300195706046679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17827289405733594274728905 13370467054300195706046679)
    ·
      refine ⟨20055700581450293559070019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13370467054300195706046679 20055700581450293559070019)
      ·
        refine ⟨30083550872175440338605029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20055700581450293559070019 30083550872175440338605029)
        ·
          refine ⟨5640665788532895063488443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30083550872175440338605029 5640665788532895063488443)
          ·
            refine ⟨8460998682799342595232665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640665788532895063488443 8460998682799342595232665)
            ·
              refine ⟨6345749012099506946424499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8460998682799342595232665 6345749012099506946424499)
              ·
                refine ⟨9518623518149260419636749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345749012099506946424499 9518623518149260419636749)
                ·
                  refine ⟨3569483819305972657363781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9518623518149260419636749 3569483819305972657363781)
                  ·
                    refine ⟨669278216119869873255709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3569483819305972657363781 669278216119869873255709)
                    ·
                      rfl

theorem cell22_1955122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_1955122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955122 prefixEnd_1955122 := by exact prefixLift 1955122
  have htrace : WordTrace (prefixWord ++ tailWord_1955122) baseStart_1955122 baseEnd_1955122 := by
    simpa [prefixWord, tailWord_1955122, baseEnd_1955122] using wordTrace_append hprefix tailTrace_1955122
  have hstable : (prefixWord ++ tailWord_1955122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955122).length < 2 ^ (prefixWord ++ tailWord_1955122).sum := by decide
  have hdescent : baseEnd_1955122 < baseStart_1955122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955152 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 4, 3]
def baseStart_1955152 : Nat := 118140960795 + 1955152 * 2 ^ 59
def prefixEnd_1955152 : Nat := 4983230072969 + 3 ^ 40 * 1955152 * 2
def baseEnd_1955152 : Nat := 669288485732959795005617

theorem tailTrace_1955152 : CollatzResearch.WordTrace tailWord_1955152 prefixEnd_1955152 669288485732959795005617 := by
  unfold tailWord_1955152
  simp only [CollatzResearch.WordTrace]
  refine ⟨35655125906412846111253855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47540167875217128148338473 35655125906412846111253855)
  ·
    refine ⟨53482688859619269166880783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35655125906412846111253855 53482688859619269166880783)
    ·
      refine ⟨80224033289428903750321175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53482688859619269166880783 80224033289428903750321175)
      ·
        refine ⟨120336049934143355625481763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80224033289428903750321175 120336049934143355625481763)
        ·
          refine ⟨180504074901215033438222645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120336049934143355625481763 180504074901215033438222645)
          ·
            refine ⟨16922257021988909384833373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180504074901215033438222645 16922257021988909384833373)
            ·
              refine ⟨6345846383245841019312515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16922257021988909384833373 6345846383245841019312515)
              ·
                refine ⟨9518769574868761528968773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345846383245841019312515 9518769574868761528968773)
                ·
                  refine ⟨1784769295287892786681645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9518769574868761528968773 1784769295287892786681645)
                  ·
                    refine ⟨669288485732959795005617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1784769295287892786681645 669288485732959795005617)
                    ·
                      rfl

theorem cell22_1955152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4, 3].length) (baseStart_1955152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955152 prefixEnd_1955152 := by exact prefixLift 1955152
  have htrace : WordTrace (prefixWord ++ tailWord_1955152) baseStart_1955152 baseEnd_1955152 := by
    simpa [prefixWord, tailWord_1955152, baseEnd_1955152] using wordTrace_append hprefix tailTrace_1955152
  have hstable : (prefixWord ++ tailWord_1955152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955152).length < 2 ^ (prefixWord ++ tailWord_1955152).sum := by decide
  have hdescent : baseEnd_1955152 < baseStart_1955152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955272 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 6]
def baseStart_1955272 : Nat := 118140960795 + 1955272 * 2 ^ 59
def prefixEnd_1955272 : Nat := 4983230072969 + 3 ^ 40 * 1955272 * 2
def baseEnd_1955272 : Nat := 223109854728439827335083

theorem tailTrace_1955272 : CollatzResearch.WordTrace tailWord_1955272 prefixEnd_1955272 223109854728439827335083 := by
  unfold tailWord_1955272
  simp only [CollatzResearch.WordTrace]
  refine ⟨35657314286195476358438035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47543085714927301811250713 35657314286195476358438035)
  ·
    refine ⟨53485971429293214537657053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35657314286195476358438035 53485971429293214537657053)
    ·
      refine ⟨20057239285984955451621395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53485971429293214537657053 20057239285984955451621395)
      ·
        refine ⟨30085858928977433177432093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20057239285984955451621395 30085858928977433177432093)
        ·
          refine ⟨11282197098366537441537035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30085858928977433177432093 11282197098366537441537035)
          ·
            refine ⟨16923295647549806162305553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11282197098366537441537035 16923295647549806162305553)
            ·
              refine ⟨12692471735662354621729165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16923295647549806162305553 12692471735662354621729165)
              ·
                refine ⟨4759676900873382983148437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12692471735662354621729165 4759676900873382983148437)
                ·
                  refine ⟨223109854728439827335083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4759676900873382983148437 223109854728439827335083)
                  ·
                    rfl

theorem cell22_1955272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_1955272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955272 prefixEnd_1955272 := by exact prefixLift 1955272
  have htrace : WordTrace (prefixWord ++ tailWord_1955272) baseStart_1955272 baseEnd_1955272 := by
    simpa [prefixWord, tailWord_1955272, baseEnd_1955272] using wordTrace_append hprefix tailTrace_1955272
  have hstable : (prefixWord ++ tailWord_1955272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955272).length < 2 ^ (prefixWord ++ tailWord_1955272).sum := by decide
  have hdescent : baseEnd_1955272 < baseStart_1955272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955304 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 4, 3]
def baseStart_1955304 : Nat := 118140960795 + 1955304 * 2 ^ 59
def prefixEnd_1955304 : Nat := 4983230072969 + 3 ^ 40 * 1955304 * 2
def baseEnd_1955304 : Nat := 669340518439282065205151

theorem tailTrace_1955304 : CollatzResearch.WordTrace tailWord_1955304 prefixEnd_1955304 669340518439282065205151 := by
  unfold tailWord_1955304
  simp only [CollatzResearch.WordTrace]
  refine ⟨35657897854137511091020483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47543863805516681454693977 35657897854137511091020483)
  ·
    refine ⟨53486846781206266636530725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35657897854137511091020483 53486846781206266636530725)
    ·
      refine ⟨10028783771476174994349511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53486846781206266636530725 10028783771476174994349511)
      ·
        refine ⟨15043175657214262491524267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10028783771476174994349511 15043175657214262491524267)
        ·
          refine ⟨22564763485821393737286401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15043175657214262491524267 22564763485821393737286401)
          ·
            refine ⟨16923572614366045302964801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22564763485821393737286401 16923572614366045302964801)
            ·
              refine ⟨12692679460774533977223601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16923572614366045302964801 12692679460774533977223601)
              ·
                refine ⟨9519509595580900482917701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12692679460774533977223601 9519509595580900482917701)
                ·
                  refine ⟨1784908049171418840547069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9519509595580900482917701 1784908049171418840547069)
                  ·
                    refine ⟨669340518439282065205151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1784908049171418840547069 669340518439282065205151)
                    ·
                      rfl

theorem cell22_1955304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_1955304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955304 prefixEnd_1955304 := by exact prefixLift 1955304
  have htrace : WordTrace (prefixWord ++ tailWord_1955304) baseStart_1955304 baseEnd_1955304 := by
    simpa [prefixWord, tailWord_1955304, baseEnd_1955304] using wordTrace_append hprefix tailTrace_1955304
  have hstable : (prefixWord ++ tailWord_1955304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955304).length < 2 ^ (prefixWord ++ tailWord_1955304).sum := by decide
  have hdescent : baseEnd_1955304 < baseStart_1955304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955338 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 2, 3]
def baseStart_1955338 : Nat := 118140960795 + 1955338 * 2 ^ 59
def prefixEnd_1955338 : Nat := 4983230072969 + 3 ^ 40 * 1955338 * 2
def baseEnd_1955338 : Nat := 669352157334117309855047

theorem tailTrace_1955338 : CollatzResearch.WordTrace tailWord_1955338 prefixEnd_1955338 669352157334117309855047 := by
  unfold tailWord_1955338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17829258947537961497194667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47544690526767897325852445 17829258947537961497194667)
  ·
    refine ⟨26743888421306942245792001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17829258947537961497194667 26743888421306942245792001)
    ·
      refine ⟨20057916315980206684344001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26743888421306942245792001 20057916315980206684344001)
      ·
        refine ⟨15043437236985155013258001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20057916315980206684344001 15043437236985155013258001)
        ·
          refine ⟨11282577927738866259943501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15043437236985155013258001 11282577927738866259943501)
          ·
            refine ⟨4230966722902074847478813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11282577927738866259943501 4230966722902074847478813)
            ·
              refine ⟨1586612521088278067804555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4230966722902074847478813 1586612521088278067804555)
              ·
                refine ⟨2379918781632417101706833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586612521088278067804555 2379918781632417101706833)
                ·
                  refine ⟨1784939086224312826280125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2379918781632417101706833 1784939086224312826280125)
                  ·
                    refine ⟨669352157334117309855047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1784939086224312826280125 669352157334117309855047)
                    ·
                      rfl

theorem cell22_1955338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_1955338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955338 prefixEnd_1955338 := by exact prefixLift 1955338
  have htrace : WordTrace (prefixWord ++ tailWord_1955338) baseStart_1955338 baseEnd_1955338 := by
    simpa [prefixWord, tailWord_1955338, baseEnd_1955338] using wordTrace_append hprefix tailTrace_1955338
  have hstable : (prefixWord ++ tailWord_1955338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955338).length < 2 ^ (prefixWord ++ tailWord_1955338).sum := by decide
  have hdescent : baseEnd_1955338 < baseStart_1955338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955392 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_1955392 : Nat := 118140960795 + 1955392 * 2 ^ 59
def prefixEnd_1955392 : Nat := 4983230072969 + 3 ^ 40 * 1955392 * 2
def baseEnd_1955392 : Nat := 669370642637679169004881

theorem tailTrace_1955392 : CollatzResearch.WordTrace tailWord_1955392 prefixEnd_1955392 669370642637679169004881 := by
  unfold tailWord_1955392
  simp only [CollatzResearch.WordTrace]
  refine ⟨35659502665978106605622215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47546003554637475474162953 35659502665978106605622215)
  ·
    refine ⟨53489253998967159908433323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35659502665978106605622215 53489253998967159908433323)
    ·
      refine ⟨80233880998450739862649985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53489253998967159908433323 80233880998450739862649985)
      ·
        refine ⟨60175410748838054896987489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80233880998450739862649985 60175410748838054896987489)
        ·
          refine ⟨45131558061628541172740617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60175410748838054896987489 45131558061628541172740617)
          ·
            refine ⟨33848668546221405879555463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45131558061628541172740617 33848668546221405879555463)
            ·
              refine ⟨50773002819332108819333195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33848668546221405879555463 50773002819332108819333195)
              ·
                refine ⟨76159504228998163228999793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50773002819332108819333195 76159504228998163228999793)
                ·
                  refine ⟨57119628171748622421749845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76159504228998163228999793 57119628171748622421749845)
                  ·
                    refine ⟨669370642637679169004881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57119628171748622421749845 669370642637679169004881)
                    ·
                      rfl

theorem cell22_1955392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_1955392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955392 prefixEnd_1955392 := by exact prefixLift 1955392
  have htrace : WordTrace (prefixWord ++ tailWord_1955392) baseStart_1955392 baseEnd_1955392 := by
    simpa [prefixWord, tailWord_1955392, baseEnd_1955392] using wordTrace_append hprefix tailTrace_1955392
  have hstable : (prefixWord ++ tailWord_1955392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955392).length < 2 ^ (prefixWord ++ tailWord_1955392).sum := by decide
  have hdescent : baseEnd_1955392 < baseStart_1955392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955407 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 8]
def baseStart_1955407 : Nat := 118140960795 + 1955407 * 2 ^ 59
def prefixEnd_1955407 : Nat := 4983230072969 + 3 ^ 40 * 1955407 * 2
def baseEnd_1955407 : Nat := 223125259148074709959945

theorem tailTrace_1955407 : CollatzResearch.WordTrace tailWord_1955407 prefixEnd_1955407 223125259148074709959945 := by
  unfold tailWord_1955407
  simp only [CollatzResearch.WordTrace]
  refine ⟨71319552426901870773040475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47546368284601247182026983 71319552426901870773040475)
  ·
    refine ⟨106979328640352806159560713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71319552426901870773040475 106979328640352806159560713)
    ·
      refine ⟨80234496480264604619670535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106979328640352806159560713 80234496480264604619670535)
      ·
        refine ⟨120351744720396906929505803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80234496480264604619670535 120351744720396906929505803)
        ·
          refine ⟨180527617080595360394258705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120351744720396906929505803 180527617080595360394258705)
          ·
            refine ⟨135395712810446520295694029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180527617080595360394258705 135395712810446520295694029)
            ·
              refine ⟨50773392303917445110885261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135395712810446520295694029 50773392303917445110885261)
              ·
                refine ⟨19040022113969041916581973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50773392303917445110885261 19040022113969041916581973)
                ·
                  refine ⟨223125259148074709959945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19040022113969041916581973 223125259148074709959945)
                  ·
                    rfl

theorem cell22_1955407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 8].length) (baseStart_1955407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955407 prefixEnd_1955407 := by exact prefixLift 1955407
  have htrace : WordTrace (prefixWord ++ tailWord_1955407) baseStart_1955407 baseEnd_1955407 := by
    simpa [prefixWord, tailWord_1955407, baseEnd_1955407] using wordTrace_append hprefix tailTrace_1955407
  have hstable : (prefixWord ++ tailWord_1955407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955407).length < 2 ^ (prefixWord ++ tailWord_1955407).sum := by decide
  have hdescent : baseEnd_1955407 < baseStart_1955407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955409 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_1955409 : Nat := 118140960795 + 1955409 * 2 ^ 59
def prefixEnd_1955409 : Nat := 4983230072969 + 3 ^ 40 * 1955409 * 2
def baseEnd_1955409 : Nat := 669376462085096791329829

theorem tailTrace_1955409 : CollatzResearch.WordTrace tailWord_1955409 prefixEnd_1955409 669376462085096791329829 := by
  unfold tailWord_1955409
  simp only [CollatzResearch.WordTrace]
  refine ⟨71319625372894625114613281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47546416915263083409742187 71319625372894625114613281)
  ·
    refine ⟨53489719029670968835959961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71319625372894625114613281 53489719029670968835959961)
    ·
      refine ⟨40117289272253226626969971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53489719029670968835959961 40117289272253226626969971)
      ·
        refine ⟨60175933908379839940454957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40117289272253226626969971 60175933908379839940454957)
        ·
          refine ⟨22565975215642439977670609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60175933908379839940454957 22565975215642439977670609)
          ·
            refine ⟨16924481411731829983252957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22565975215642439977670609 16924481411731829983252957)
            ·
              refine ⟨6346680529399436243719859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16924481411731829983252957 6346680529399436243719859)
              ·
                refine ⟨9520020794099154365579789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6346680529399436243719859 9520020794099154365579789)
                ·
                  refine ⟨3570007797787182887092421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9520020794099154365579789 3570007797787182887092421)
                  ·
                    refine ⟨669376462085096791329829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3570007797787182887092421 669376462085096791329829)
                    ·
                      rfl

theorem cell22_1955409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_1955409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955409 prefixEnd_1955409 := by exact prefixLift 1955409
  have htrace : WordTrace (prefixWord ++ tailWord_1955409) baseStart_1955409 baseEnd_1955409 := by
    simpa [prefixWord, tailWord_1955409, baseEnd_1955409] using wordTrace_append hprefix tailTrace_1955409
  have hstable : (prefixWord ++ tailWord_1955409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955409).length < 2 ^ (prefixWord ++ tailWord_1955409).sum := by decide
  have hdescent : baseEnd_1955409 < baseStart_1955409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955456 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 2, 3]
def baseStart_1955456 : Nat := 118140960795 + 1955456 * 2 ^ 59
def prefixEnd_1955456 : Nat := 4983230072969 + 3 ^ 40 * 1955456 * 2
def baseEnd_1955456 : Nat := 669392551145604335404685

theorem tailTrace_1955456 : CollatzResearch.WordTrace tailWord_1955456 prefixEnd_1955456 669392551145604335404685 := by
  unfold tailWord_1955456
  simp only [CollatzResearch.WordTrace]
  refine ⟨35660669801862176070787111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47547559735816234761049481 35660669801862176070787111)
  ·
    refine ⟨53491004702793264106180667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35660669801862176070787111 53491004702793264106180667)
    ·
      refine ⟨80236507054189896159271001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53491004702793264106180667 80236507054189896159271001)
      ·
        refine ⟨60177380290642422119453251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80236507054189896159271001 60177380290642422119453251)
        ·
          refine ⟨90266070435963633179179877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60177380290642422119453251 90266070435963633179179877)
          ·
            refine ⟨16924888206743181221096227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90266070435963633179179877 16924888206743181221096227)
            ·
              refine ⟨25387332310114771831644341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16924888206743181221096227 25387332310114771831644341)
              ·
                refine ⟨2380062404073259859216657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25387332310114771831644341 2380062404073259859216657)
                ·
                  refine ⟨1785046803054944894412493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2380062404073259859216657 1785046803054944894412493)
                  ·
                    refine ⟨669392551145604335404685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785046803054944894412493 669392551145604335404685)
                    ·
                      rfl

theorem cell22_1955456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2, 3].length) (baseStart_1955456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955456 prefixEnd_1955456 := by exact prefixLift 1955456
  have htrace : WordTrace (prefixWord ++ tailWord_1955456) baseStart_1955456 baseEnd_1955456 := by
    simpa [prefixWord, tailWord_1955456, baseEnd_1955456] using wordTrace_append hprefix tailTrace_1955456
  have hstable : (prefixWord ++ tailWord_1955456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955456).length < 2 ^ (prefixWord ++ tailWord_1955456).sum := by decide
  have hdescent : baseEnd_1955456 < baseStart_1955456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955486 : List Nat := [4, 3, 1, 1, 1, 3, 9]
def baseStart_1955486 : Nat := 118140960795 + 1955486 * 2 ^ 59
def prefixEnd_1955486 : Nat := 4983230072969 + 3 ^ 40 * 1955486 * 2
def baseEnd_1955486 : Nat := 24792697065136824339059

theorem tailTrace_1955486 : CollatzResearch.WordTrace tailWord_1955486 prefixEnd_1955486 24792697065136824339059 := by
  unfold tailWord_1955486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915304224201958408145789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47548289195743778176777541 8915304224201958408145789)
  ·
    refine ⟨3343239084075734403054671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8915304224201958408145789 3343239084075734403054671)
    ·
      refine ⟨5014858626113601604582007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3343239084075734403054671 5014858626113601604582007)
      ·
        refine ⟨7522287939170402406873011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5014858626113601604582007 7522287939170402406873011)
        ·
          refine ⟨11283431908755603610309517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7522287939170402406873011 11283431908755603610309517)
          ·
            refine ⟨4231286965783351353866069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11283431908755603610309517 4231286965783351353866069)
            ·
              refine ⟨24792697065136824339059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4231286965783351353866069 24792697065136824339059)
              ·
                rfl

theorem cell22_1955486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 9].length) (baseStart_1955486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955486 prefixEnd_1955486 := by exact prefixLift 1955486
  have htrace : WordTrace (prefixWord ++ tailWord_1955486) baseStart_1955486 baseEnd_1955486 := by
    simpa [prefixWord, tailWord_1955486, baseEnd_1955486] using wordTrace_append hprefix tailTrace_1955486
  have hstable : (prefixWord ++ tailWord_1955486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955486).length < 2 ^ (prefixWord ++ tailWord_1955486).sum := by decide
  have hdescent : baseEnd_1955486 < baseStart_1955486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955490 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1955490 : Nat := 118140960795 + 1955490 * 2 ^ 59
def prefixEnd_1955490 : Nat := 4983230072969 + 3 ^ 40 * 1955490 * 2
def baseEnd_1955490 : Nat := 669404190040439580054581

theorem tailTrace_1955490 : CollatzResearch.WordTrace tailWord_1955490 prefixEnd_1955490 669404190040439580054581 := by
  unfold tailWord_1955490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17830644921400293987077981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47548386457067450632207949 17830644921400293987077981)
  ·
    refine ⟨6686491845525110245154243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17830644921400293987077981 6686491845525110245154243)
    ·
      refine ⟨10029737768287665367731365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6686491845525110245154243 10029737768287665367731365)
      ·
        refine ⟨1880575831553937256449631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10029737768287665367731365 1880575831553937256449631)
        ·
          refine ⟨2820863747330905884674447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1880575831553937256449631 2820863747330905884674447)
          ·
            refine ⟨4231295620996358827011671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820863747330905884674447 4231295620996358827011671)
            ·
              refine ⟨6346943431494538240517507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231295620996358827011671 6346943431494538240517507)
              ·
                refine ⟨9520415147241807360776261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6346943431494538240517507 9520415147241807360776261)
                ·
                  refine ⟨1785077840107838880145549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9520415147241807360776261 1785077840107838880145549)
                  ·
                    refine ⟨669404190040439580054581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785077840107838880145549 669404190040439580054581)
                    ·
                      rfl

theorem cell22_1955490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1955490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955490 prefixEnd_1955490 := by exact prefixLift 1955490
  have htrace : WordTrace (prefixWord ++ tailWord_1955490) baseStart_1955490 baseEnd_1955490 := by
    simpa [prefixWord, tailWord_1955490, baseEnd_1955490] using wordTrace_append hprefix tailTrace_1955490
  have hstable : (prefixWord ++ tailWord_1955490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955490).length < 2 ^ (prefixWord ++ tailWord_1955490).sum := by decide
  have hdescent : baseEnd_1955490 < baseStart_1955490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955518 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_1955518 : Nat := 118140960795 + 1955518 * 2 ^ 59
def prefixEnd_1955518 : Nat := 4983230072969 + 3 ^ 40 * 1955518 * 2
def baseEnd_1955518 : Nat := 669413775012656840354495

theorem tailTrace_1955518 : CollatzResearch.WordTrace tailWord_1955518 prefixEnd_1955518 669413775012656840354495 := by
  unfold tailWord_1955518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915450116187467091291401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47549067286333157820220805 8915450116187467091291401)
  ·
    refine ⟨6686587587140600318468551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8915450116187467091291401 6686587587140600318468551)
    ·
      refine ⟨10029881380710900477702827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6686587587140600318468551 10029881380710900477702827)
      ·
        refine ⟨15044822071066350716554241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10029881380710900477702827 15044822071066350716554241)
        ·
          refine ⟨11283616553299763037415681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15044822071066350716554241 11283616553299763037415681)
          ·
            refine ⟨8462712414974822278061761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11283616553299763037415681 8462712414974822278061761)
            ·
              refine ⟨6347034311231116708546321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8462712414974822278061761 6347034311231116708546321)
              ·
                refine ⟨4760275733423337531409741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6347034311231116708546321 4760275733423337531409741)
                ·
                  refine ⟨1785103400033751574278653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4760275733423337531409741 1785103400033751574278653)
                  ·
                    refine ⟨669413775012656840354495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785103400033751574278653 669413775012656840354495)
                    ·
                      rfl

theorem cell22_1955518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_1955518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955518 prefixEnd_1955518 := by exact prefixLift 1955518
  have htrace : WordTrace (prefixWord ++ tailWord_1955518) baseStart_1955518 baseEnd_1955518 := by
    simpa [prefixWord, tailWord_1955518, baseEnd_1955518] using wordTrace_append hprefix tailTrace_1955518
  have hstable : (prefixWord ++ tailWord_1955518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955518).length < 2 ^ (prefixWord ++ tailWord_1955518).sum := by decide
  have hdescent : baseEnd_1955518 < baseStart_1955518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955565 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 5]
def baseStart_1955565 : Nat := 118140960795 + 1955565 * 2 ^ 59
def prefixEnd_1955565 : Nat := 4983230072969 + 3 ^ 40 * 1955565 * 2
def baseEnd_1955565 : Nat := 223143288024388128143117

theorem tailTrace_1955565 : CollatzResearch.WordTrace tailWord_1955565 prefixEnd_1955565 223143288024388128143117 := by
  unfold tailWord_1955565
  simp only [CollatzResearch.WordTrace]
  refine ⟨71325315160329463757292149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47550210106886309171528099 71325315160329463757292149)
  ·
    refine ⟨6686748296280887227246139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71325315160329463757292149 6686748296280887227246139)
    ·
      refine ⟨10030122444421330840869209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6686748296280887227246139 10030122444421330840869209)
      ·
        refine ⟨7522591833315998130651907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10030122444421330840869209 7522591833315998130651907)
        ·
          refine ⟨11283887749973997195977861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7522591833315998130651907 11283887749973997195977861)
          ·
            refine ⟨2115728953120124474245849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11283887749973997195977861 2115728953120124474245849)
            ·
              refine ⟨1586796714840093355684387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2115728953120124474245849 1586796714840093355684387)
              ·
                refine ⟨2380195072260140033526581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586796714840093355684387 2380195072260140033526581)
                ·
                  refine ⟨223143288024388128143117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2380195072260140033526581 223143288024388128143117)
                  ·
                    rfl

theorem cell22_1955565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_1955565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955565 prefixEnd_1955565 := by exact prefixLift 1955565
  have htrace : WordTrace (prefixWord ++ tailWord_1955565) baseStart_1955565 baseEnd_1955565 := by
    simpa [prefixWord, tailWord_1955565, baseEnd_1955565] using wordTrace_append hprefix tailTrace_1955565
  have hstable : (prefixWord ++ tailWord_1955565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955565).length < 2 ^ (prefixWord ++ tailWord_1955565).sum := by decide
  have hdescent : baseEnd_1955565 < baseStart_1955565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955608 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 2, 3]
def baseStart_1955608 : Nat := 118140960795 + 1955608 * 2 ^ 59
def prefixEnd_1955608 : Nat := 4983230072969 + 3 ^ 40 * 1955608 * 2
def baseEnd_1955608 : Nat := 669444583851926605604219

theorem tailTrace_1955608 : CollatzResearch.WordTrace tailWord_1955608 prefixEnd_1955608 669444583851926605604219 := by
  unfold tailWord_1955608
  simp only [CollatzResearch.WordTrace]
  refine ⟨35663441749586841050553739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47551255666115788067404985 35663441749586841050553739)
  ·
    refine ⟨53495162624380261575830609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35663441749586841050553739 53495162624380261575830609)
    ·
      refine ⟨40121371968285196181872957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53495162624380261575830609 40121371968285196181872957)
      ·
        refine ⟨15045514488106948568202359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40121371968285196181872957 15045514488106948568202359)
        ·
          refine ⟨22568271732160422852303539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15045514488106948568202359 22568271732160422852303539)
          ·
            refine ⟨33852407598240634278455309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22568271732160422852303539 33852407598240634278455309)
            ·
              refine ⟨12694652849340237854420741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33852407598240634278455309 12694652849340237854420741)
              ·
                refine ⟨2380247409251294597703889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12694652849340237854420741 2380247409251294597703889)
                ·
                  refine ⟨1785185556938470948277917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2380247409251294597703889 1785185556938470948277917)
                  ·
                    refine ⟨669444583851926605604219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785185556938470948277917 669444583851926605604219)
                    ·
                      rfl

theorem cell22_1955608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_1955608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955608 prefixEnd_1955608 := by exact prefixLift 1955608
  have htrace : WordTrace (prefixWord ++ tailWord_1955608) baseStart_1955608 baseEnd_1955608 := by
    simpa [prefixWord, tailWord_1955608, baseEnd_1955608] using wordTrace_append hprefix tailTrace_1955608
  have hstable : (prefixWord ++ tailWord_1955608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955608).length < 2 ^ (prefixWord ++ tailWord_1955608).sum := by decide
  have hdescent : baseEnd_1955608 < baseStart_1955608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955610 : List Nat := [3, 1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_1955610 : Nat := 118140960795 + 1955610 * 2 ^ 59
def prefixEnd_1955610 : Nat := 4983230072969 + 3 ^ 40 * 1955610 * 2
def baseEnd_1955610 : Nat := 223148422830933089018071

theorem tailTrace_1955610 : CollatzResearch.WordTrace tailWord_1955610 prefixEnd_1955610 223148422830933089018071 := by
  unfold tailWord_1955610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17831739111291609110670071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47551304296777624295120189 17831739111291609110670071)
  ·
    refine ⟨26747608666937413666005107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17831739111291609110670071 26747608666937413666005107)
    ·
      refine ⟨40121413000406120499007661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26747608666937413666005107 40121413000406120499007661)
      ·
        refine ⟨15045529875152295187127873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40121413000406120499007661 15045529875152295187127873)
        ·
          refine ⟨11284147406364221390345905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15045529875152295187127873 11284147406364221390345905)
          ·
            refine ⟨8463110554773166042759429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11284147406364221390345905 8463110554773166042759429)
            ·
              refine ⟨1586833229019968633017393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8463110554773166042759429 1586833229019968633017393)
              ·
                refine ⟨1190124921764976474763045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586833229019968633017393 1190124921764976474763045)
                ·
                  refine ⟨223148422830933089018071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1190124921764976474763045 223148422830933089018071)
                  ·
                    rfl

theorem cell22_1955610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_1955610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955610 prefixEnd_1955610 := by exact prefixLift 1955610
  have htrace : WordTrace (prefixWord ++ tailWord_1955610) baseStart_1955610 baseEnd_1955610 := by
    simpa [prefixWord, tailWord_1955610, baseEnd_1955610] using wordTrace_append hprefix tailTrace_1955610
  have hstable : (prefixWord ++ tailWord_1955610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955610).length < 2 ^ (prefixWord ++ tailWord_1955610).sum := by decide
  have hdescent : baseEnd_1955610 < baseStart_1955610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955621 : List Nat := [1, 3, 1, 2, 3, 2, 3, 7]
def baseStart_1955621 : Nat := 118140960795 + 1955621 * 2 ^ 59
def prefixEnd_1955621 : Nat := 4983230072969 + 3 ^ 40 * 1955621 * 2
def baseEnd_1955621 : Nat := 74383226001955433892131

theorem tailTrace_1955621 : CollatzResearch.WordTrace tailWord_1955621 prefixEnd_1955621 74383226001955433892131 := by
  unfold tailWord_1955621
  simp only [CollatzResearch.WordTrace]
  refine ⟨71327357648126585321330717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47551571765417723547553811 71327357648126585321330717)
  ·
    refine ⟨26747759118047469495499019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71327357648126585321330717 26747759118047469495499019)
    ·
      refine ⟨40121638677071204243248529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26747759118047469495499019 40121638677071204243248529)
      ·
        refine ⟨30091229007803403182436397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40121638677071204243248529 30091229007803403182436397)
        ·
          refine ⟨11284210877926276193413649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30091229007803403182436397 11284210877926276193413649)
          ·
            refine ⟨8463158158444707145060237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11284210877926276193413649 8463158158444707145060237)
            ·
              refine ⟨3173684309416765179397589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8463158158444707145060237 3173684309416765179397589)
              ·
                refine ⟨74383226001955433892131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3173684309416765179397589 74383226001955433892131)
                ·
                  rfl

theorem cell22_1955621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 7].length) (baseStart_1955621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955621 prefixEnd_1955621 := by exact prefixLift 1955621
  have htrace : WordTrace (prefixWord ++ tailWord_1955621) baseStart_1955621 baseEnd_1955621 := by
    simpa [prefixWord, tailWord_1955621, baseEnd_1955621] using wordTrace_append hprefix tailTrace_1955621
  have hstable : (prefixWord ++ tailWord_1955621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955621).length < 2 ^ (prefixWord ++ tailWord_1955621).sum := by decide
  have hdescent : baseEnd_1955621 < baseStart_1955621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955681 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1955681 : Nat := 118140960795 + 1955681 * 2 ^ 59
def prefixEnd_1955681 : Nat := 4983230072969 + 3 ^ 40 * 1955681 * 2
def baseEnd_1955681 : Nat := 669469573243778748528995

theorem tailTrace_1955681 : CollatzResearch.WordTrace tailWord_1955681 prefixEnd_1955681 669469573243778748528995 := by
  unfold tailWord_1955681
  simp only [CollatzResearch.WordTrace]
  refine ⟨71329546027909215568514897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47553030685272810379009931 71329546027909215568514897)
  ·
    refine ⟨53497159520931911676386173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71329546027909215568514897 53497159520931911676386173)
    ·
      refine ⟨20061434820349466878644815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53497159520931911676386173 20061434820349466878644815)
      ·
        refine ⟨30092152230524200317967223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20061434820349466878644815 30092152230524200317967223)
        ·
          refine ⟨45138228345786300476950835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30092152230524200317967223 45138228345786300476950835)
          ·
            refine ⟨67707342518679450715426253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45138228345786300476950835 67707342518679450715426253)
            ·
              refine ⟨25390253444504794018284845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67707342518679450715426253 25390253444504794018284845)
              ·
                refine ⟨9521345041689297756856817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25390253444504794018284845 9521345041689297756856817)
                ·
                  refine ⟨7141008781266973317642613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9521345041689297756856817 7141008781266973317642613)
                  ·
                    refine ⟨669469573243778748528995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7141008781266973317642613 669469573243778748528995)
                    ·
                      rfl

theorem cell22_1955681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1955681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955681 prefixEnd_1955681 := by exact prefixLift 1955681
  have htrace : WordTrace (prefixWord ++ tailWord_1955681) baseStart_1955681 baseEnd_1955681 := by
    simpa [prefixWord, tailWord_1955681, baseEnd_1955681] using wordTrace_append hprefix tailTrace_1955681
  have hstable : (prefixWord ++ tailWord_1955681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955681).length < 2 ^ (prefixWord ++ tailWord_1955681).sum := by decide
  have hdescent : baseEnd_1955681 < baseStart_1955681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955734 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1955734 : Nat := 118140960795 + 1955734 * 2 ^ 59
def prefixEnd_1955734 : Nat := 4983230072969 + 3 ^ 40 * 1955734 * 2
def baseEnd_1955734 : Nat := 223162572075634758984611

theorem tailTrace_1955734 : CollatzResearch.WordTrace tailWord_1955734 prefixEnd_1955734 223162572075634758984611 := by
  unfold tailWord_1955734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4458217443544825351262141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47554319397811470413462837 4458217443544825351262141)
  ·
    refine ⟨1671831541329309506723303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4458217443544825351262141 1671831541329309506723303)
    ·
      refine ⟨2507747311993964260084955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1671831541329309506723303 2507747311993964260084955)
      ·
        refine ⟨3761620967990946390127433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507747311993964260084955 3761620967990946390127433)
        ·
          refine ⟨2821215725993209792595575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3761620967990946390127433 2821215725993209792595575)
          ·
            refine ⟨4231823588989814688893363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821215725993209792595575 4231823588989814688893363)
            ·
              refine ⟨6347735383484722033340045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231823588989814688893363 6347735383484722033340045)
              ·
                refine ⟨2380400768806770762502517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6347735383484722033340045 2380400768806770762502517)
                ·
                  refine ⟨223162572075634758984611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2380400768806770762502517 223162572075634758984611)
                  ·
                    rfl

theorem cell22_1955734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1955734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955734 prefixEnd_1955734 := by exact prefixLift 1955734
  have htrace : WordTrace (prefixWord ++ tailWord_1955734) baseStart_1955734 baseEnd_1955734 := by
    simpa [prefixWord, tailWord_1955734, baseEnd_1955734] using wordTrace_append hprefix tailTrace_1955734
  have hstable : (prefixWord ++ tailWord_1955734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955734).length < 2 ^ (prefixWord ++ tailWord_1955734).sum := by decide
  have hdescent : baseEnd_1955734 < baseStart_1955734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955818 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_1955818 : Nat := 118140960795 + 1955818 * 2 ^ 59
def prefixEnd_1955818 : Nat := 4983230072969 + 3 ^ 40 * 1955818 * 2
def baseEnd_1955818 : Nat := 223172157047852019284525

theorem tailTrace_1955818 : CollatzResearch.WordTrace tailWord_1955818 prefixEnd_1955818 223172157047852019284525 := by
  unfold tailWord_1955818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17833635707103221991563027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47556361885608591977501405 17833635707103221991563027)
  ·
    refine ⟨26750453560654832987344541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17833635707103221991563027 26750453560654832987344541)
    ·
      refine ⟨10031420085245562370254203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26750453560654832987344541 10031420085245562370254203)
      ·
        refine ⟨15047130127868343555381305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10031420085245562370254203 15047130127868343555381305)
        ·
          refine ⟨11285347595901257666535979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15047130127868343555381305 11285347595901257666535979)
          ·
            refine ⟨16928021393851886499803969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11285347595901257666535979 16928021393851886499803969)
            ·
              refine ⟨12696016045388914874852977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16928021393851886499803969 12696016045388914874852977)
              ·
                refine ⟨9522012034041686156139733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12696016045388914874852977 9522012034041686156139733)
                ·
                  refine ⟨223172157047852019284525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9522012034041686156139733 223172157047852019284525)
                  ·
                    rfl

theorem cell22_1955818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_1955818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955818 prefixEnd_1955818 := by exact prefixLift 1955818
  have htrace : WordTrace (prefixWord ++ tailWord_1955818) baseStart_1955818 baseEnd_1955818 := by
    simpa [prefixWord, tailWord_1955818, baseEnd_1955818] using wordTrace_append hprefix tailTrace_1955818
  have hstable : (prefixWord ++ tailWord_1955818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955818).length < 2 ^ (prefixWord ++ tailWord_1955818).sum := by decide
  have hdescent : baseEnd_1955818 < baseStart_1955818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955833 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_1955833 : Nat := 118140960795 + 1955833 * 2 ^ 59
def prefixEnd_1955833 : Nat := 4983230072969 + 3 ^ 40 * 1955833 * 2
def baseEnd_1955833 : Nat := 669521605950101018728529

theorem tailTrace_1955833 : CollatzResearch.WordTrace tailWord_1955833 prefixEnd_1955833 669521605950101018728529 := by
  unfold tailWord_1955833
  simp only [CollatzResearch.WordTrace]
  refine ⟨71335089923358545528048153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47556726615572363685365435 71335089923358545528048153)
  ·
    refine ⟨53501317442518909146036115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71335089923358545528048153 53501317442518909146036115)
    ·
      refine ⟨80251976163778363719054173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53501317442518909146036115 80251976163778363719054173)
      ·
        refine ⟨30094491061416886394645315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80251976163778363719054173 30094491061416886394645315)
        ·
          refine ⟨45141736592125329591967973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30094491061416886394645315 45141736592125329591967973)
          ·
            refine ⟨8464075611023499298493995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45141736592125329591967973 8464075611023499298493995)
            ·
              refine ⟨12696113416535248947740993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464075611023499298493995 12696113416535248947740993)
              ·
                refine ⟨9522085062401436710805745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12696113416535248947740993 9522085062401436710805745)
                ·
                  refine ⟨7141563796801077533104309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9522085062401436710805745 7141563796801077533104309)
                  ·
                    refine ⟨669521605950101018728529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7141563796801077533104309 669521605950101018728529)
                    ·
                      rfl

theorem cell22_1955833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_1955833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955833 prefixEnd_1955833 := by exact prefixLift 1955833
  have htrace : WordTrace (prefixWord ++ tailWord_1955833) baseStart_1955833 baseEnd_1955833 := by
    simpa [prefixWord, tailWord_1955833, baseEnd_1955833] using wordTrace_append hprefix tailTrace_1955833
  have hstable : (prefixWord ++ tailWord_1955833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955833).length < 2 ^ (prefixWord ++ tailWord_1955833).sum := by decide
  have hdescent : baseEnd_1955833 < baseStart_1955833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955882 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1955882 : Nat := 118140960795 + 1955882 * 2 ^ 59
def prefixEnd_1955882 : Nat := 4983230072969 + 3 ^ 40 * 1955882 * 2
def baseEnd_1955882 : Nat := 669538379651481224253379

theorem tailTrace_1955882 : CollatzResearch.WordTrace tailWord_1955882 prefixEnd_1955882 669538379651481224253379 := by
  unfold tailWord_1955882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17834219275045256724145475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47557918066787351264387933 17834219275045256724145475)
  ·
    refine ⟨26751328912567885086218213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17834219275045256724145475 26751328912567885086218213)
    ·
      refine ⟨5015874171106478453665915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26751328912567885086218213 5015874171106478453665915)
      ·
        refine ⟨7523811256659717680498873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5015874171106478453665915 7523811256659717680498873)
        ·
          refine ⟨5642858442494788260374155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7523811256659717680498873 5642858442494788260374155)
          ·
            refine ⟨8464287663742182390561233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642858442494788260374155 8464287663742182390561233)
            ·
              refine ⟨6348215747806636792920925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8464287663742182390561233 6348215747806636792920925)
              ·
                refine ⟨2380580905427488797345347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6348215747806636792920925 2380580905427488797345347)
                ·
                  refine ⟨3570871358141233196018021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380580905427488797345347 3570871358141233196018021)
                  ·
                    refine ⟨669538379651481224253379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3570871358141233196018021 669538379651481224253379)
                    ·
                      rfl

theorem cell22_1955882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1955882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955882 prefixEnd_1955882 := by exact prefixLift 1955882
  have htrace : WordTrace (prefixWord ++ tailWord_1955882) baseStart_1955882 baseEnd_1955882 := by
    simpa [prefixWord, tailWord_1955882, baseEnd_1955882] using wordTrace_append hprefix tailTrace_1955882
  have hstable : (prefixWord ++ tailWord_1955882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955882).length < 2 ^ (prefixWord ++ tailWord_1955882).sum := by decide
  have hdescent : baseEnd_1955882 < baseStart_1955882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955895 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 4, 3]
def baseStart_1955895 : Nat := 118140960795 + 1955895 * 2 ^ 59
def prefixEnd_1955895 : Nat := 4983230072969 + 3 ^ 40 * 1955895 * 2
def baseEnd_1955895 : Nat := 669542829817153523678339

theorem tailTrace_1955895 : CollatzResearch.WordTrace tailWord_1955895 prefixEnd_1955895 669542829817153523678339 := by
  unfold tailWord_1955895
  simp only [CollatzResearch.WordTrace]
  refine ⟨71337351249133930116805139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47558234166089286744536759 71337351249133930116805139)
  ·
    refine ⟨107006026873700895175207709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71337351249133930116805139 107006026873700895175207709)
    ·
      refine ⟨40127260077637835690702891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107006026873700895175207709 40127260077637835690702891)
      ·
        refine ⟨60190890116456753536054337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40127260077637835690702891 60190890116456753536054337)
        ·
          refine ⟨45143167587342565152040753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60190890116456753536054337 45143167587342565152040753)
          ·
            refine ⟨33857375690506923864030565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45143167587342565152040753 33857375690506923864030565)
            ·
              refine ⟨6348257941970048224505731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33857375690506923864030565 6348257941970048224505731)
              ·
                refine ⟨9522386912955072336758597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6348257941970048224505731 9522386912955072336758597)
                ·
                  refine ⟨1785447546179076063142237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9522386912955072336758597 1785447546179076063142237)
                  ·
                    refine ⟨669542829817153523678339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785447546179076063142237 669542829817153523678339)
                    ·
                      rfl

theorem cell22_1955895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_1955895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955895 prefixEnd_1955895 := by exact prefixLift 1955895
  have htrace : WordTrace (prefixWord ++ tailWord_1955895) baseStart_1955895 baseEnd_1955895 := by
    simpa [prefixWord, tailWord_1955895, baseEnd_1955895] using wordTrace_append hprefix tailTrace_1955895
  have hstable : (prefixWord ++ tailWord_1955895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955895).length < 2 ^ (prefixWord ++ tailWord_1955895).sum := by decide
  have hdescent : baseEnd_1955895 < baseStart_1955895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955897 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 6]
def baseStart_1955897 : Nat := 118140960795 + 1955897 * 2 ^ 59
def prefixEnd_1955897 : Nat := 4983230072969 + 3 ^ 40 * 1955897 * 2
def baseEnd_1955897 : Nat := 223181171486008728376111

theorem tailTrace_1955897 : CollatzResearch.WordTrace tailWord_1955897 prefixEnd_1955897 223181171486008728376111 := by
  unfold tailWord_1955897
  simp only [CollatzResearch.WordTrace]
  refine ⟨71337424195126684458377945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47558282796751122972251963 71337424195126684458377945)
  ·
    refine ⟨53503068146345013343783459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71337424195126684458377945 53503068146345013343783459)
    ·
      refine ⟨80254602219517520015675189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53503068146345013343783459 80254602219517520015675189)
      ·
        refine ⟨7523868958079767501469549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80254602219517520015675189 7523868958079767501469549)
        ·
          refine ⟨2821450859279912813051081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7523868958079767501469549 2821450859279912813051081)
          ·
            refine ⟨2116088144459934609788311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821450859279912813051081 2116088144459934609788311)
            ·
              refine ⟨3174132216689901914682467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116088144459934609788311 3174132216689901914682467)
              ·
                refine ⟨4761198325034852872023701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174132216689901914682467 4761198325034852872023701)
                ·
                  refine ⟨223181171486008728376111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4761198325034852872023701 223181171486008728376111)
                  ·
                    rfl

theorem cell22_1955897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 6].length) (baseStart_1955897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955897 prefixEnd_1955897 := by exact prefixLift 1955897
  have htrace : WordTrace (prefixWord ++ tailWord_1955897) baseStart_1955897 baseEnd_1955897 := by
    simpa [prefixWord, tailWord_1955897, baseEnd_1955897] using wordTrace_append hprefix tailTrace_1955897
  have hstable : (prefixWord ++ tailWord_1955897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955897).length < 2 ^ (prefixWord ++ tailWord_1955897).sum := by decide
  have hdescent : baseEnd_1955897 < baseStart_1955897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955991 : List Nat := [1, 1, 3, 3, 4, 1, 2, 3, 1, 3]
def baseStart_1955991 : Nat := 118140960795 + 1955991 * 2 ^ 59
def prefixEnd_1955991 : Nat := 4983230072969 + 3 ^ 40 * 1955991 * 2
def baseEnd_1955991 : Nat := 669575692579041273278045

theorem tailTrace_1955991 : CollatzResearch.WordTrace tailWord_1955991 prefixEnd_1955991 669575692579041273278045 := by
  unfold tailWord_1955991
  simp only [CollatzResearch.WordTrace]
  refine ⟨71340852656786138512299827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47560568437857425674866551 71340852656786138512299827)
  ·
    refine ⟨107011278985179207768449741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71340852656786138512299827 107011278985179207768449741)
    ·
      refine ⟨40129229619442202913168653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107011278985179207768449741 40129229619442202913168653)
      ·
        refine ⟨15048461107290826092438245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40129229619442202913168653 15048461107290826092438245)
        ·
          refine ⟨2821586457617029892332171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15048461107290826092438245 2821586457617029892332171)
          ·
            refine ⟨4232379686425544838498257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821586457617029892332171 4232379686425544838498257)
            ·
              refine ⟨3174284764819158628873693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4232379686425544838498257 3174284764819158628873693)
              ·
                refine ⟨1190356786807184485827635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3174284764819158628873693 1190356786807184485827635)
                ·
                  refine ⟨1785535180210776728741453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190356786807184485827635 1785535180210776728741453)
                  ·
                    refine ⟨669575692579041273278045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785535180210776728741453 669575692579041273278045)
                    ·
                      rfl

theorem cell22_1955991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_1955991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1955991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1955991 prefixEnd_1955991 := by exact prefixLift 1955991
  have htrace : WordTrace (prefixWord ++ tailWord_1955991) baseStart_1955991 baseEnd_1955991 := by
    simpa [prefixWord, tailWord_1955991, baseEnd_1955991] using wordTrace_append hprefix tailTrace_1955991
  have hstable : (prefixWord ++ tailWord_1955991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955991).length < 2 ^ (prefixWord ++ tailWord_1955991).sum := by decide
  have hdescent : baseEnd_1955991 < baseStart_1955991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956002 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1956002 : Nat := 118140960795 + 1956002 * 2 ^ 59
def prefixEnd_1956002 : Nat := 4983230072969 + 3 ^ 40 * 1956002 * 2
def baseEnd_1956002 : Nat := 669579458103840911253011

theorem tailTrace_1956002 : CollatzResearch.WordTrace tailWord_1956002 prefixEnd_1956002 669579458103840911253011 := by
  unfold tailWord_1956002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17835313464936571847737565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47560835906497524927300173 17835313464936571847737565)
  ·
    refine ⟨6688242549351214442901587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17835313464936571847737565 6688242549351214442901587)
    ·
      refine ⟨10032363824026821664352381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6688242549351214442901587 10032363824026821664352381)
      ·
        refine ⟨3762136434010058124132143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10032363824026821664352381 3762136434010058124132143)
        ·
          refine ⟨5643204651015087186198215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3762136434010058124132143 5643204651015087186198215)
          ·
            refine ⟨8464806976522630779297323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5643204651015087186198215 8464806976522630779297323)
            ·
              refine ⟨12697210464783946168945985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464806976522630779297323 12697210464783946168945985)
              ·
                refine ⟨9522907848587959626709489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12697210464783946168945985 9522907848587959626709489)
                ·
                  refine ⟨7142180886440969720032117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9522907848587959626709489 7142180886440969720032117)
                  ·
                    refine ⟨669579458103840911253011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7142180886440969720032117 669579458103840911253011)
                    ·
                      rfl

theorem cell22_1956002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1956002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956002 prefixEnd_1956002 := by exact prefixLift 1956002
  have htrace : WordTrace (prefixWord ++ tailWord_1956002) baseStart_1956002 baseEnd_1956002 := by
    simpa [prefixWord, tailWord_1956002, baseEnd_1956002] using wordTrace_append hprefix tailTrace_1956002
  have hstable : (prefixWord ++ tailWord_1956002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956002).length < 2 ^ (prefixWord ++ tailWord_1956002).sum := by decide
  have hdescent : baseEnd_1956002 < baseStart_1956002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956004 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 5]
def baseStart_1956004 : Nat := 118140960795 + 1956004 * 2 ^ 59
def prefixEnd_1956004 : Nat := 4983230072969 + 3 ^ 40 * 1956004 * 2
def baseEnd_1956004 : Nat := 223193380914904524234335

theorem tailTrace_1956004 : CollatzResearch.WordTrace tailWord_1956004 prefixEnd_1956004 223193380914904524234335 := by
  unfold tailWord_1956004
  simp only [CollatzResearch.WordTrace]
  refine ⟨35670663402869520866261533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47560884537159361155015377 35670663402869520866261533)
  ·
    refine ⟨13376498776076070324848075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35670663402869520866261533 13376498776076070324848075)
    ·
      refine ⟨20064748164114105487272113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13376498776076070324848075 20064748164114105487272113)
      ·
        refine ⟨15048561123085579115454085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20064748164114105487272113 15048561123085579115454085)
        ·
          refine ⟨2821605210578546084147641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15048561123085579115454085 2821605210578546084147641)
          ·
            refine ⟨2116203907933909563110731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821605210578546084147641 2116203907933909563110731)
            ·
              refine ⟨3174305861900864344666097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116203907933909563110731 3174305861900864344666097)
              ·
                refine ⟨2380729396425648258499573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174305861900864344666097 2380729396425648258499573)
                ·
                  refine ⟨223193380914904524234335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2380729396425648258499573 223193380914904524234335)
                  ·
                    rfl

theorem cell22_1956004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_1956004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956004 prefixEnd_1956004 := by exact prefixLift 1956004
  have htrace : WordTrace (prefixWord ++ tailWord_1956004) baseStart_1956004 baseEnd_1956004 := by
    simpa [prefixWord, tailWord_1956004, baseEnd_1956004] using wordTrace_append hprefix tailTrace_1956004
  have hstable : (prefixWord ++ tailWord_1956004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956004).length < 2 ^ (prefixWord ++ tailWord_1956004).sum := by decide
  have hdescent : baseEnd_1956004 < baseStart_1956004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956021 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 5]
def baseStart_1956021 : Nat := 118140960795 + 1956021 * 2 ^ 59
def prefixEnd_1956021 : Nat := 4983230072969 + 3 ^ 40 * 1956021 * 2
def baseEnd_1956021 : Nat := 223195320730710398342651

theorem tailTrace_1956021 : CollatzResearch.WordTrace tailWord_1956021 prefixEnd_1956021 223195320730710398342651 := by
  unfold tailWord_1956021
  simp only [CollatzResearch.WordTrace]
  refine ⟨71341946846677453635891917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47561297897784969090594611 71341946846677453635891917)
  ·
    refine ⟨26753230067504045113459469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71341946846677453635891917 26753230067504045113459469)
    ·
      refine ⟨10032461275314016917547301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26753230067504045113459469 10032461275314016917547301)
      ·
        refine ⟨1881086489121378172040119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10032461275314016917547301 1881086489121378172040119)
        ·
          refine ⟨2821629733682067258060179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881086489121378172040119 2821629733682067258060179)
          ·
            refine ⟨4232444600523100887090269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821629733682067258060179 4232444600523100887090269)
            ·
              refine ⟨1587166725196162832658851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4232444600523100887090269 1587166725196162832658851)
              ·
                refine ⟨2380750087794244248988277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587166725196162832658851 2380750087794244248988277)
                ·
                  refine ⟨223195320730710398342651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2380750087794244248988277 223195320730710398342651)
                  ·
                    rfl

theorem cell22_1956021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_1956021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956021 prefixEnd_1956021 := by exact prefixLift 1956021
  have htrace : WordTrace (prefixWord ++ tailWord_1956021) baseStart_1956021 baseEnd_1956021 := by
    simpa [prefixWord, tailWord_1956021, baseEnd_1956021] using wordTrace_append hprefix tailTrace_1956021
  have hstable : (prefixWord ++ tailWord_1956021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956021).length < 2 ^ (prefixWord ++ tailWord_1956021).sum := by decide
  have hdescent : baseEnd_1956021 < baseStart_1956021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956152 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_1956152 : Nat := 118140960795 + 1956152 * 2 ^ 59
def prefixEnd_1956152 : Nat := 4983230072969 + 3 ^ 40 * 1956152 * 2
def baseEnd_1956152 : Nat := 669630806169290520002551

theorem tailTrace_1956152 : CollatzResearch.WordTrace tailWord_1956152 prefixEnd_1956152 669630806169290520002551 := by
  unfold tailWord_1956152
  simp only [CollatzResearch.WordTrace]
  refine ⟨35673362404601431504455355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47564483206135242005940473 35673362404601431504455355)
  ·
    refine ⟨53510043606902147256683033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35673362404601431504455355 53510043606902147256683033)
    ·
      refine ⟨40132532705176610442512275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53510043606902147256683033 40132532705176610442512275)
      ·
        refine ⟨60198799057764915663768413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40132532705176610442512275 60198799057764915663768413)
        ·
          refine ⟨22574549646661843373913155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60198799057764915663768413 22574549646661843373913155)
          ·
            refine ⟨33861824469992765060869733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22574549646661843373913155 33861824469992765060869733)
            ·
              refine ⟨6349092088123643448913075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33861824469992765060869733 6349092088123643448913075)
              ·
                refine ⟨9523638132185465173369613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6349092088123643448913075 9523638132185465173369613)
                ·
                  refine ⟨3571364299569549440013605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9523638132185465173369613 3571364299569549440013605)
                  ·
                    refine ⟨669630806169290520002551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3571364299569549440013605 669630806169290520002551)
                    ·
                      rfl

theorem cell22_1956152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_1956152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956152 prefixEnd_1956152 := by exact prefixLift 1956152
  have htrace : WordTrace (prefixWord ++ tailWord_1956152) baseStart_1956152 baseEnd_1956152 := by
    simpa [prefixWord, tailWord_1956152, baseEnd_1956152] using wordTrace_append hprefix tailTrace_1956152
  have hstable : (prefixWord ++ tailWord_1956152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956152).length < 2 ^ (prefixWord ++ tailWord_1956152).sum := by decide
  have hdescent : baseEnd_1956152 < baseStart_1956152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956197 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_1956197 : Nat := 118140960795 + 1956197 * 2 ^ 59
def prefixEnd_1956197 : Nat := 4983230072969 + 3 ^ 40 * 1956197 * 2
def baseEnd_1956197 : Nat := 669646210588925402627413

theorem tailTrace_1956197 : CollatzResearch.WordTrace tailWord_1956197 prefixEnd_1956197 669646210588925402627413 := by
  unfold tailWord_1956197
  simp only [CollatzResearch.WordTrace]
  refine ⟨71348366094039835694298845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47565577396026557129532563 71348366094039835694298845)
  ·
    refine ⟨26755637285264938385362067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71348366094039835694298845 26755637285264938385362067)
    ·
      refine ⟨40133455927897407578043101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26755637285264938385362067 40133455927897407578043101)
      ·
        refine ⟨15050045972961527841766163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40133455927897407578043101 15050045972961527841766163)
        ·
          refine ⟨22575068959442291762649245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15050045972961527841766163 22575068959442291762649245)
          ·
            refine ⟨8465650859790859410993467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22575068959442291762649245 8465650859790859410993467)
            ·
              refine ⟨12698476289686289116490201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465650859790859410993467 12698476289686289116490201)
              ·
                refine ⟨9523857217264716837367651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12698476289686289116490201 9523857217264716837367651)
                ·
                  refine ⟨14285785825897075256051477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9523857217264716837367651 14285785825897075256051477)
                  ·
                    refine ⟨669646210588925402627413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14285785825897075256051477 669646210588925402627413)
                    ·
                      rfl

theorem cell22_1956197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_1956197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956197 prefixEnd_1956197 := by exact prefixLift 1956197
  have htrace : WordTrace (prefixWord ++ tailWord_1956197) baseStart_1956197 baseEnd_1956197 := by
    simpa [prefixWord, tailWord_1956197, baseEnd_1956197] using wordTrace_append hprefix tailTrace_1956197
  have hstable : (prefixWord ++ tailWord_1956197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956197).length < 2 ^ (prefixWord ++ tailWord_1956197).sum := by decide
  have hdescent : baseEnd_1956197 < baseStart_1956197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956199 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1956199 : Nat := 118140960795 + 1956199 * 2 ^ 59
def prefixEnd_1956199 : Nat := 4983230072969 + 3 ^ 40 * 1956199 * 2
def baseEnd_1956199 : Nat := 669646895229798064077407

theorem tailTrace_1956199 : CollatzResearch.WordTrace tailWord_1956199 prefixEnd_1956199 669646895229798064077407 := by
  unfold tailWord_1956199
  simp only [CollatzResearch.WordTrace]
  refine ⟨71348439040032590035871651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47565626026688393357247767 71348439040032590035871651)
  ·
    refine ⟨107022658560048885053807477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71348439040032590035871651 107022658560048885053807477)
    ·
      refine ⟨10033374240004582973794451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107022658560048885053807477 10033374240004582973794451)
      ·
        refine ⟨15050061360006874460691677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033374240004582973794451 15050061360006874460691677)
        ·
          refine ⟨5643773010002577922759379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15050061360006874460691677 5643773010002577922759379)
          ·
            refine ⟨8465659515003866884139069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5643773010002577922759379 8465659515003866884139069)
            ·
              refine ⟨3174622318126450081552151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8465659515003866884139069 3174622318126450081552151)
              ·
                refine ⟨4761933477189675122328227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174622318126450081552151 4761933477189675122328227)
                ·
                  refine ⟨7142900215784512683492341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761933477189675122328227 7142900215784512683492341)
                  ·
                    refine ⟨669646895229798064077407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7142900215784512683492341 669646895229798064077407)
                    ·
                      rfl

theorem cell22_1956199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1956199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956199 prefixEnd_1956199 := by exact prefixLift 1956199
  have htrace : WordTrace (prefixWord ++ tailWord_1956199) baseStart_1956199 baseEnd_1956199 := by
    simpa [prefixWord, tailWord_1956199, baseEnd_1956199] using wordTrace_append hprefix tailTrace_1956199
  have hstable : (prefixWord ++ tailWord_1956199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956199).length < 2 ^ (prefixWord ++ tailWord_1956199).sum := by decide
  have hdescent : baseEnd_1956199 < baseStart_1956199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956295 : List Nat := [1, 1, 4, 1, 1, 6, 2, 2, 1, 3]
def baseStart_1956295 : Nat := 118140960795 + 1956295 * 2 ^ 59
def prefixEnd_1956295 : Nat := 4983230072969 + 3 ^ 40 * 1956295 * 2
def baseEnd_1956295 : Nat := 669679757991685813677113

theorem tailTrace_1956295 : CollatzResearch.WordTrace tailWord_1956295 prefixEnd_1956295 669679757991685813677113 := by
  unfold tailWord_1956295
  simp only [CollatzResearch.WordTrace]
  refine ⟨71351940447684798431366339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47567960298456532287577559 71351940447684798431366339)
  ·
    refine ⟨107027910671527197647049509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71351940447684798431366339 107027910671527197647049509)
    ·
      refine ⟨20067733250911349558821783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107027910671527197647049509 20067733250911349558821783)
      ·
        refine ⟨30101599876367024338232675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20067733250911349558821783 30101599876367024338232675)
        ·
          refine ⟨45152399814550536507349013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30101599876367024338232675 45152399814550536507349013)
          ·
            refine ⟨2116518741307056398781985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45152399814550536507349013 2116518741307056398781985)
            ·
              refine ⟨1587389055980292299086489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116518741307056398781985 1587389055980292299086489)
              ·
                refine ⟨1190541791985219224314867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587389055980292299086489 1190541791985219224314867)
                ·
                  refine ⟨1785812687977828836472301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190541791985219224314867 1785812687977828836472301)
                  ·
                    refine ⟨669679757991685813677113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785812687977828836472301 669679757991685813677113)
                    ·
                      rfl

theorem cell22_1956295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_1956295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956295 prefixEnd_1956295 := by exact prefixLift 1956295
  have htrace : WordTrace (prefixWord ++ tailWord_1956295) baseStart_1956295 baseEnd_1956295 := by
    simpa [prefixWord, tailWord_1956295, baseEnd_1956295] using wordTrace_append hprefix tailTrace_1956295
  have hstable : (prefixWord ++ tailWord_1956295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956295).length < 2 ^ (prefixWord ++ tailWord_1956295).sum := by decide
  have hdescent : baseEnd_1956295 < baseStart_1956295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956319 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 6]
def baseStart_1956319 : Nat := 118140960795 + 1956319 * 2 ^ 59
def prefixEnd_1956319 : Nat := 4983230072969 + 3 ^ 40 * 1956319 * 2
def baseEnd_1956319 : Nat := 223229324560719250359013

theorem tailTrace_1956319 : CollatzResearch.WordTrace tailWord_1956319 prefixEnd_1956319 223229324560719250359013 := by
  unfold tailWord_1956319
  simp only [CollatzResearch.WordTrace]
  refine ⟨71352815799597850530240011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47568543866398567020160007 71352815799597850530240011)
  ·
    refine ⟨107029223699396775795360017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71352815799597850530240011 107029223699396775795360017)
    ·
      refine ⟨80271917774547581846520013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107029223699396775795360017 80271917774547581846520013)
      ·
        refine ⟨30101969165455343192445005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80271917774547581846520013 30101969165455343192445005)
        ·
          refine ⟨11288238437045753697166877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30101969165455343192445005 11288238437045753697166877)
          ·
            refine ⟨4233089413892157636437579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11288238437045753697166877 4233089413892157636437579)
            ·
              refine ⟨6349634120838236454656369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233089413892157636437579 6349634120838236454656369)
              ·
                refine ⟨4762225590628677340992277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6349634120838236454656369 4762225590628677340992277)
                ·
                  refine ⟨223229324560719250359013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4762225590628677340992277 223229324560719250359013)
                  ·
                    rfl

theorem cell22_1956319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 6].length) (baseStart_1956319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956319 prefixEnd_1956319 := by exact prefixLift 1956319
  have htrace : WordTrace (prefixWord ++ tailWord_1956319) baseStart_1956319 baseEnd_1956319 := by
    simpa [prefixWord, tailWord_1956319, baseEnd_1956319] using wordTrace_append hprefix tailTrace_1956319
  have hstable : (prefixWord ++ tailWord_1956319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956319).length < 2 ^ (prefixWord ++ tailWord_1956319).sum := by decide
  have hdescent : baseEnd_1956319 < baseStart_1956319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956336 : List Nat := [2, 1, 1, 1, 3, 3, 4, 3, 4]
def baseStart_1956336 : Nat := 118140960795 + 1956336 * 2 ^ 59
def prefixEnd_1956336 : Nat := 4983230072969 + 3 ^ 40 * 1956336 * 2
def baseEnd_1956336 : Nat := 223231264376525124467329

theorem tailTrace_1956336 : CollatzResearch.WordTrace tailWord_1956336 prefixEnd_1956336 223231264376525124467329 := by
  unfold tailWord_1956336
  simp only [CollatzResearch.WordTrace]
  refine ⟨35676717920268131216804431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47568957227024174955739241 35676717920268131216804431)
  ·
    refine ⟨53515076880402196825206647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35676717920268131216804431 53515076880402196825206647)
    ·
      refine ⟨80272615320603295237809971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53515076880402196825206647 80272615320603295237809971)
      ·
        refine ⟨120408922980904942856714957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80272615320603295237809971 120408922980904942856714957)
        ·
          refine ⟨45153346117839353571268109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120408922980904942856714957 45153346117839353571268109)
          ·
            refine ⟨16932504794189757589225541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45153346117839353571268109 16932504794189757589225541)
            ·
              refine ⟨3174844648910579547979789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16932504794189757589225541 3174844648910579547979789)
              ·
                refine ⟨1190566743341467330492421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3174844648910579547979789 1190566743341467330492421)
                ·
                  refine ⟨223231264376525124467329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1190566743341467330492421 223231264376525124467329)
                  ·
                    rfl

theorem cell22_1956336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 4].length) (baseStart_1956336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956336 prefixEnd_1956336 := by exact prefixLift 1956336
  have htrace : WordTrace (prefixWord ++ tailWord_1956336) baseStart_1956336 baseEnd_1956336 := by
    simpa [prefixWord, tailWord_1956336, baseEnd_1956336] using wordTrace_append hprefix tailTrace_1956336
  have hstable : (prefixWord ++ tailWord_1956336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956336).length < 2 ^ (prefixWord ++ tailWord_1956336).sum := by decide
  have hdescent : baseEnd_1956336 < baseStart_1956336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956338 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_1956338 : Nat := 118140960795 + 1956338 * 2 ^ 59
def prefixEnd_1956338 : Nat := 4983230072969 + 3 ^ 40 * 1956338 * 2
def baseEnd_1956338 : Nat := 669694477770448034851981

theorem tailTrace_1956338 : CollatzResearch.WordTrace tailWord_1956338 prefixEnd_1956338 669694477770448034851981 := by
  unfold tailWord_1956338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17838377196632254193795417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47569005857686011183454445 17838377196632254193795417)
  ·
    refine ⟨13378782897474190645346563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17838377196632254193795417 13378782897474190645346563)
    ·
      refine ⟨20068174346211285968019845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13378782897474190645346563 20068174346211285968019845)
      ·
        refine ⟨3762782689914616119003721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20068174346211285968019845 3762782689914616119003721)
        ·
          refine ⟨2822087017435962089252791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3762782689914616119003721 2822087017435962089252791)
          ·
            refine ⟨4233130526153943133879187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822087017435962089252791 4233130526153943133879187)
            ·
              refine ⟨6349695789230914700818781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233130526153943133879187 6349695789230914700818781)
              ·
                refine ⟨2381135920961593012807043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6349695789230914700818781 2381135920961593012807043)
                ·
                  refine ⟨3571703881442389519210565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381135920961593012807043 3571703881442389519210565)
                  ·
                    refine ⟨669694477770448034851981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3571703881442389519210565 669694477770448034851981)
                    ·
                      rfl

theorem cell22_1956338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_1956338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956338 prefixEnd_1956338 := by exact prefixLift 1956338
  have htrace : WordTrace (prefixWord ++ tailWord_1956338) baseStart_1956338 baseEnd_1956338 := by
    simpa [prefixWord, tailWord_1956338, baseEnd_1956338] using wordTrace_append hprefix tailTrace_1956338
  have hstable : (prefixWord ++ tailWord_1956338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956338).length < 2 ^ (prefixWord ++ tailWord_1956338).sum := by decide
  have hdescent : baseEnd_1956338 < baseStart_1956338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956349 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_1956349 : Nat := 118140960795 + 1956349 * 2 ^ 59
def prefixEnd_1956349 : Nat := 4983230072969 + 3 ^ 40 * 1956349 * 2
def baseEnd_1956349 : Nat := 669698243295247672826947

theorem tailTrace_1956349 : CollatzResearch.WordTrace tailWord_1956349 prefixEnd_1956349 669698243295247672826947 := by
  unfold tailWord_1956349
  simp only [CollatzResearch.WordTrace]
  refine ⟨71353909989489165653832101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47569273326326110435888067 71353909989489165653832101)
  ·
    refine ⟨13378858123029218560093519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71353909989489165653832101 13378858123029218560093519)
    ·
      refine ⟨20068287184543827840140279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13378858123029218560093519 20068287184543827840140279)
      ·
        refine ⟨30102430776815741760210419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20068287184543827840140279 30102430776815741760210419)
        ·
          refine ⟨45153646165223612640315629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30102430776815741760210419 45153646165223612640315629)
          ·
            refine ⟨16932617311958854740118361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45153646165223612640315629 16932617311958854740118361)
            ·
              refine ⟨12699462983969141055088771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16932617311958854740118361 12699462983969141055088771)
              ·
                refine ⟨19049194475953711582633157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12699462983969141055088771 19049194475953711582633157)
                ·
                  refine ⟨3571723964241320921743717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19049194475953711582633157 3571723964241320921743717)
                  ·
                    refine ⟨669698243295247672826947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3571723964241320921743717 669698243295247672826947)
                    ·
                      rfl

theorem cell22_1956349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_1956349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956349 prefixEnd_1956349 := by exact prefixLift 1956349
  have htrace : WordTrace (prefixWord ++ tailWord_1956349) baseStart_1956349 baseEnd_1956349 := by
    simpa [prefixWord, tailWord_1956349, baseEnd_1956349] using wordTrace_append hprefix tailTrace_1956349
  have hstable : (prefixWord ++ tailWord_1956349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956349).length < 2 ^ (prefixWord ++ tailWord_1956349).sum := by decide
  have hdescent : baseEnd_1956349 < baseStart_1956349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956381 : List Nat := [1, 4, 2, 2, 1, 2, 4, 6]
def baseStart_1956381 : Nat := 118140960795 + 1956381 * 2 ^ 59
def prefixEnd_1956381 : Nat := 4983230072969 + 3 ^ 40 * 1956381 * 2
def baseEnd_1956381 : Nat := 74412133061023361780761

theorem tailTrace_1956381 : CollatzResearch.WordTrace tailWord_1956381 prefixEnd_1956381 74412133061023361780761 := by
  unfold tailWord_1956381
  simp only [CollatzResearch.WordTrace]
  refine ⟨71355077125373235118996997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47570051416915490079331331 71355077125373235118996997)
  ·
    refine ⟨13379076961007481584811937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71355077125373235118996997 13379076961007481584811937)
    ·
      refine ⟨10034307720755611188608953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13379076961007481584811937 10034307720755611188608953)
      ·
        refine ⟨7525730790566708391456715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10034307720755611188608953 7525730790566708391456715)
        ·
          refine ⟨11288596185850062587185073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525730790566708391456715 11288596185850062587185073)
          ·
            refine ⟨8466447139387546940388805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11288596185850062587185073 8466447139387546940388805)
            ·
              refine ⟨1587458838635165051322901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8466447139387546940388805 1587458838635165051322901)
              ·
                refine ⟨74412133061023361780761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1587458838635165051322901 74412133061023361780761)
                ·
                  rfl

theorem cell22_1956381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 6].length) (baseStart_1956381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956381 prefixEnd_1956381 := by exact prefixLift 1956381
  have htrace : WordTrace (prefixWord ++ tailWord_1956381) baseStart_1956381 baseEnd_1956381 := by
    simpa [prefixWord, tailWord_1956381, baseEnd_1956381] using wordTrace_append hprefix tailTrace_1956381
  have hstable : (prefixWord ++ tailWord_1956381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956381).length < 2 ^ (prefixWord ++ tailWord_1956381).sum := by decide
  have hdescent : baseEnd_1956381 < baseStart_1956381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956398 : List Nat := [4, 1, 3, 1, 4, 1, 8]
def baseStart_1956398 : Nat := 118140960795 + 1956398 * 2 ^ 59
def prefixEnd_1956398 : Nat := 4983230072969 + 3 ^ 40 * 1956398 * 2
def baseEnd_1956398 : Nat := 24804259888763995494511

theorem tailTrace_1956398 : CollatzResearch.WordTrace tailWord_1956398 prefixEnd_1956398 24804259888763995494511 := by
  unfold tailWord_1956398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8919462145788955877795731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47570464777541098014910565 8919462145788955877795731)
  ·
    refine ⟨13379193218683433816693597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8919462145788955877795731 13379193218683433816693597)
    ·
      refine ⟨5017197457006287681260099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13379193218683433816693597 5017197457006287681260099)
      ·
        refine ⟨7525796185509431521890149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5017197457006287681260099 7525796185509431521890149)
        ·
          refine ⟨1411086784783018410354403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7525796185509431521890149 1411086784783018410354403)
          ·
            refine ⟨2116630177174527615531605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411086784783018410354403 2116630177174527615531605)
            ·
              refine ⟨24804259888763995494511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2116630177174527615531605 24804259888763995494511)
              ·
                rfl

theorem cell22_1956398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 8].length) (baseStart_1956398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956398 prefixEnd_1956398 := by exact prefixLift 1956398
  have htrace : WordTrace (prefixWord ++ tailWord_1956398) baseStart_1956398 baseEnd_1956398 := by
    simpa [prefixWord, tailWord_1956398, baseEnd_1956398] using wordTrace_append hprefix tailTrace_1956398
  have hstable : (prefixWord ++ tailWord_1956398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956398).length < 2 ^ (prefixWord ++ tailWord_1956398).sum := by decide
  have hdescent : baseEnd_1956398 < baseStart_1956398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956409 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 7]
def baseStart_1956409 : Nat := 118140960795 + 1956409 * 2 ^ 59
def prefixEnd_1956409 : Nat := 4983230072969 + 3 ^ 40 * 1956409 * 2
def baseEnd_1956409 : Nat := 223239594173809172108921

theorem tailTrace_1956409 : CollatzResearch.WordTrace tailWord_1956409 prefixEnd_1956409 223239594173809172108921 := by
  unfold tailWord_1956409
  simp only [CollatzResearch.WordTrace]
  refine ⟨71356098369271795901016281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47570732246181197267344187 71356098369271795901016281)
  ·
    refine ⟨53517073776953846925762211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71356098369271795901016281 53517073776953846925762211)
    ·
      refine ⟨80275610665430770388643317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53517073776953846925762211 80275610665430770388643317)
      ·
        refine ⟨7525838499884134723935311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80275610665430770388643317 7525838499884134723935311)
        ·
          refine ⟨11288757749826202085902967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525838499884134723935311 11288757749826202085902967)
          ·
            refine ⟨16933136624739303128854451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288757749826202085902967 16933136624739303128854451)
            ·
              refine ⟨25399704937108954693281677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16933136624739303128854451 25399704937108954693281677)
              ·
                refine ⟨9524889351415858009980629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25399704937108954693281677 9524889351415858009980629)
                ·
                  refine ⟨223239594173809172108921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9524889351415858009980629 223239594173809172108921)
                  ·
                    rfl

theorem cell22_1956409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_1956409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956409 prefixEnd_1956409 := by exact prefixLift 1956409
  have htrace : WordTrace (prefixWord ++ tailWord_1956409) baseStart_1956409 baseEnd_1956409 := by
    simpa [prefixWord, tailWord_1956409, baseEnd_1956409] using wordTrace_append hprefix tailTrace_1956409
  have hstable : (prefixWord ++ tailWord_1956409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956409).length < 2 ^ (prefixWord ++ tailWord_1956409).sum := by decide
  have hdescent : baseEnd_1956409 < baseStart_1956409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956413 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_1956413 : Nat := 118140960795 + 1956413 * 2 ^ 59
def prefixEnd_1956413 : Nat := 4983230072969 + 3 ^ 40 * 1956413 * 2
def baseEnd_1956413 : Nat := 669720151803172839226751

theorem tailTrace_1956413 : CollatzResearch.WordTrace tailWord_1956413 prefixEnd_1956413 669720151803172839226751 := by
  unfold tailWord_1956413
  simp only [CollatzResearch.WordTrace]
  refine ⟨71356244261257304584161893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47570829507504869722774595 71356244261257304584161893)
  ·
    refine ⟨13379295798985744609530355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71356244261257304584161893 13379295798985744609530355)
    ·
      refine ⟨20068943698478616914295533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13379295798985744609530355 20068943698478616914295533)
      ·
        refine ⟨7525853886929481342860825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20068943698478616914295533 7525853886929481342860825)
        ·
          refine ⟨5644390415197111007145619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7525853886929481342860825 5644390415197111007145619)
          ·
            refine ⟨8466585622795666510718429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5644390415197111007145619 8466585622795666510718429)
            ·
              refine ⟨3174969608548374941519411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8466585622795666510718429 3174969608548374941519411)
              ·
                refine ⟨4762454412822562412279117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174969608548374941519411 4762454412822562412279117)
                ·
                  refine ⟨1785920404808460904604669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4762454412822562412279117 1785920404808460904604669)
                  ·
                    refine ⟨669720151803172839226751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785920404808460904604669 669720151803172839226751)
                    ·
                      rfl

theorem cell22_1956413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_1956413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956413 prefixEnd_1956413 := by exact prefixLift 1956413
  have htrace : WordTrace (prefixWord ++ tailWord_1956413) baseStart_1956413 baseEnd_1956413 := by
    simpa [prefixWord, tailWord_1956413, baseEnd_1956413] using wordTrace_append hprefix tailTrace_1956413
  have hstable : (prefixWord ++ tailWord_1956413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956413).length < 2 ^ (prefixWord ++ tailWord_1956413).sum := by decide
  have hdescent : baseEnd_1956413 < baseStart_1956413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956424 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_1956424 : Nat := 118140960795 + 1956424 * 2 ^ 59
def prefixEnd_1956424 : Nat := 4983230072969 + 3 ^ 40 * 1956424 * 2
def baseEnd_1956424 : Nat := 669723917327972477201717

theorem tailTrace_1956424 : CollatzResearch.WordTrace tailWord_1956424 prefixEnd_1956424 669723917327972477201717 := by
  unfold tailWord_1956424
  simp only [CollatzResearch.WordTrace]
  refine ⟨35678322732108726731406163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47571096976144968975208217 35678322732108726731406163)
  ·
    refine ⟨53517484098163090097109245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35678322732108726731406163 53517484098163090097109245)
    ·
      refine ⟨20069056536811158786415967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53517484098163090097109245 20069056536811158786415967)
      ·
        refine ⟨30103584805216738179623951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20069056536811158786415967 30103584805216738179623951)
        ·
          refine ⟨45155377207825107269435927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30103584805216738179623951 45155377207825107269435927)
          ·
            refine ⟨67733065811737660904153891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45155377207825107269435927 67733065811737660904153891)
            ·
              refine ⟨101599598717606491356230837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67733065811737660904153891 101599598717606491356230837)
              ·
                refine ⟨9524962379775608564646641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101599598717606491356230837 9524962379775608564646641)
                ·
                  refine ⟨7143721784831706423484981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9524962379775608564646641 7143721784831706423484981)
                  ·
                    refine ⟨669723917327972477201717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7143721784831706423484981 669723917327972477201717)
                    ·
                      rfl

theorem cell22_1956424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_1956424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956424 prefixEnd_1956424 := by exact prefixLift 1956424
  have htrace : WordTrace (prefixWord ++ tailWord_1956424) baseStart_1956424 baseEnd_1956424 := by
    simpa [prefixWord, tailWord_1956424, baseEnd_1956424] using wordTrace_append hprefix tailTrace_1956424
  have hstable : (prefixWord ++ tailWord_1956424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956424).length < 2 ^ (prefixWord ++ tailWord_1956424).sum := by decide
  have hdescent : baseEnd_1956424 < baseStart_1956424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956426 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_1956426 : Nat := 118140960795 + 1956426 * 2 ^ 59
def prefixEnd_1956426 : Nat := 4983230072969 + 3 ^ 40 * 1956426 * 2
def baseEnd_1956426 : Nat := 223241533989615046217237

theorem tailTrace_1956426 : CollatzResearch.WordTrace tailWord_1956426 prefixEnd_1956426 223241533989615046217237 := by
  unfold tailWord_1956426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17839179602552551951096283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47571145606806805202923421 17839179602552551951096283)
  ·
    refine ⟨26758769403828827926644425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17839179602552551951096283 26758769403828827926644425)
    ·
      refine ⟨20069077052871620944983319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26758769403828827926644425 20069077052871620944983319)
      ·
        refine ⟨30103615579307431417474979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20069077052871620944983319 30103615579307431417474979)
        ·
          refine ⟨45155423368961147126212469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30103615579307431417474979 45155423368961147126212469)
          ·
            refine ⟨4233320940840107543082419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45155423368961147126212469 4233320940840107543082419)
            ·
              refine ⟨6349981411260161314623629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233320940840107543082419 6349981411260161314623629)
              ·
                refine ⟨2381243029222560492983861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6349981411260161314623629 2381243029222560492983861)
                ·
                  refine ⟨223241533989615046217237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2381243029222560492983861 223241533989615046217237)
                  ·
                    rfl

theorem cell22_1956426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_1956426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956426 prefixEnd_1956426 := by exact prefixLift 1956426
  have htrace : WordTrace (prefixWord ++ tailWord_1956426) baseStart_1956426 baseEnd_1956426 := by
    simpa [prefixWord, tailWord_1956426, baseEnd_1956426] using wordTrace_append hprefix tailTrace_1956426
  have hstable : (prefixWord ++ tailWord_1956426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956426).length < 2 ^ (prefixWord ++ tailWord_1956426).sum := by decide
  have hdescent : baseEnd_1956426 < baseStart_1956426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956464 : List Nat := [2, 1, 1, 1, 8, 1, 2, 2, 1, 3]
def baseStart_1956464 : Nat := 118140960795 + 1956464 * 2 ^ 59
def prefixEnd_1956464 : Nat := 4983230072969 + 3 ^ 40 * 1956464 * 2
def baseEnd_1956464 : Nat := 669737610145425706201595

theorem tailTrace_1956464 : CollatzResearch.WordTrace tailWord_1956464 prefixEnd_1956464 669737610145425706201595 := by
  unfold tailWord_1956464
  simp only [CollatzResearch.WordTrace]
  refine ⟨35679052192036270147134223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47572069589381693529512297 35679052192036270147134223)
  ·
    refine ⟨53518578288054405220701335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35679052192036270147134223 53518578288054405220701335)
    ·
      refine ⟨80277867432081607831052003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53518578288054405220701335 80277867432081607831052003)
      ·
        refine ⟨120416801148122411746578005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80277867432081607831052003 120416801148122411746578005)
        ·
          refine ⟨1411134388454559512655211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 120416801148122411746578005 1411134388454559512655211)
          ·
            refine ⟨2116701582681839268982817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411134388454559512655211 2116701582681839268982817)
            ·
              refine ⟨1587526187011379451737113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116701582681839268982817 1587526187011379451737113)
              ·
                refine ⟨1190644640258534588802835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587526187011379451737113 1190644640258534588802835)
                ·
                  refine ⟨1785966960387801883204253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190644640258534588802835 1785966960387801883204253)
                  ·
                    refine ⟨669737610145425706201595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785966960387801883204253 669737610145425706201595)
                    ·
                      rfl

theorem cell22_1956464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 1, 3].length) (baseStart_1956464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956464 prefixEnd_1956464 := by exact prefixLift 1956464
  have htrace : WordTrace (prefixWord ++ tailWord_1956464) baseStart_1956464 baseEnd_1956464 := by
    simpa [prefixWord, tailWord_1956464, baseEnd_1956464] using wordTrace_append hprefix tailTrace_1956464
  have hstable : (prefixWord ++ tailWord_1956464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956464).length < 2 ^ (prefixWord ++ tailWord_1956464).sum := by decide
  have hdescent : baseEnd_1956464 < baseStart_1956464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956623 : List Nat := [1, 1, 2, 1, 1, 1, 6, 5, 4]
def baseStart_1956623 : Nat := 118140960795 + 1956623 * 2 ^ 59
def prefixEnd_1956623 : Nat := 4983230072969 + 3 ^ 40 * 1956623 * 2
def baseEnd_1956623 : Nat := 223264013031600763825369

theorem tailTrace_1956623 : CollatzResearch.WordTrace tailWord_1956623 prefixEnd_1956623 223264013031600763825369 := by
  unfold tailWord_1956623
  simp only [CollatzResearch.WordTrace]
  refine ⟨71363903590496510449306523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47575935726997673632871015 71363903590496510449306523)
  ·
    refine ⟨107045855385744765673959785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71363903590496510449306523 107045855385744765673959785)
    ·
      refine ⟨80284391539308574255469839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107045855385744765673959785 80284391539308574255469839)
      ·
        refine ⟨120426587308962861383204759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80284391539308574255469839 120426587308962861383204759)
        ·
          refine ⟨180639880963444292074807139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120426587308962861383204759 180639880963444292074807139)
          ·
            refine ⟨270959821445166438112210709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180639880963444292074807139 270959821445166438112210709)
            ·
              refine ⟨12701241630242176786509877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 270959821445166438112210709 12701241630242176786509877)
              ·
                refine ⟨1190741402835204073735301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12701241630242176786509877 1190741402835204073735301)
                ·
                  refine ⟨223264013031600763825369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1190741402835204073735301 223264013031600763825369)
                  ·
                    rfl

theorem cell22_1956623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 4].length) (baseStart_1956623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956623 prefixEnd_1956623 := by exact prefixLift 1956623
  have htrace : WordTrace (prefixWord ++ tailWord_1956623) baseStart_1956623 baseEnd_1956623 := by
    simpa [prefixWord, tailWord_1956623, baseEnd_1956623] using wordTrace_append hprefix tailTrace_1956623
  have hstable : (prefixWord ++ tailWord_1956623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956623).length < 2 ^ (prefixWord ++ tailWord_1956623).sum := by decide
  have hdescent : baseEnd_1956623 < baseStart_1956623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956640 : List Nat := [2, 1, 1, 5, 1, 3, 1, 4, 4]
def baseStart_1956640 : Nat := 118140960795 + 1956640 * 2 ^ 59
def prefixEnd_1956640 : Nat := 4983230072969 + 3 ^ 40 * 1956640 * 2
def baseEnd_1956640 : Nat := 223265952847406637933685

theorem tailTrace_1956640 : CollatzResearch.WordTrace tailWord_1956640 prefixEnd_1956640 223265952847406637933685 := by
  unfold tailWord_1956640
  simp only [CollatzResearch.WordTrace]
  refine ⟨35682261815717461176337687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47576349087623281568450249 35682261815717461176337687)
  ·
    refine ⟨53523392723576191764506531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35682261815717461176337687 53523392723576191764506531)
    ·
      refine ⟨80285089085364287646759797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53523392723576191764506531 80285089085364287646759797)
      ·
        refine ⟨7526727101752901966883731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80285089085364287646759797 7526727101752901966883731)
        ·
          refine ⟨11290090652629352950325597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7526727101752901966883731 11290090652629352950325597)
          ·
            refine ⟨4233783994736007356372099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11290090652629352950325597 4233783994736007356372099)
            ·
              refine ⟨6350675992104011034558149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233783994736007356372099 6350675992104011034558149)
              ·
                refine ⟨1190751748519502068979653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6350675992104011034558149 1190751748519502068979653)
                ·
                  refine ⟨223265952847406637933685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1190751748519502068979653 223265952847406637933685)
                  ·
                    rfl

theorem cell22_1956640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 4].length) (baseStart_1956640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956640 prefixEnd_1956640 := by exact prefixLift 1956640
  have htrace : WordTrace (prefixWord ++ tailWord_1956640) baseStart_1956640 baseEnd_1956640 := by
    simpa [prefixWord, tailWord_1956640, baseEnd_1956640] using wordTrace_append hprefix tailTrace_1956640
  have hstable : (prefixWord ++ tailWord_1956640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956640).length < 2 ^ (prefixWord ++ tailWord_1956640).sum := by decide
  have hdescent : baseEnd_1956640 < baseStart_1956640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956670 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_1956670 : Nat := 118140960795 + 1956670 * 2 ^ 59
def prefixEnd_1956670 : Nat := 4983230072969 + 3 ^ 40 * 1956670 * 2
def baseEnd_1956670 : Nat := 669808128155309835550963

theorem tailTrace_1956670 : CollatzResearch.WordTrace tailWord_1956670 prefixEnd_1956670 669808128155309835550963 := by
  unfold tailWord_1956670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8920702227665779684533433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47577078547550824984178309 8920702227665779684533433)
  ·
    refine ⟨6690526670749334763400075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8920702227665779684533433 6690526670749334763400075)
    ·
      refine ⟨10035790006124002145100113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6690526670749334763400075 10035790006124002145100113)
      ·
        refine ⟨7526842504593001608825085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10035790006124002145100113 7526842504593001608825085)
        ·
          refine ⟨2822565939222375603309407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7526842504593001608825085 2822565939222375603309407)
          ·
            refine ⟨4233848908833563404964111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822565939222375603309407 4233848908833563404964111)
            ·
              refine ⟨6350773363250345107446167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233848908833563404964111 6350773363250345107446167)
              ·
                refine ⟨9526160044875517661169251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6350773363250345107446167 9526160044875517661169251)
                ·
                  refine ⟨14289240067313276491753877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9526160044875517661169251 14289240067313276491753877)
                  ·
                    refine ⟨669808128155309835550963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14289240067313276491753877 669808128155309835550963)
                    ·
                      rfl

theorem cell22_1956670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_1956670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956670 prefixEnd_1956670 := by exact prefixLift 1956670
  have htrace : WordTrace (prefixWord ++ tailWord_1956670) baseStart_1956670 baseEnd_1956670 := by
    simpa [prefixWord, tailWord_1956670, baseEnd_1956670] using wordTrace_append hprefix tailTrace_1956670
  have hstable : (prefixWord ++ tailWord_1956670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956670).length < 2 ^ (prefixWord ++ tailWord_1956670).sum := by decide
  have hdescent : baseEnd_1956670 < baseStart_1956670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956676 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1956676 : Nat := 118140960795 + 1956676 * 2 ^ 59
def prefixEnd_1956676 : Nat := 4983230072969 + 3 ^ 40 * 1956676 * 2
def baseEnd_1956676 : Nat := 669810182077927819900945

theorem tailTrace_1956676 : CollatzResearch.WordTrace tailWord_1956676 prefixEnd_1956676 669810182077927819900945 := by
  unfold tailWord_1956676
  simp only [CollatzResearch.WordTrace]
  refine ⟨35682918329652250250492941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47577224439536333667323921 35682918329652250250492941)
  ·
    refine ⟨13381094373619593843934853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35682918329652250250492941 13381094373619593843934853)
    ·
      refine ⟨2508955195053673845737785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13381094373619593843934853 2508955195053673845737785)
      ·
        refine ⟨1881716396290255384303339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2508955195053673845737785 1881716396290255384303339)
        ·
          refine ⟨2822574594435383076455009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881716396290255384303339 2822574594435383076455009)
          ·
            refine ⟨2116930945826537307341257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822574594435383076455009 2116930945826537307341257)
            ·
              refine ⟨1587698209369902980505943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116930945826537307341257 1587698209369902980505943)
              ·
                refine ⟨2381547314054854470758915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587698209369902980505943 2381547314054854470758915)
                ·
                  refine ⟨3572320971082281706138373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381547314054854470758915 3572320971082281706138373)
                  ·
                    refine ⟨669810182077927819900945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3572320971082281706138373 669810182077927819900945)
                    ·
                      rfl

theorem cell22_1956676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1956676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956676 prefixEnd_1956676 := by exact prefixLift 1956676
  have htrace : WordTrace (prefixWord ++ tailWord_1956676) baseStart_1956676 baseEnd_1956676 := by
    simpa [prefixWord, tailWord_1956676, baseEnd_1956676] using wordTrace_append hprefix tailTrace_1956676
  have hstable : (prefixWord ++ tailWord_1956676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956676).length < 2 ^ (prefixWord ++ tailWord_1956676).sum := by decide
  have hdescent : baseEnd_1956676 < baseStart_1956676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956685 : List Nat := [1, 6, 1, 2, 2, 1, 9]
def baseStart_1956685 : Nat := 118140960795 + 1956685 * 2 ^ 59
def prefixEnd_1956685 : Nat := 4983230072969 + 3 ^ 40 * 1956685 * 2
def baseEnd_1956685 : Nat := 24807898628216844312071

theorem tailTrace_1956685 : CollatzResearch.WordTrace tailWord_1956685 prefixEnd_1956685 24807898628216844312071 := by
  unfold tailWord_1956685
  simp only [CollatzResearch.WordTrace]
  refine ⟨71366164916271895038063509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47577443277514596692042339 71366164916271895038063509)
  ·
    refine ⟨3345288980450245079909227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71366164916271895038063509 3345288980450245079909227)
    ·
      refine ⟨5017933470675367619863841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3345288980450245079909227 5017933470675367619863841)
      ·
        refine ⟨3763450103006525714897881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5017933470675367619863841 3763450103006525714897881)
        ·
          refine ⟨2822587577254894286173411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3763450103006525714897881 2822587577254894286173411)
          ·
            refine ⟨4233881365882341429260117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822587577254894286173411 4233881365882341429260117)
            ·
              refine ⟨24807898628216844312071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4233881365882341429260117 24807898628216844312071)
              ·
                rfl

theorem cell22_1956685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 9].length) (baseStart_1956685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956685 prefixEnd_1956685 := by exact prefixLift 1956685
  have htrace : WordTrace (prefixWord ++ tailWord_1956685) baseStart_1956685 baseEnd_1956685 := by
    simpa [prefixWord, tailWord_1956685, baseEnd_1956685] using wordTrace_append hprefix tailTrace_1956685
  have hstable : (prefixWord ++ tailWord_1956685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956685).length < 2 ^ (prefixWord ++ tailWord_1956685).sum := by decide
  have hdescent : baseEnd_1956685 < baseStart_1956685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956689 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 2, 3]
def baseStart_1956689 : Nat := 118140960795 + 1956689 * 2 ^ 59
def prefixEnd_1956689 : Nat := 4983230072969 + 3 ^ 40 * 1956689 * 2
def baseEnd_1956689 : Nat := 669814632243600119325905

theorem tailTrace_1956689 : CollatzResearch.WordTrace tailWord_1956689 prefixEnd_1956689 669814632243600119325905 := by
  unfold tailWord_1956689
  simp only [CollatzResearch.WordTrace]
  refine ⟨71366310808257403721209121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47577540538838269147472747 71366310808257403721209121)
  ·
    refine ⟨53524733106193052790906841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71366310808257403721209121 53524733106193052790906841)
    ·
      refine ⟨40143549829644789593180131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53524733106193052790906841 40143549829644789593180131)
      ·
        refine ⟨60215324744467184389770197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40143549829644789593180131 60215324744467184389770197)
        ·
          refine ⟨1411296673698449634135239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 60215324744467184389770197 1411296673698449634135239)
          ·
            refine ⟨2116945010547674451202859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411296673698449634135239 2116945010547674451202859)
            ·
              refine ⟨3175417515821511676804289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116945010547674451202859 3175417515821511676804289)
              ·
                refine ⟨2381563136866133757603217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3175417515821511676804289 2381563136866133757603217)
                ·
                  refine ⟨1786172352649600318202413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2381563136866133757603217 1786172352649600318202413)
                  ·
                    refine ⟨669814632243600119325905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1786172352649600318202413 669814632243600119325905)
                    ·
                      rfl

theorem cell22_1956689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_1956689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956689 prefixEnd_1956689 := by exact prefixLift 1956689
  have htrace : WordTrace (prefixWord ++ tailWord_1956689) baseStart_1956689 baseEnd_1956689 := by
    simpa [prefixWord, tailWord_1956689, baseEnd_1956689] using wordTrace_append hprefix tailTrace_1956689
  have hstable : (prefixWord ++ tailWord_1956689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956689).length < 2 ^ (prefixWord ++ tailWord_1956689).sum := by decide
  have hdescent : baseEnd_1956689 < baseStart_1956689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956764 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 5]
def baseStart_1956764 : Nat := 118140960795 + 1956764 * 2 ^ 59
def prefixEnd_1956764 : Nat := 4983230072969 + 3 ^ 40 * 1956764 * 2
def baseEnd_1956764 : Nat := 223280102092108307900225

theorem tailTrace_1956764 : CollatzResearch.WordTrace tailWord_1956764 prefixEnd_1956764 223280102092108307900225 := by
  unfold tailWord_1956764
  simp only [CollatzResearch.WordTrace]
  refine ⟨35684523141492845765094673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47579364188657127686792897 35684523141492845765094673)
  ·
    refine ⟨26763392356119634323821005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35684523141492845765094673 26763392356119634323821005)
    ·
      refine ⟨10036272133544862871432877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26763392356119634323821005 10036272133544862871432877)
      ·
        refine ⟨3763602050079323576787329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10036272133544862871432877 3763602050079323576787329)
        ·
          refine ⟨2822701537559492682590497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3763602050079323576787329 2822701537559492682590497)
          ·
            refine ⟨2117026153169619511942873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822701537559492682590497 2117026153169619511942873)
            ·
              refine ⟨1587769614877214633957155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117026153169619511942873 1587769614877214633957155)
              ·
                refine ⟨2381654422315821950935733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587769614877214633957155 2381654422315821950935733)
                ·
                  refine ⟨223280102092108307900225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2381654422315821950935733 223280102092108307900225)
                  ·
                    rfl

theorem cell22_1956764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_1956764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956764 prefixEnd_1956764 := by exact prefixLift 1956764
  have htrace : WordTrace (prefixWord ++ tailWord_1956764) baseStart_1956764 baseEnd_1956764 := by
    simpa [prefixWord, tailWord_1956764, baseEnd_1956764] using wordTrace_append hprefix tailTrace_1956764
  have hstable : (prefixWord ++ tailWord_1956764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956764).length < 2 ^ (prefixWord ++ tailWord_1956764).sum := by decide
  have hdescent : baseEnd_1956764 < baseStart_1956764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956820 : List Nat := [2, 4, 1, 2, 1, 2, 3, 7]
def baseStart_1956820 : Nat := 118140960795 + 1956820 * 2 ^ 59
def prefixEnd_1956820 : Nat := 4983230072969 + 3 ^ 40 * 1956820 * 2
def baseEnd_1956820 : Nat := 74428830691195493811167

theorem tailTrace_1956820 : CollatzResearch.WordTrace tailWord_1956820 prefixEnd_1956820 74428830691195493811167 := by
  unfold tailWord_1956820
  simp only [CollatzResearch.WordTrace]
  refine ⟨35685544385391406547113957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47580725847188542062818609 35685544385391406547113957)
  ·
    refine ⟨6691039572260888727583867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35685544385391406547113957 6691039572260888727583867)
    ·
      refine ⟨10036559358391333091375801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6691039572260888727583867 10036559358391333091375801)
      ·
        refine ⟨7527419518793499818531851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10036559358391333091375801 7527419518793499818531851)
        ·
          refine ⟨11291129278190249727797777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7527419518793499818531851 11291129278190249727797777)
          ·
            refine ⟨8468346958642687295848333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11291129278190249727797777 8468346958642687295848333)
            ·
              refine ⟨3175630109491007735943125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8468346958642687295848333 3175630109491007735943125)
              ·
                refine ⟨74428830691195493811167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3175630109491007735943125 74428830691195493811167)
                ·
                  rfl

theorem cell22_1956820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 7].length) (baseStart_1956820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956820 prefixEnd_1956820 := by exact prefixLift 1956820
  have htrace : WordTrace (prefixWord ++ tailWord_1956820) baseStart_1956820 baseEnd_1956820 := by
    simpa [prefixWord, tailWord_1956820, baseEnd_1956820] using wordTrace_append hprefix tailTrace_1956820
  have hstable : (prefixWord ++ tailWord_1956820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956820).length < 2 ^ (prefixWord ++ tailWord_1956820).sum := by decide
  have hdescent : baseEnd_1956820 < baseStart_1956820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956833 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1956833 : Nat := 118140960795 + 1956833 * 2 ^ 59
def prefixEnd_1956833 : Nat := 4983230072969 + 3 ^ 40 * 1956833 * 2
def baseEnd_1956833 : Nat := 669863926386431743725463

theorem tailTrace_1956833 : CollatzResearch.WordTrace tailWord_1956833 prefixEnd_1956833 669863926386431743725463 := by
  unfold tailWord_1956833
  simp only [CollatzResearch.WordTrace]
  refine ⟨71371562919735716314451153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47581041946490477542967435 71371562919735716314451153)
  ·
    refine ⟨53528672189801787235838365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71371562919735716314451153 53528672189801787235838365)
    ·
      refine ⟨20073252071175670213439387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53528672189801787235838365 20073252071175670213439387)
      ·
        refine ⟨30109878106763505320159081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20073252071175670213439387 30109878106763505320159081)
        ·
          refine ⟨22582408580072628990119311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30109878106763505320159081 22582408580072628990119311)
          ·
            refine ⟨33873612870108943485178967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22582408580072628990119311 33873612870108943485178967)
            ·
              refine ⟨50810419305163415227768451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33873612870108943485178967 50810419305163415227768451)
              ·
                refine ⟨76215628957745122841652677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50810419305163415227768451 76215628957745122841652677)
                ·
                  refine ⟨14290430429577210532809877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76215628957745122841652677 14290430429577210532809877)
                  ·
                    refine ⟨669863926386431743725463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14290430429577210532809877 669863926386431743725463)
                    ·
                      rfl

theorem cell22_1956833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1956833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956833 prefixEnd_1956833 := by exact prefixLift 1956833
  have htrace : WordTrace (prefixWord ++ tailWord_1956833) baseStart_1956833 baseEnd_1956833 := by
    simpa [prefixWord, tailWord_1956833, baseEnd_1956833] using wordTrace_append hprefix tailTrace_1956833
  have hstable : (prefixWord ++ tailWord_1956833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956833).length < 2 ^ (prefixWord ++ tailWord_1956833).sum := by decide
  have hdescent : baseEnd_1956833 < baseStart_1956833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956848 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 7]
def baseStart_1956848 : Nat := 118140960795 + 1956848 * 2 ^ 59
def prefixEnd_1956848 : Nat := 4983230072969 + 3 ^ 40 * 1956848 * 2
def baseEnd_1956848 : Nat := 223289687064325568200139

theorem tailTrace_1956848 : CollatzResearch.WordTrace tailWord_1956848 prefixEnd_1956848 223289687064325568200139 := by
  unfold tailWord_1956848
  simp only [CollatzResearch.WordTrace]
  refine ⟨35686055007340686938123599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47581406676454249250831465 35686055007340686938123599)
  ·
    refine ⟨53529082511011030407185399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35686055007340686938123599 53529082511011030407185399)
    ·
      refine ⟨80293623766516545610778099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53529082511011030407185399 80293623766516545610778099)
      ·
        refine ⟨120440435649774818416167149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80293623766516545610778099 120440435649774818416167149)
        ·
          refine ⟨45165163368665556906062681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120440435649774818416167149 45165163368665556906062681)
          ·
            refine ⟨33873872526499167679547011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45165163368665556906062681 33873872526499167679547011)
            ·
              refine ⟨50810808789748751519320517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33873872526499167679547011 50810808789748751519320517)
              ·
                refine ⟨9527026648077890909872597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50810808789748751519320517 9527026648077890909872597)
                ·
                  refine ⟨223289687064325568200139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9527026648077890909872597 223289687064325568200139)
                  ·
                    rfl

theorem cell22_1956848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_1956848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956848 prefixEnd_1956848 := by exact prefixLift 1956848
  have htrace : WordTrace (prefixWord ++ tailWord_1956848) baseStart_1956848 baseEnd_1956848 := by
    simpa [prefixWord, tailWord_1956848, baseEnd_1956848] using wordTrace_append hprefix tailTrace_1956848
  have hstable : (prefixWord ++ tailWord_1956848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956848).length < 2 ^ (prefixWord ++ tailWord_1956848).sum := by decide
  have hdescent : baseEnd_1956848 < baseStart_1956848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956865 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 7]
def baseStart_1956865 : Nat := 118140960795 + 1956865 * 2 ^ 59
def prefixEnd_1956865 : Nat := 4983230072969 + 3 ^ 40 * 1956865 * 2
def baseEnd_1956865 : Nat := 223291626880131442308455

theorem tailTrace_1956865 : CollatzResearch.WordTrace tailWord_1956865 prefixEnd_1956865 223291626880131442308455 := by
  unfold tailWord_1956865
  simp only [CollatzResearch.WordTrace]
  refine ⟨71372730055619785779616049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47581820037079857186410699 71372730055619785779616049)
  ·
    refine ⟨53529547541714839334712037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71372730055619785779616049 53529547541714839334712037)
    ·
      refine ⟨10036790164071532375258507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53529547541714839334712037 10036790164071532375258507)
      ·
        refine ⟨15055185246107298562887761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10036790164071532375258507 15055185246107298562887761)
        ·
          refine ⟨11291388934580473922165821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15055185246107298562887761 11291388934580473922165821)
          ·
            refine ⟨4234270850467677720812183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11291388934580473922165821 4234270850467677720812183)
            ·
              refine ⟨6351406275701516581218275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234270850467677720812183 6351406275701516581218275)
              ·
                refine ⟨9527109413552274871827413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351406275701516581218275 9527109413552274871827413)
                ·
                  refine ⟨223291626880131442308455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9527109413552274871827413 223291626880131442308455)
                  ·
                    rfl

theorem cell22_1956865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_1956865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956865 prefixEnd_1956865 := by exact prefixLift 1956865
  have htrace : WordTrace (prefixWord ++ tailWord_1956865) baseStart_1956865 baseEnd_1956865 := by
    simpa [prefixWord, tailWord_1956865, baseEnd_1956865] using wordTrace_append hprefix tailTrace_1956865
  have hstable : (prefixWord ++ tailWord_1956865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956865).length < 2 ^ (prefixWord ++ tailWord_1956865).sum := by decide
  have hdescent : baseEnd_1956865 < baseStart_1956865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956903 : List Nat := [1, 1, 7, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1956903 : Nat := 118140960795 + 1956903 * 2 ^ 59
def prefixEnd_1956903 : Nat := 4983230072969 + 3 ^ 40 * 1956903 * 2
def baseEnd_1956903 : Nat := 669887888816974894475249

theorem tailTrace_1956903 : CollatzResearch.WordTrace tailWord_1956903 prefixEnd_1956903 669887888816974894475249 := by
  unfold tailWord_1956903
  simp only [CollatzResearch.WordTrace]
  refine ⟨71374116029482118269499363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47582744019654745512999575 71374116029482118269499363)
  ·
    refine ⟨107061174044223177404249045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71374116029482118269499363 107061174044223177404249045)
    ·
      refine ⟨2509246266661480720412087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 107061174044223177404249045 2509246266661480720412087)
      ·
        refine ⟨3763869399992221080618131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509246266661480720412087 3763869399992221080618131)
        ·
          refine ⟨5645804099988331620927197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763869399992221080618131 5645804099988331620927197)
          ·
            refine ⟨2117176537495624357847699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5645804099988331620927197 2117176537495624357847699)
            ·
              refine ⟨3175764806243436536771549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117176537495624357847699 3175764806243436536771549)
              ·
                refine ⟨1190911802341288701289331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3175764806243436536771549 1190911802341288701289331)
                ·
                  refine ⟨1786367703511933051933997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190911802341288701289331 1786367703511933051933997)
                  ·
                    refine ⟨669887888816974894475249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1786367703511933051933997 669887888816974894475249)
                    ·
                      rfl

theorem cell22_1956903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1956903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956903 prefixEnd_1956903 := by exact prefixLift 1956903
  have htrace : WordTrace (prefixWord ++ tailWord_1956903) baseStart_1956903 baseEnd_1956903 := by
    simpa [prefixWord, tailWord_1956903, baseEnd_1956903] using wordTrace_append hprefix tailTrace_1956903
  have hstable : (prefixWord ++ tailWord_1956903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956903).length < 2 ^ (prefixWord ++ tailWord_1956903).sum := by decide
  have hdescent : baseEnd_1956903 < baseStart_1956903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956940 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_1956940 : Nat := 118140960795 + 1956940 * 2 ^ 59
def prefixEnd_1956940 : Nat := 4983230072969 + 3 ^ 40 * 1956940 * 2
def baseEnd_1956940 : Nat := 669900554673119131300135

theorem tailTrace_1956940 : CollatzResearch.WordTrace tailWord_1956940 prefixEnd_1956940 669900554673119131300135 := by
  unfold tailWord_1956940
  simp only [CollatzResearch.WordTrace]
  refine ⟨35687732765174036794298137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47583643686898715725730849 35687732765174036794298137)
  ·
    refine ⟨26765799573880527595723603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35687732765174036794298137 26765799573880527595723603)
    ·
      refine ⟨40148699360820791393585405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26765799573880527595723603 40148699360820791393585405)
      ·
        refine ⟨15055762260307796772594527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40148699360820791393585405 15055762260307796772594527)
        ·
          refine ⟨22583643390461695158891791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055762260307796772594527 22583643390461695158891791)
          ·
            refine ⟨33875465085692542738337687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22583643390461695158891791 33875465085692542738337687)
            ·
              refine ⟨50813197628538814107506531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33875465085692542738337687 50813197628538814107506531)
              ·
                refine ⟨76219796442808221161259797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50813197628538814107506531 76219796442808221161259797)
                ·
                  refine ⟨3572802958256635366934053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76219796442808221161259797 3572802958256635366934053)
                  ·
                    refine ⟨669900554673119131300135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3572802958256635366934053 669900554673119131300135)
                    ·
                      rfl

theorem cell22_1956940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_1956940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956940 prefixEnd_1956940 := by exact prefixLift 1956940
  have htrace : WordTrace (prefixWord ++ tailWord_1956940) baseStart_1956940 baseEnd_1956940 := by
    simpa [prefixWord, tailWord_1956940, baseEnd_1956940] using wordTrace_append hprefix tailTrace_1956940
  have hstable : (prefixWord ++ tailWord_1956940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956940).length < 2 ^ (prefixWord ++ tailWord_1956940).sum := by decide
  have hdescent : baseEnd_1956940 < baseStart_1956940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957021 : List Nat := [1, 4, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_1957021 : Nat := 118140960795 + 1957021 * 2 ^ 59
def prefixEnd_1957021 : Nat := 4983230072969 + 3 ^ 40 * 1957021 * 2
def baseEnd_1957021 : Nat := 669928282628461920024887

theorem tailTrace_1957021 : CollatzResearch.WordTrace tailWord_1957021 prefixEnd_1957021 669928282628461920024887 := by
  unfold tailWord_1957021
  simp only [CollatzResearch.WordTrace]
  refine ⟨71378419843054624422294917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47585613228703082948196611 71378419843054624422294917)
  ·
    refine ⟨13383453720572742079180297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71378419843054624422294917 13383453720572742079180297)
    ·
      refine ⟨10037590290429556559385223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13383453720572742079180297 10037590290429556559385223)
      ·
        refine ⟨15056385435644334839077835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037590290429556559385223 15056385435644334839077835)
        ·
          refine ⟨22584578153466502258616753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15056385435644334839077835 22584578153466502258616753)
          ·
            refine ⟨16938433615099876693962565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22584578153466502258616753 16938433615099876693962565)
            ·
              refine ⟨3175956302831226880117981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16938433615099876693962565 3175956302831226880117981)
              ·
                refine ⟨1190983613561710080044243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3175956302831226880117981 1190983613561710080044243)
                ·
                  refine ⟨1786475420342565120066365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190983613561710080044243 1786475420342565120066365)
                  ·
                    refine ⟨669928282628461920024887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1786475420342565120066365 669928282628461920024887)
                    ·
                      rfl

theorem cell22_1957021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_1957021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957021 prefixEnd_1957021 := by exact prefixLift 1957021
  have htrace : WordTrace (prefixWord ++ tailWord_1957021) baseStart_1957021 baseEnd_1957021 := by
    simpa [prefixWord, tailWord_1957021, baseEnd_1957021] using wordTrace_append hprefix tailTrace_1957021
  have hstable : (prefixWord ++ tailWord_1957021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957021).length < 2 ^ (prefixWord ++ tailWord_1957021).sum := by decide
  have hdescent : baseEnd_1957021 < baseStart_1957021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957034 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_1957034 : Nat := 118140960795 + 1957034 * 2 ^ 59
def prefixEnd_1957034 : Nat := 4983230072969 + 3 ^ 40 * 1957034 * 2
def baseEnd_1957034 : Nat := 223310910931378073149949

theorem tailTrace_1957034 : CollatzResearch.WordTrace tailWord_1957034 prefixEnd_1957034 223310910931378073149949 := by
  unfold tailWord_1957034
  simp only [CollatzResearch.WordTrace]
  refine ⟨17844723498001881910629539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47585929328005018428345437 17844723498001881910629539)
  ·
    refine ⟨26767085247002822865944309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17844723498001881910629539 26767085247002822865944309)
    ·
      refine ⟨2509414241906514643682279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26767085247002822865944309 2509414241906514643682279)
      ·
        refine ⟨3764121362859771965523419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509414241906514643682279 3764121362859771965523419)
        ·
          refine ⟨5646182044289657948285129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764121362859771965523419 5646182044289657948285129)
          ·
            refine ⟨4234636533217243461213847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5646182044289657948285129 4234636533217243461213847)
            ·
              refine ⟨6351954799825865191820771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234636533217243461213847 6351954799825865191820771)
              ·
                refine ⟨9527932199738797787731157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351954799825865191820771 9527932199738797787731157)
                ·
                  refine ⟨223310910931378073149949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9527932199738797787731157 223310910931378073149949)
                  ·
                    rfl

theorem cell22_1957034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_1957034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957034 prefixEnd_1957034 := by exact prefixLift 1957034
  have htrace : WordTrace (prefixWord ++ tailWord_1957034) baseStart_1957034 baseEnd_1957034 := by
    simpa [prefixWord, tailWord_1957034, baseEnd_1957034] using wordTrace_append hprefix tailTrace_1957034
  have hstable : (prefixWord ++ tailWord_1957034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957034).length < 2 ^ (prefixWord ++ tailWord_1957034).sum := by decide
  have hdescent : baseEnd_1957034 < baseStart_1957034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957079 : List Nat := [1, 1, 3, 2, 1, 2, 5, 3, 4]
def baseStart_1957079 : Nat := 118140960795 + 1957079 * 2 ^ 59
def prefixEnd_1957079 : Nat := 4983230072969 + 3 ^ 40 * 1957079 * 2
def baseEnd_1957079 : Nat := 223316045737923034024903

theorem tailTrace_1957079 : CollatzResearch.WordTrace tailWord_1957079 prefixEnd_1957079 223316045737923034024903 := by
  unfold tailWord_1957079
  simp only [CollatzResearch.WordTrace]
  refine ⟨71380535276844500327906291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47587023517896333551937527 71380535276844500327906291)
  ·
    refine ⟨107070802915266750491859437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71380535276844500327906291 107070802915266750491859437)
    ·
      refine ⟨40151551093225031434447289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107070802915266750491859437 40151551093225031434447289)
      ·
        refine ⟨30113663319918773575835467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40151551093225031434447289 30113663319918773575835467)
        ·
          refine ⟨45170494979878160363753201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30113663319918773575835467 45170494979878160363753201)
          ·
            refine ⟨33877871234908620272814901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45170494979878160363753201 33877871234908620272814901)
            ·
              refine ⟨3176050428272683150576397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33877871234908620272814901 3176050428272683150576397)
              ·
                refine ⟨1191018910602256181466149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3176050428272683150576397 1191018910602256181466149)
                ·
                  refine ⟨223316045737923034024903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1191018910602256181466149 223316045737923034024903)
                  ·
                    rfl

theorem cell22_1957079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 4].length) (baseStart_1957079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957079 prefixEnd_1957079 := by exact prefixLift 1957079
  have htrace : WordTrace (prefixWord ++ tailWord_1957079) baseStart_1957079 baseEnd_1957079 := by
    simpa [prefixWord, tailWord_1957079, baseEnd_1957079] using wordTrace_append hprefix tailTrace_1957079
  have hstable : (prefixWord ++ tailWord_1957079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957079).length < 2 ^ (prefixWord ++ tailWord_1957079).sum := by decide
  have hdescent : baseEnd_1957079 < baseStart_1957079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957092 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_1957092 : Nat := 118140960795 + 1957092 * 2 ^ 59
def prefixEnd_1957092 : Nat := 4983230072969 + 3 ^ 40 * 1957092 * 2
def baseEnd_1957092 : Nat := 669952587379441401499669

theorem tailTrace_1957092 : CollatzResearch.WordTrace tailWord_1957092 prefixEnd_1957092 669952587379441401499669 := by
  unfold tailWord_1957092
  simp only [CollatzResearch.WordTrace]
  refine ⟨35690504712898701774064765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47587339617198269032086353 35690504712898701774064765)
  ·
    refine ⟨13383939267337013165274287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35690504712898701774064765 13383939267337013165274287)
    ·
      refine ⟨20075908901005519747911431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13383939267337013165274287 20075908901005519747911431)
      ·
        refine ⟨30113863351508279621867147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20075908901005519747911431 30113863351508279621867147)
        ·
          refine ⟨45170795027262419432800721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30113863351508279621867147 45170795027262419432800721)
          ·
            refine ⟨33878096270446814574600541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45170795027262419432800721 33878096270446814574600541)
            ·
              refine ⟨12704286101417555465475203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33878096270446814574600541 12704286101417555465475203)
              ·
                refine ⟨19056429152126333198212805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12704286101417555465475203 19056429152126333198212805)
                ·
                  refine ⟨3573080466023687474664901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19056429152126333198212805 3573080466023687474664901)
                  ·
                    refine ⟨669952587379441401499669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573080466023687474664901 669952587379441401499669)
                    ·
                      rfl

theorem cell22_1957092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_1957092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957092 prefixEnd_1957092 := by exact prefixLift 1957092
  have htrace : WordTrace (prefixWord ++ tailWord_1957092) baseStart_1957092 baseEnd_1957092 := by
    simpa [prefixWord, tailWord_1957092, baseEnd_1957092] using wordTrace_append hprefix tailTrace_1957092
  have hstable : (prefixWord ++ tailWord_1957092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957092).length < 2 ^ (prefixWord ++ tailWord_1957092).sum := by decide
  have hdescent : baseEnd_1957092 < baseStart_1957092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957096 : List Nat := [2, 1, 4, 1, 2, 1, 5, 2, 4]
def baseStart_1957096 : Nat := 118140960795 + 1957096 * 2 ^ 59
def prefixEnd_1957096 : Nat := 4983230072969 + 3 ^ 40 * 1957096 * 2
def baseEnd_1957096 : Nat := 223317985553728908133219

theorem tailTrace_1957096 : CollatzResearch.WordTrace tailWord_1957096 prefixEnd_1957096 223317985553728908133219 := by
  unfold tailWord_1957096
  simp only [CollatzResearch.WordTrace]
  refine ⟨35690577658891456115637571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47587436878521941487516761 35690577658891456115637571)
  ·
    refine ⟨53535866488337184173456357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35690577658891456115637571 53535866488337184173456357)
    ·
      refine ⟨10037974966563222032523067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53535866488337184173456357 10037974966563222032523067)
      ·
        refine ⟨15056962449844833048784601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037974966563222032523067 15056962449844833048784601)
        ·
          refine ⟨11292721837383624786588451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15056962449844833048784601 11292721837383624786588451)
          ·
            refine ⟨16939082756075437179882677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292721837383624786588451 16939082756075437179882677)
            ·
              refine ⟨1588039008382072235614001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16939082756075437179882677 1588039008382072235614001)
              ·
                refine ⟨1191029256286554176710501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1588039008382072235614001 1191029256286554176710501)
                ·
                  refine ⟨223317985553728908133219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1191029256286554176710501 223317985553728908133219)
                  ·
                    rfl

theorem cell22_1957096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 4].length) (baseStart_1957096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957096 prefixEnd_1957096 := by exact prefixLift 1957096
  have htrace : WordTrace (prefixWord ++ tailWord_1957096) baseStart_1957096 baseEnd_1957096 := by
    simpa [prefixWord, tailWord_1957096, baseEnd_1957096] using wordTrace_append hprefix tailTrace_1957096
  have hstable : (prefixWord ++ tailWord_1957096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957096).length < 2 ^ (prefixWord ++ tailWord_1957096).sum := by decide
  have hdescent : baseEnd_1957096 < baseStart_1957096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957107 : List Nat := [1, 1, 1, 2, 2, 6, 2, 7]
def baseStart_1957107 : Nat := 118140960795 + 1957107 * 2 ^ 59
def prefixEnd_1957107 : Nat := 4983230072969 + 3 ^ 40 * 1957107 * 2
def baseEnd_1957107 : Nat := 74439746909554040263847

theorem tailTrace_1957107 : CollatzResearch.WordTrace tailWord_1957107 prefixEnd_1957107 74439746909554040263847 := by
  unfold tailWord_1957107
  simp only [CollatzResearch.WordTrace]
  refine ⟨71381556520743061109925575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47587704347162040739950383 71381556520743061109925575)
  ·
    refine ⟨107072334781114591664888363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71381556520743061109925575 107072334781114591664888363)
    ·
      refine ⟨160608502171671887497332545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107072334781114591664888363 160608502171671887497332545)
      ·
        refine ⟨120456376628753915622999409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160608502171671887497332545 120456376628753915622999409)
        ·
          refine ⟨90342282471565436717249557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120456376628753915622999409 90342282471565436717249557)
          ·
            refine ⟨4234794490854629846121073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90342282471565436717249557 4234794490854629846121073)
            ·
              refine ⟨3176095868140972384590805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234794490854629846121073 3176095868140972384590805)
              ·
                refine ⟨74439746909554040263847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3176095868140972384590805 74439746909554040263847)
                ·
                  rfl

theorem cell22_1957107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 7].length) (baseStart_1957107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957107 prefixEnd_1957107 := by exact prefixLift 1957107
  have htrace : WordTrace (prefixWord ++ tailWord_1957107) baseStart_1957107 baseEnd_1957107 := by
    simpa [prefixWord, tailWord_1957107, baseEnd_1957107] using wordTrace_append hprefix tailTrace_1957107
  have hstable : (prefixWord ++ tailWord_1957107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957107).length < 2 ^ (prefixWord ++ tailWord_1957107).sum := by decide
  have hdescent : baseEnd_1957107 < baseStart_1957107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957169 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 5]
def baseStart_1957169 : Nat := 118140960795 + 1957169 * 2 ^ 59
def prefixEnd_1957169 : Nat := 4983230072969 + 3 ^ 40 * 1957169 * 2
def baseEnd_1957169 : Nat := 223326315351012955774811

theorem tailTrace_1957169 : CollatzResearch.WordTrace tailWord_1957169 prefixEnd_1957169 223326315351012955774811 := by
  unfold tailWord_1957169
  simp only [CollatzResearch.WordTrace]
  refine ⟨71383817846518445698682561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47589211897678963799121707 71383817846518445698682561)
  ·
    refine ⟨53537863384888834274011921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71383817846518445698682561 53537863384888834274011921)
    ·
      refine ⟨40153397538666625705508941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53537863384888834274011921 40153397538666625705508941)
      ·
        refine ⟨15057524076999984639565853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40153397538666625705508941 15057524076999984639565853)
        ·
          refine ⟨5646571528874994239837195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15057524076999984639565853 5646571528874994239837195)
          ·
            refine ⟨8469857293312491359755793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5646571528874994239837195 8469857293312491359755793)
            ·
              refine ⟨6352392969984368519816845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8469857293312491359755793 6352392969984368519816845)
              ·
                refine ⟨2382147363744138194931317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6352392969984368519816845 2382147363744138194931317)
                ·
                  refine ⟨223326315351012955774811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2382147363744138194931317 223326315351012955774811)
                  ·
                    rfl

theorem cell22_1957169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_1957169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957169 prefixEnd_1957169 := by exact prefixLift 1957169
  have htrace : WordTrace (prefixWord ++ tailWord_1957169) baseStart_1957169 baseEnd_1957169 := by
    simpa [prefixWord, tailWord_1957169, baseEnd_1957169] using wordTrace_append hprefix tailTrace_1957169
  have hstable : (prefixWord ++ tailWord_1957169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957169).length < 2 ^ (prefixWord ++ tailWord_1957169).sum := by decide
  have hdescent : baseEnd_1957169 < baseStart_1957169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957242 : List Nat := [3, 1, 1, 1, 1, 1, 2, 12]
def baseStart_1957242 : Nat := 118140960795 + 1957242 * 2 ^ 59
def prefixEnd_1957242 : Nat := 4983230072969 + 3 ^ 40 * 1957242 * 2
def baseEnd_1957242 : Nat := 74444881716099001138801

theorem tailTrace_1957242 : CollatzResearch.WordTrace tailWord_1957242 prefixEnd_1957242 74444881716099001138801 := by
  unfold tailWord_1957242
  simp only [CollatzResearch.WordTrace]
  refine ⟨17846620093813494791522495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47590986916835986110726653 17846620093813494791522495)
  ·
    refine ⟨26769930140720242187283743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17846620093813494791522495 26769930140720242187283743)
    ·
      refine ⟨40154895211080363280925615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26769930140720242187283743 40154895211080363280925615)
      ·
        refine ⟨60232342816620544921388423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40154895211080363280925615 60232342816620544921388423)
        ·
          refine ⟨90348514224930817382082635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60232342816620544921388423 90348514224930817382082635)
          ·
            refine ⟨135522771337396226073123953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90348514224930817382082635 135522771337396226073123953)
            ·
              refine ⟨101642078503047169554842965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135522771337396226073123953 101642078503047169554842965)
              ·
                refine ⟨74444881716099001138801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 101642078503047169554842965 74444881716099001138801)
                ·
                  rfl

theorem cell22_1957242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_1957242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957242 prefixEnd_1957242 := by exact prefixLift 1957242
  have htrace : WordTrace (prefixWord ++ tailWord_1957242) baseStart_1957242 baseEnd_1957242 := by
    simpa [prefixWord, tailWord_1957242, baseEnd_1957242] using wordTrace_append hprefix tailTrace_1957242
  have hstable : (prefixWord ++ tailWord_1957242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957242).length < 2 ^ (prefixWord ++ tailWord_1957242).sum := by decide
  have hdescent : baseEnd_1957242 < baseStart_1957242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957244 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_1957244 : Nat := 118140960795 + 1957244 * 2 ^ 59
def prefixEnd_1957244 : Nat := 4983230072969 + 3 ^ 40 * 1957244 * 2
def baseEnd_1957244 : Nat := 670004620085763671699203

theorem tailTrace_1957244 : CollatzResearch.WordTrace tailWord_1957244 prefixEnd_1957244 670004620085763671699203 := by
  unfold tailWord_1957244
  simp only [CollatzResearch.WordTrace]
  refine ⟨35693276660623366753831393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47591035547497822338441857 35693276660623366753831393)
  ·
    refine ⟨26769957495467525065373545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35693276660623366753831393 26769957495467525065373545)
    ·
      refine ⟨20077468121600643799030159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26769957495467525065373545 20077468121600643799030159)
      ·
        refine ⟨30116202182400965698545239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20077468121600643799030159 30116202182400965698545239)
        ·
          refine ⟨45174303273601448547817859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30116202182400965698545239 45174303273601448547817859)
          ·
            refine ⟨67761454910402172821726789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45174303273601448547817859 67761454910402172821726789)
            ·
              refine ⟨12705272795700407404073773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67761454910402172821726789 12705272795700407404073773)
              ·
                refine ⟨4764477298387652776527665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12705272795700407404073773 4764477298387652776527665)
                ·
                  refine ⟨3573357973790739582395749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764477298387652776527665 3573357973790739582395749)
                  ·
                    refine ⟨670004620085763671699203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573357973790739582395749 670004620085763671699203)
                    ·
                      rfl

theorem cell22_1957244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_1957244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957244 prefixEnd_1957244 := by exact prefixLift 1957244
  have htrace : WordTrace (prefixWord ++ tailWord_1957244) baseStart_1957244 baseEnd_1957244 := by
    simpa [prefixWord, tailWord_1957244, baseEnd_1957244] using wordTrace_append hprefix tailTrace_1957244
  have hstable : (prefixWord ++ tailWord_1957244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957244).length < 2 ^ (prefixWord ++ tailWord_1957244).sum := by decide
  have hdescent : baseEnd_1957244 < baseStart_1957244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957319 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1957319 : Nat := 118140960795 + 1957319 * 2 ^ 59
def prefixEnd_1957319 : Nat := 4983230072969 + 3 ^ 40 * 1957319 * 2
def baseEnd_1957319 : Nat := 670030294118488476073973

theorem tailTrace_1957319 : CollatzResearch.WordTrace tailWord_1957319 prefixEnd_1957319 670030294118488476073973 := by
  unfold tailWord_1957319
  simp only [CollatzResearch.WordTrace]
  refine ⟨71389288795975021316643011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47592859197316680877762007 71389288795975021316643011)
  ·
    refine ⟨107083933193962531974964517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71389288795975021316643011 107083933193962531974964517)
    ·
      refine ⟨20078237473867974745305847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107083933193962531974964517 20078237473867974745305847)
      ·
        refine ⟨30117356210801962117958771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20078237473867974745305847 30117356210801962117958771)
        ·
          refine ⟨45176034316202943176938157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30117356210801962117958771 45176034316202943176938157)
          ·
            refine ⟨16941012868576103691351809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45176034316202943176938157 16941012868576103691351809)
            ·
              refine ⟨12705759651432077768513857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16941012868576103691351809 12705759651432077768513857)
              ·
                refine ⟨9529319738574058326385393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12705759651432077768513857 9529319738574058326385393)
                ·
                  refine ⟨7146989803930543744789045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9529319738574058326385393 7146989803930543744789045)
                  ·
                    refine ⟨670030294118488476073973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7146989803930543744789045 670030294118488476073973)
                    ·
                      rfl

theorem cell22_1957319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1957319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957319 prefixEnd_1957319 := by exact prefixLift 1957319
  have htrace : WordTrace (prefixWord ++ tailWord_1957319) baseStart_1957319 baseEnd_1957319 := by
    simpa [prefixWord, tailWord_1957319, baseEnd_1957319] using wordTrace_append hprefix tailTrace_1957319
  have hstable : (prefixWord ++ tailWord_1957319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957319).length < 2 ^ (prefixWord ++ tailWord_1957319).sum := by decide
  have hdescent : baseEnd_1957319 < baseStart_1957319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957351 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1957351 : Nat := 118140960795 + 1957351 * 2 ^ 59
def prefixEnd_1957351 : Nat := 4983230072969 + 3 ^ 40 * 1957351 * 2
def baseEnd_1957351 : Nat := 670041248372451059273875

theorem tailTrace_1957351 : CollatzResearch.WordTrace tailWord_1957351 prefixEnd_1957351 670041248372451059273875 := by
  unfold tailWord_1957351
  simp only [CollatzResearch.WordTrace]
  refine ⟨71390455931859090781807907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47593637287906060521205271 71390455931859090781807907)
  ·
    refine ⟨107085683897788636172711861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71390455931859090781807907 107085683897788636172711861)
    ·
      refine ⟨10039282865417684641191737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107085683897788636172711861 10039282865417684641191737)
      ·
        refine ⟨7529462149063263480893803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10039282865417684641191737 7529462149063263480893803)
        ·
          refine ⟨11294193223594895221340705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7529462149063263480893803 11294193223594895221340705)
          ·
            refine ⟨8470644917696171416005529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11294193223594895221340705 8470644917696171416005529)
            ·
              refine ⟨6352983688272128562004147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8470644917696171416005529 6352983688272128562004147)
              ·
                refine ⟨9529475532408192843006221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352983688272128562004147 9529475532408192843006221)
                ·
                  refine ⟨3573553324653072316127333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9529475532408192843006221 3573553324653072316127333)
                  ·
                    refine ⟨670041248372451059273875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573553324653072316127333 670041248372451059273875)
                    ·
                      rfl

theorem cell22_1957351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1957351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957351 prefixEnd_1957351 := by exact prefixLift 1957351
  have htrace : WordTrace (prefixWord ++ tailWord_1957351) baseStart_1957351 baseEnd_1957351 := by
    simpa [prefixWord, tailWord_1957351, baseEnd_1957351] using wordTrace_append hprefix tailTrace_1957351
  have hstable : (prefixWord ++ tailWord_1957351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957351).length < 2 ^ (prefixWord ++ tailWord_1957351).sum := by decide
  have hdescent : baseEnd_1957351 < baseStart_1957351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957368 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 1, 4]
def baseStart_1957368 : Nat := 118140960795 + 1957368 * 2 ^ 59
def prefixEnd_1957368 : Nat := 4983230072969 + 3 ^ 40 * 1957368 * 2
def baseEnd_1957368 : Nat := 670047067819868681598823

theorem tailTrace_1957368 : CollatzResearch.WordTrace tailWord_1957368 prefixEnd_1957368 670047067819868681598823 := by
  unfold tailWord_1957368
  simp only [CollatzResearch.WordTrace]
  refine ⟨35695537986398751342588379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47594050648531668456784505 35695537986398751342588379)
  ·
    refine ⟨53543306979598127013882569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35695537986398751342588379 53543306979598127013882569)
    ·
      refine ⟨40157480234698595260411927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53543306979598127013882569 40157480234698595260411927)
      ·
        refine ⟨60236220352047892890617891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40157480234698595260411927 60236220352047892890617891)
        ·
          refine ⟨90354330528071839335926837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60236220352047892890617891 90354330528071839335926837)
          ·
            refine ⟨8470718487006734937743141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90354330528071839335926837 8470718487006734937743141)
            ·
              refine ⟨1588259716313762800826839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8470718487006734937743141 1588259716313762800826839)
              ·
                refine ⟨2382389574470644201240259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588259716313762800826839 2382389574470644201240259)
                ·
                  refine ⟨3573584361705966301860389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382389574470644201240259 3573584361705966301860389)
                  ·
                    refine ⟨670047067819868681598823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573584361705966301860389 670047067819868681598823)
                    ·
                      rfl

theorem cell22_1957368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_1957368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957368 prefixEnd_1957368 := by exact prefixLift 1957368
  have htrace : WordTrace (prefixWord ++ tailWord_1957368) baseStart_1957368 baseEnd_1957368 := by
    simpa [prefixWord, tailWord_1957368, baseEnd_1957368] using wordTrace_append hprefix tailTrace_1957368
  have hstable : (prefixWord ++ tailWord_1957368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957368).length < 2 ^ (prefixWord ++ tailWord_1957368).sum := by decide
  have hdescent : baseEnd_1957368 < baseStart_1957368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957383 : List Nat := [1, 1, 4, 3, 2, 1, 2, 4, 4]
def baseStart_1957383 : Nat := 118140960795 + 1957383 * 2 ^ 59
def prefixEnd_1957383 : Nat := 4983230072969 + 3 ^ 40 * 1957383 * 2
def baseEnd_1957383 : Nat := 223350734208804547491259

theorem tailTrace_1957383 : CollatzResearch.WordTrace tailWord_1957383 prefixEnd_1957383 223350734208804547491259 := by
  unfold tailWord_1957383
  simp only [CollatzResearch.WordTrace]
  refine ⟨71391623067743160246972803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47594415378495440164648535 71391623067743160246972803)
  ·
    refine ⟨107087434601614740370459205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71391623067743160246972803 107087434601614740370459205)
    ·
      refine ⟨20078893987802763819461101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107087434601614740370459205 20078893987802763819461101)
      ·
        refine ⟨7529585245426036432297913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20078893987802763819461101 7529585245426036432297913)
        ·
          refine ⟨5647188934069527324223435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7529585245426036432297913 5647188934069527324223435)
          ·
            refine ⟨8470783401104290986335153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647188934069527324223435 8470783401104290986335153)
            ·
              refine ⟨6353087550828218239751365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8470783401104290986335153 6353087550828218239751365)
              ·
                refine ⟨1191203915780290919953381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6353087550828218239751365 1191203915780290919953381)
                ·
                  refine ⟨223350734208804547491259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1191203915780290919953381 223350734208804547491259)
                  ·
                    rfl

theorem cell22_1957383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 4].length) (baseStart_1957383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957383 prefixEnd_1957383 := by exact prefixLift 1957383
  have htrace : WordTrace (prefixWord ++ tailWord_1957383) baseStart_1957383 baseEnd_1957383 := by
    simpa [prefixWord, tailWord_1957383, baseEnd_1957383] using wordTrace_append hprefix tailTrace_1957383
  have hstable : (prefixWord ++ tailWord_1957383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957383).length < 2 ^ (prefixWord ++ tailWord_1957383).sum := by decide
  have hdescent : baseEnd_1957383 < baseStart_1957383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957411 : List Nat := [1, 1, 1, 4, 5, 1, 1, 8]
def baseStart_1957411 : Nat := 118140960795 + 1957411 * 2 ^ 59
def prefixEnd_1957411 : Nat := 4983230072969 + 3 ^ 40 * 1957411 * 2
def baseEnd_1957411 : Nat := 74451309733181211419299

theorem tailTrace_1957411 : CollatzResearch.WordTrace tailWord_1957411 prefixEnd_1957411 74451309733181211419299 := by
  unfold tailWord_1957411
  simp only [CollatzResearch.WordTrace]
  refine ⟨71392644311641721028992087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47595096207761147352661391 71392644311641721028992087)
  ·
    refine ⟨107088966467462581543488131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71392644311641721028992087 107088966467462581543488131)
    ·
      refine ⟨160633449701193872315232197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107088966467462581543488131 160633449701193872315232197)
      ·
        refine ⟨30118771818973851059106037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160633449701193872315232197 30118771818973851059106037)
        ·
          refine ⟨2823634858028798536791191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30118771818973851059106037 2823634858028798536791191)
          ·
            refine ⟨4235452287043197805186787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823634858028798536791191 4235452287043197805186787)
            ·
              refine ⟨6353178430564796707780181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4235452287043197805186787 6353178430564796707780181)
              ·
                refine ⟨74451309733181211419299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6353178430564796707780181 74451309733181211419299)
                ·
                  rfl

theorem cell22_1957411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 8].length) (baseStart_1957411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957411 prefixEnd_1957411 := by exact prefixLift 1957411
  have htrace : WordTrace (prefixWord ++ tailWord_1957411) baseStart_1957411 baseEnd_1957411 := by
    simpa [prefixWord, tailWord_1957411, baseEnd_1957411] using wordTrace_append hprefix tailTrace_1957411
  have hstable : (prefixWord ++ tailWord_1957411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957411).length < 2 ^ (prefixWord ++ tailWord_1957411).sum := by decide
  have hdescent : baseEnd_1957411 < baseStart_1957411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957424 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_1957424 : Nat := 118140960795 + 1957424 * 2 ^ 59
def prefixEnd_1957424 : Nat := 4983230072969 + 3 ^ 40 * 1957424 * 2
def baseEnd_1957424 : Nat := 670066237764303202198651

theorem tailTrace_1957424 : CollatzResearch.WordTrace tailWord_1957424 prefixEnd_1957424 670066237764303202198651 := by
  unfold tailWord_1957424
  simp only [CollatzResearch.WordTrace]
  refine ⟨35696559230297312124607663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47595412307063082832810217 35696559230297312124607663)
  ·
    refine ⟨53544838845445968186911495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35696559230297312124607663 53544838845445968186911495)
    ·
      refine ⟨80317258268168952280367243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53544838845445968186911495 80317258268168952280367243)
      ·
        refine ⟨120475887402253428420550865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80317258268168952280367243 120475887402253428420550865)
        ·
          refine ⟨90356915551690071315413149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120475887402253428420550865 90356915551690071315413149)
          ·
            refine ⟨33883843331883776743279931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90356915551690071315413149 33883843331883776743279931)
            ·
              refine ⟨50825764997825665114919897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33883843331883776743279931 50825764997825665114919897)
              ·
                refine ⟨38119323748369248836189923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50825764997825665114919897 38119323748369248836189923)
                ·
                  refine ⟨57178985622553873254284885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38119323748369248836189923 57178985622553873254284885)
                  ·
                    refine ⟨670066237764303202198651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57178985622553873254284885 670066237764303202198651)
                    ·
                      rfl

theorem cell22_1957424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_1957424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957424 prefixEnd_1957424 := by exact prefixLift 1957424
  have htrace : WordTrace (prefixWord ++ tailWord_1957424) baseStart_1957424 baseEnd_1957424 := by
    simpa [prefixWord, tailWord_1957424, baseEnd_1957424] using wordTrace_append hprefix tailTrace_1957424
  have hstable : (prefixWord ++ tailWord_1957424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957424).length < 2 ^ (prefixWord ++ tailWord_1957424).sum := by decide
  have hdescent : baseEnd_1957424 < baseStart_1957424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957430 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1957430 : Nat := 118140960795 + 1957430 * 2 ^ 59
def prefixEnd_1957430 : Nat := 4983230072969 + 3 ^ 40 * 1957430 * 2
def baseEnd_1957430 : Nat := 670068291686921186548633

theorem tailTrace_1957430 : CollatzResearch.WordTrace tailWord_1957430 prefixEnd_1957430 670068291686921186548633 := by
  unfold tailWord_1957430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462083581160805454620859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47595558199048591515955829 4462083581160805454620859)
  ·
    refine ⟨6693125371741208181931289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4462083581160805454620859 6693125371741208181931289)
    ·
      refine ⟨5019844028805906136448467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6693125371741208181931289 5019844028805906136448467)
      ·
        refine ⟨7529766043208859204672701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019844028805906136448467 7529766043208859204672701)
        ·
          refine ⟨2823662266203322201752263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7529766043208859204672701 2823662266203322201752263)
          ·
            refine ⟨4235493399304983302628395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823662266203322201752263 4235493399304983302628395)
            ·
              refine ⟨6353240098957474953942593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4235493399304983302628395 6353240098957474953942593)
              ·
                refine ⟨4764930074218106215456945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6353240098957474953942593 4764930074218106215456945)
                ·
                  refine ⟨3573697555663579661592709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764930074218106215456945 3573697555663579661592709)
                  ·
                    refine ⟨670068291686921186548633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573697555663579661592709 670068291686921186548633)
                    ·
                      rfl

theorem cell22_1957430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1957430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957430 prefixEnd_1957430 := by exact prefixLift 1957430
  have htrace : WordTrace (prefixWord ++ tailWord_1957430) baseStart_1957430 baseEnd_1957430 := by
    simpa [prefixWord, tailWord_1957430, baseEnd_1957430] using wordTrace_append hprefix tailTrace_1957430
  have hstable : (prefixWord ++ tailWord_1957430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957430).length < 2 ^ (prefixWord ++ tailWord_1957430).sum := by decide
  have hdescent : baseEnd_1957430 < baseStart_1957430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957441 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1957441 : Nat := 118140960795 + 1957441 * 2 ^ 59
def prefixEnd_1957441 : Nat := 4983230072969 + 3 ^ 40 * 1957441 * 2
def baseEnd_1957441 : Nat := 670072057211720824523599

theorem tailTrace_1957441 : CollatzResearch.WordTrace tailWord_1957441 prefixEnd_1957441 670072057211720824523599 := by
  unfold tailWord_1957441
  simp only [CollatzResearch.WordTrace]
  refine ⟨71393738501533036152584177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47595825667688690768389451 71393738501533036152584177)
  ·
    refine ⟨53545303876149777114438133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71393738501533036152584177 53545303876149777114438133)
    ·
      refine ⟨5019872238389041604478575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53545303876149777114438133 5019872238389041604478575)
      ·
        refine ⟨7529808357583562406717863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019872238389041604478575 7529808357583562406717863)
        ·
          refine ⟨11294712536375343610076795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7529808357583562406717863 11294712536375343610076795)
          ·
            refine ⟨16942068804563015415115193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11294712536375343610076795 16942068804563015415115193)
            ·
              refine ⟨12706551603422261561336395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16942068804563015415115193 12706551603422261561336395)
              ·
                refine ⟨19059827405133392342004593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12706551603422261561336395 19059827405133392342004593)
                ·
                  refine ⟨14294870553850044256503445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19059827405133392342004593 14294870553850044256503445)
                  ·
                    refine ⟨670072057211720824523599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14294870553850044256503445 670072057211720824523599)
                    ·
                      rfl

theorem cell22_1957441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1957441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957441 prefixEnd_1957441 := by exact prefixLift 1957441
  have htrace : WordTrace (prefixWord ++ tailWord_1957441) baseStart_1957441 baseEnd_1957441 := by
    simpa [prefixWord, tailWord_1957441, baseEnd_1957441] using wordTrace_append hprefix tailTrace_1957441
  have hstable : (prefixWord ++ tailWord_1957441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957441).length < 2 ^ (prefixWord ++ tailWord_1957441).sum := by decide
  have hdescent : baseEnd_1957441 < baseStart_1957441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957456 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 5]
def baseStart_1957456 : Nat := 118140960795 + 1957456 * 2 ^ 59
def prefixEnd_1957456 : Nat := 4983230072969 + 3 ^ 40 * 1957456 * 2
def baseEnd_1957456 : Nat := 223359064006088595132851

theorem tailTrace_1957456 : CollatzResearch.WordTrace tailWord_1957456 prefixEnd_1957456 223359064006088595132851 := by
  unfold tailWord_1957456
  simp only [CollatzResearch.WordTrace]
  refine ⟨35697142798239346857190111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47596190397652462476253481 35697142798239346857190111)
  ·
    refine ⟨53545714197359020285785167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35697142798239346857190111 53545714197359020285785167)
    ·
      refine ⟨80318571296038530428677751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53545714197359020285785167 80318571296038530428677751)
      ·
        refine ⟨120477856944057795643016627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80318571296038530428677751 120477856944057795643016627)
        ·
          refine ⟨180716785416086693464524941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120477856944057795643016627 180716785416086693464524941)
          ·
            refine ⟨67768794531032510049196853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180716785416086693464524941 67768794531032510049196853)
            ·
              refine ⟨6353324487284297817112205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67768794531032510049196853 6353324487284297817112205)
              ·
                refine ⟨2382496682731611681417077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6353324487284297817112205 2382496682731611681417077)
                ·
                  refine ⟨223359064006088595132851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2382496682731611681417077 223359064006088595132851)
                  ·
                    rfl

theorem cell22_1957456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_1957456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957456 prefixEnd_1957456 := by exact prefixLift 1957456
  have htrace : WordTrace (prefixWord ++ tailWord_1957456) baseStart_1957456 baseEnd_1957456 := by
    simpa [prefixWord, tailWord_1957456, baseEnd_1957456] using wordTrace_append hprefix tailTrace_1957456
  have hstable : (prefixWord ++ tailWord_1957456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957456).length < 2 ^ (prefixWord ++ tailWord_1957456).sum := by decide
  have hdescent : baseEnd_1957456 < baseStart_1957456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957494 : List Nat := [5, 1, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_1957494 : Nat := 118140960795 + 1957494 * 2 ^ 59
def prefixEnd_1957494 : Nat := 4983230072969 + 3 ^ 40 * 1957494 * 2
def baseEnd_1957494 : Nat := 670090200194846352948437

theorem tailTrace_1957494 : CollatzResearch.WordTrace tailWord_1957494 prefixEnd_1957494 670090200194846352948437 := by
  unfold tailWord_1957494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462229473146314137766471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47597114380227350802842357 4462229473146314137766471)
  ·
    refine ⟨6693344209719471206649707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4462229473146314137766471 6693344209719471206649707)
    ·
      refine ⟨10040016314579206809974561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6693344209719471206649707 10040016314579206809974561)
      ·
        refine ⟨7530012235934405107480921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10040016314579206809974561 7530012235934405107480921)
        ·
          refine ⟨5647509176950803830610691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7530012235934405107480921 5647509176950803830610691)
          ·
            refine ⟨8471263765426205745916037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647509176950803830610691 8471263765426205745916037)
            ·
              refine ⟨1588361956017413577359257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8471263765426205745916037 1588361956017413577359257)
              ·
                refine ⟨1191271467013060183019443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1588361956017413577359257 1191271467013060183019443)
                ·
                  refine ⟨1786907200519590274529165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191271467013060183019443 1786907200519590274529165)
                  ·
                    refine ⟨670090200194846352948437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1786907200519590274529165 670090200194846352948437)
                    ·
                      rfl

theorem cell22_1957494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_1957494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957494 prefixEnd_1957494 := by exact prefixLift 1957494
  have htrace : WordTrace (prefixWord ++ tailWord_1957494) baseStart_1957494 baseEnd_1957494 := by
    simpa [prefixWord, tailWord_1957494, baseEnd_1957494] using wordTrace_append hprefix tailTrace_1957494
  have hstable : (prefixWord ++ tailWord_1957494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957494).length < 2 ^ (prefixWord ++ tailWord_1957494).sum := by decide
  have hdescent : baseEnd_1957494 < baseStart_1957494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957518 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_1957518 : Nat := 118140960795 + 1957518 * 2 ^ 59
def prefixEnd_1957518 : Nat := 4983230072969 + 3 ^ 40 * 1957518 * 2
def baseEnd_1957518 : Nat := 223366138628439430116121

theorem tailTrace_1957518 : CollatzResearch.WordTrace tailWord_1957518 prefixEnd_1957518 223366138628439430116121 := by
  unfold tailWord_1957518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8924568365281759787892151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47597697948169385535424805 8924568365281759787892151)
  ·
    refine ⟨13386852547922639681838227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8924568365281759787892151 13386852547922639681838227)
    ·
      refine ⟨20080278821883959522757341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13386852547922639681838227 20080278821883959522757341)
      ·
        refine ⟨7530104558206484821034003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20080278821883959522757341 7530104558206484821034003)
        ·
          refine ⟨11295156837309727231551005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7530104558206484821034003 11295156837309727231551005)
          ·
            refine ⟨4235683813991147711831627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11295156837309727231551005 4235683813991147711831627)
            ·
              refine ⟨6353525720986721567747441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4235683813991147711831627 6353525720986721567747441)
              ·
                refine ⟨4765144290740041175810581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6353525720986721567747441 4765144290740041175810581)
                ·
                  refine ⟨223366138628439430116121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4765144290740041175810581 223366138628439430116121)
                  ·
                    rfl

theorem cell22_1957518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_1957518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957518 prefixEnd_1957518 := by exact prefixLift 1957518
  have htrace : WordTrace (prefixWord ++ tailWord_1957518) baseStart_1957518 baseEnd_1957518 := by
    simpa [prefixWord, tailWord_1957518, baseEnd_1957518] using wordTrace_append hprefix tailTrace_1957518
  have hstable : (prefixWord ++ tailWord_1957518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957518).length < 2 ^ (prefixWord ++ tailWord_1957518).sum := by decide
  have hdescent : baseEnd_1957518 < baseStart_1957518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957533 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1957533 : Nat := 118140960795 + 1957533 * 2 ^ 59
def prefixEnd_1957533 : Nat := 4983230072969 + 3 ^ 40 * 1957533 * 2
def baseEnd_1957533 : Nat := 670103550691863251223317

theorem tailTrace_1957533 : CollatzResearch.WordTrace tailWord_1957533 prefixEnd_1957533 670103550691863251223317 := by
  unfold tailWord_1957533
  simp only [CollatzResearch.WordTrace]
  refine ⟨71397094017199735864933253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47598062678133157243288835 71397094017199735864933253)
  ·
    refine ⟨13386955128224950474674985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71397094017199735864933253 13386955128224950474674985)
    ·
      refine ⟨10040216346168712856006239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13386955128224950474674985 10040216346168712856006239)
      ·
        refine ⟨15060324519253069284009359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10040216346168712856006239 15060324519253069284009359)
        ·
          refine ⟨22590486778879603926014039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15060324519253069284009359 22590486778879603926014039)
          ·
            refine ⟨33885730168319405889021059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22590486778879603926014039 33885730168319405889021059)
            ·
              refine ⟨50828595252479108833531589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33885730168319405889021059 50828595252479108833531589)
              ·
                refine ⟨9530361609839832906287173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50828595252479108833531589 9530361609839832906287173)
                ·
                  refine ⟨1786942801844968669928845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9530361609839832906287173 1786942801844968669928845)
                  ·
                    refine ⟨670103550691863251223317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1786942801844968669928845 670103550691863251223317)
                    ·
                      rfl

theorem cell22_1957533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1957533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957533 prefixEnd_1957533 := by exact prefixLift 1957533
  have htrace : WordTrace (prefixWord ++ tailWord_1957533) baseStart_1957533 baseEnd_1957533 := by
    simpa [prefixWord, tailWord_1957533, baseEnd_1957533] using wordTrace_append hprefix tailTrace_1957533
  have hstable : (prefixWord ++ tailWord_1957533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957533).length < 2 ^ (prefixWord ++ tailWord_1957533).sum := by decide
  have hdescent : baseEnd_1957533 < baseStart_1957533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957537 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 1, 4]
def baseStart_1957537 : Nat := 118140960795 + 1957537 * 2 ^ 59
def prefixEnd_1957537 : Nat := 4983230072969 + 3 ^ 40 * 1957537 * 2
def baseEnd_1957537 : Nat := 670104919973608574123305

theorem tailTrace_1957537 : CollatzResearch.WordTrace tailWord_1957537 prefixEnd_1957537 670104919973608574123305 := by
  unfold tailWord_1957537
  simp only [CollatzResearch.WordTrace]
  refine ⟨71397239909185244548078865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47598159939456829698719243 71397239909185244548078865)
  ·
    refine ⟨53547929931888933411059149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71397239909185244548078865 53547929931888933411059149)
    ·
      refine ⟨20080473724458350029147181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53547929931888933411059149 20080473724458350029147181)
      ·
        refine ⟨7530177646671881260930193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20080473724458350029147181 7530177646671881260930193)
        ·
          refine ⟨5647633235003910945697645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7530177646671881260930193 5647633235003910945697645)
          ·
            refine ⟨2117862463126466604636617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5647633235003910945697645 2117862463126466604636617)
            ·
              refine ⟨1588396847344849953477463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117862463126466604636617 1588396847344849953477463)
              ·
                refine ⟨2382595271017274930216195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588396847344849953477463 2382595271017274930216195)
                ·
                  refine ⟨3573892906525912395324293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382595271017274930216195 3573892906525912395324293)
                  ·
                    refine ⟨670104919973608574123305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573892906525912395324293 670104919973608574123305)
                    ·
                      rfl

theorem cell22_1957537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_1957537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957537 prefixEnd_1957537 := by exact prefixLift 1957537
  have htrace : WordTrace (prefixWord ++ tailWord_1957537) baseStart_1957537 baseEnd_1957537 := by
    simpa [prefixWord, tailWord_1957537, baseEnd_1957537] using wordTrace_append hprefix tailTrace_1957537
  have hstable : (prefixWord ++ tailWord_1957537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957537).length < 2 ^ (prefixWord ++ tailWord_1957537).sum := by decide
  have hdescent : baseEnd_1957537 < baseStart_1957537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957591 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 9]
def baseStart_1957591 : Nat := 118140960795 + 1957591 * 2 ^ 59
def prefixEnd_1957591 : Nat := 4983230072969 + 3 ^ 40 * 1957591 * 2
def baseEnd_1957591 : Nat := 223374468425723477757713

theorem tailTrace_1957591 : CollatzResearch.WordTrace tailWord_1957591 prefixEnd_1957591 223374468425723477757713 := by
  unfold tailWord_1957591
  simp only [CollatzResearch.WordTrace]
  refine ⟨71399209450989611770544627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47599472967326407847029751 71399209450989611770544627)
  ·
    refine ⟨107098814176484417655816941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71399209450989611770544627 107098814176484417655816941)
    ·
      refine ⟨40162055316181656620931353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107098814176484417655816941 40162055316181656620931353)
      ·
        refine ⟨30121541487136242465698515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40162055316181656620931353 30121541487136242465698515)
        ·
          refine ⟨45182312230704363698547773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30121541487136242465698515 45182312230704363698547773)
          ·
            refine ⟨16943367086514136386955415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45182312230704363698547773 16943367086514136386955415)
            ·
              refine ⟨25415050629771204580433123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16943367086514136386955415 25415050629771204580433123)
              ·
                refine ⟨38122575944656806870649685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25415050629771204580433123 38122575944656806870649685)
                ·
                  refine ⟨223374468425723477757713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38122575944656806870649685 223374468425723477757713)
                  ·
                    rfl

theorem cell22_1957591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 9].length) (baseStart_1957591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957591 prefixEnd_1957591 := by exact prefixLift 1957591
  have htrace : WordTrace (prefixWord ++ tailWord_1957591) baseStart_1957591 baseEnd_1957591 := by
    simpa [prefixWord, tailWord_1957591, baseEnd_1957591] using wordTrace_append hprefix tailTrace_1957591
  have hstable : (prefixWord ++ tailWord_1957591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957591).length < 2 ^ (prefixWord ++ tailWord_1957591).sum := by decide
  have hdescent : baseEnd_1957591 < baseStart_1957591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957597 : List Nat := [1, 4, 3, 3, 2, 1, 8]
def baseStart_1957597 : Nat := 118140960795 + 1957597 * 2 ^ 59
def prefixEnd_1957597 : Nat := 4983230072969 + 3 ^ 40 * 1957597 * 2
def baseEnd_1957597 : Nat := 24819461451844015467523

theorem tailTrace_1957597 : CollatzResearch.WordTrace tailWord_1957597 prefixEnd_1957597 24819461451844015467523 := by
  unfold tailWord_1957597
  simp only [CollatzResearch.WordTrace]
  refine ⟨71399428288967874795263045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47599618859311916530175363 71399428288967874795263045)
  ·
    refine ⟨13387392804181476524111821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71399428288967874795263045 13387392804181476524111821)
    ·
      refine ⟨5020272301568053696541933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13387392804181476524111821 5020272301568053696541933)
      ·
        refine ⟨1882602113088020136203225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5020272301568053696541933 1882602113088020136203225)
        ·
          refine ⟨1411951584816015102152419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1882602113088020136203225 1411951584816015102152419)
          ·
            refine ⟨2117927377224022653228629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411951584816015102152419 2117927377224022653228629)
            ·
              refine ⟨24819461451844015467523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2117927377224022653228629 24819461451844015467523)
              ·
                rfl

theorem cell22_1957597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 8].length) (baseStart_1957597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957597 prefixEnd_1957597 := by exact prefixLift 1957597
  have htrace : WordTrace (prefixWord ++ tailWord_1957597) baseStart_1957597 baseEnd_1957597 := by
    simpa [prefixWord, tailWord_1957597, baseEnd_1957597] using wordTrace_append hprefix tailTrace_1957597
  have hstable : (prefixWord ++ tailWord_1957597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957597).length < 2 ^ (prefixWord ++ tailWord_1957597).sum := by decide
  have hdescent : baseEnd_1957597 < baseStart_1957597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957608 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 7]
def baseStart_1957608 : Nat := 118140960795 + 1957608 * 2 ^ 59
def prefixEnd_1957608 : Nat := 4983230072969 + 3 ^ 40 * 1957608 * 2
def baseEnd_1957608 : Nat := 223376408241529351866029

theorem tailTrace_1957608 : CollatzResearch.WordTrace tailWord_1957608 prefixEnd_1957608 223376408241529351866029 := by
  unfold tailWord_1957608
  simp only [CollatzResearch.WordTrace]
  refine ⟨35699914745964011836956739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47599886327952015782608985 35699914745964011836956739)
  ·
    refine ⟨53549872118946017755435109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35699914745964011836956739 53549872118946017755435109)
    ·
      refine ⟨10040601022302378329144083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53549872118946017755435109 10040601022302378329144083)
      ·
        refine ⟨15060901533453567493716125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10040601022302378329144083 15060901533453567493716125)
        ·
          refine ⟨5647838075045087810143547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15060901533453567493716125 5647838075045087810143547)
          ·
            refine ⟨8471757112567631715215321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647838075045087810143547 8471757112567631715215321)
            ·
              refine ⟨6353817834425723786411491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8471757112567631715215321 6353817834425723786411491)
              ·
                refine ⟨9530726751638585679617237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6353817834425723786411491 9530726751638585679617237)
                ·
                  refine ⟨223376408241529351866029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9530726751638585679617237 223376408241529351866029)
                  ·
                    rfl

theorem cell22_1957608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_1957608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957608 prefixEnd_1957608 := by exact prefixLift 1957608
  have htrace : WordTrace (prefixWord ++ tailWord_1957608) baseStart_1957608 baseEnd_1957608 := by
    simpa [prefixWord, tailWord_1957608, baseEnd_1957608] using wordTrace_append hprefix tailTrace_1957608
  have hstable : (prefixWord ++ tailWord_1957608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957608).length < 2 ^ (prefixWord ++ tailWord_1957608).sum := by decide
  have hdescent : baseEnd_1957608 < baseStart_1957608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957719 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 2, 3]
def baseStart_1957719 : Nat := 118140960795 + 1957719 * 2 ^ 59
def prefixEnd_1957719 : Nat := 4983230072969 + 3 ^ 40 * 1957719 * 2
def baseEnd_1957719 : Nat := 670167222293020766072747

theorem tailTrace_1957719 : CollatzResearch.WordTrace tailWord_1957719 prefixEnd_1957719 670167222293020766072747 := by
  unfold tailWord_1957719
  simp only [CollatzResearch.WordTrace]
  refine ⟨71403877994525889631204211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47602585329683926420802807 71403877994525889631204211)
  ·
    refine ⟨107105816991788834446806317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71403877994525889631204211 107105816991788834446806317)
    ·
      refine ⟨40164681371920812917552369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107105816991788834446806317 40164681371920812917552369)
      ·
        refine ⟨30123511028940609688164277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40164681371920812917552369 30123511028940609688164277)
        ·
          refine ⟨2824079158963182158265401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30123511028940609688164277 2824079158963182158265401)
          ·
            refine ⟨2118059369222386618699051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2824079158963182158265401 2118059369222386618699051)
            ·
              refine ⟨3177089053833579928048577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118059369222386618699051 3177089053833579928048577)
              ·
                refine ⟨2382816790375184946036433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3177089053833579928048577 2382816790375184946036433)
                ·
                  refine ⟨1787112592781388709527325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2382816790375184946036433 1787112592781388709527325)
                  ·
                    refine ⟨670167222293020766072747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1787112592781388709527325 670167222293020766072747)
                    ·
                      rfl

theorem cell22_1957719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_1957719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957719 prefixEnd_1957719 := by exact prefixLift 1957719
  have htrace : WordTrace (prefixWord ++ tailWord_1957719) baseStart_1957719 baseEnd_1957719 := by
    simpa [prefixWord, tailWord_1957719, baseEnd_1957719] using wordTrace_append hprefix tailTrace_1957719
  have hstable : (prefixWord ++ tailWord_1957719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957719).length < 2 ^ (prefixWord ++ tailWord_1957719).sum := by decide
  have hdescent : baseEnd_1957719 < baseStart_1957719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957764 : List Nat := [2, 3, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_1957764 : Nat := 118140960795 + 1957764 * 2 ^ 59
def prefixEnd_1957764 : Nat := 4983230072969 + 3 ^ 40 * 1957764 * 2
def baseEnd_1957764 : Nat := 670182626712655648697609

theorem tailTrace_1957764 : CollatzResearch.WordTrace tailWord_1957764 prefixEnd_1957764 670182626712655648697609 := by
  unfold tailWord_1957764
  simp only [CollatzResearch.WordTrace]
  refine ⟨35702759639681431158296173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47603679519575241544394897 35702759639681431158296173)
  ·
    refine ⟨13388534864880536684361065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35702759639681431158296173 13388534864880536684361065)
    ·
      refine ⟨10041401148660402513270799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13388534864880536684361065 10041401148660402513270799)
      ·
        refine ⟨15062101722990603769906199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10041401148660402513270799 15062101722990603769906199)
        ·
          refine ⟨22593152584485905654859299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15062101722990603769906199 22593152584485905654859299)
          ·
            refine ⟨33889728876728858482288949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22593152584485905654859299 33889728876728858482288949)
            ·
              refine ⟨3177162082193330482714589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33889728876728858482288949 3177162082193330482714589)
              ·
                refine ⟨1191435780822498931017971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3177162082193330482714589 1191435780822498931017971)
                ·
                  refine ⟨1787153671233748396526957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191435780822498931017971 1787153671233748396526957)
                  ·
                    refine ⟨670182626712655648697609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1787153671233748396526957 670182626712655648697609)
                    ·
                      rfl

theorem cell22_1957764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_1957764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957764 prefixEnd_1957764 := by exact prefixLift 1957764
  have htrace : WordTrace (prefixWord ++ tailWord_1957764) baseStart_1957764 baseEnd_1957764 := by
    simpa [prefixWord, tailWord_1957764, baseEnd_1957764] using wordTrace_append hprefix tailTrace_1957764
  have hstable : (prefixWord ++ tailWord_1957764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957764).length < 2 ^ (prefixWord ++ tailWord_1957764).sum := by decide
  have hdescent : baseEnd_1957764 < baseStart_1957764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957835 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 2, 4]
def baseStart_1957835 : Nat := 118140960795 + 1957835 * 2 ^ 59
def prefixEnd_1957835 : Nat := 4983230072969 + 3 ^ 40 * 1957835 * 2
def baseEnd_1957835 : Nat := 670206931463635130172391

theorem tailTrace_1957835 : CollatzResearch.WordTrace tailWord_1957835 prefixEnd_1957835 670206931463635130172391 := by
  unfold tailWord_1957835
  simp only [CollatzResearch.WordTrace]
  refine ⟨71408108862105641442426959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47605405908070427628284639 71408108862105641442426959)
  ·
    refine ⟨107112163293158462163640439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71408108862105641442426959 107112163293158462163640439)
    ·
      refine ⟨160668244939737693245460659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107112163293158462163640439 160668244939737693245460659)
      ·
        refine ⟨241002367409606539868190989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160668244939737693245460659 241002367409606539868190989)
        ·
          refine ⟨90375887778602452450571621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241002367409606539868190989 90375887778602452450571621)
          ·
            refine ⟨16945478958487959834482179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90375887778602452450571621 16945478958487959834482179)
            ·
              refine ⟨25418218437731939751723269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16945478958487959834482179 25418218437731939751723269)
              ·
                refine ⟨4765915957074738703448113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25418218437731939751723269 4765915957074738703448113)
                ·
                  refine ⟨3574436967806054027586085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4765915957074738703448113 3574436967806054027586085)
                  ·
                    refine ⟨670206931463635130172391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3574436967806054027586085 670206931463635130172391)
                    ·
                      rfl

theorem cell22_1957835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 4].length) (baseStart_1957835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957835 prefixEnd_1957835 := by exact prefixLift 1957835
  have htrace : WordTrace (prefixWord ++ tailWord_1957835) baseStart_1957835 baseEnd_1957835 := by
    simpa [prefixWord, tailWord_1957835, baseEnd_1957835] using wordTrace_append hprefix tailTrace_1957835
  have hstable : (prefixWord ++ tailWord_1957835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957835).length < 2 ^ (prefixWord ++ tailWord_1957835).sum := by decide
  have hdescent : baseEnd_1957835 < baseStart_1957835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957869 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_1957869 : Nat := 118140960795 + 1957869 * 2 ^ 59
def prefixEnd_1957869 : Nat := 4983230072969 + 3 ^ 40 * 1957869 * 2
def baseEnd_1957869 : Nat := 670218570358470374822287

theorem tailTrace_1957869 : CollatzResearch.WordTrace tailWord_1957869 prefixEnd_1957869 670218570358470374822287 := by
  unfold tailWord_1957869
  simp only [CollatzResearch.WordTrace]
  refine ⟨71409348943982465249164661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47606232629321643499443107 71409348943982465249164661)
  ·
    refine ⟨6694626463498356117109187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71409348943982465249164661 6694626463498356117109187)
    ·
      refine ⟨10041939695247534175663781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6694626463498356117109187 10041939695247534175663781)
      ·
        refine ⟨1882863692858912657936959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10041939695247534175663781 1882863692858912657936959)
        ·
          refine ⟨2824295539288368986905439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882863692858912657936959 2824295539288368986905439)
          ·
            refine ⟨4236443308932553480358159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824295539288368986905439 4236443308932553480358159)
            ·
              refine ⟨6354664963398830220537239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236443308932553480358159 6354664963398830220537239)
              ·
                refine ⟨9531997445098245330805859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6354664963398830220537239 9531997445098245330805859)
                ·
                  refine ⟨14297996167647367996208789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9531997445098245330805859 14297996167647367996208789)
                  ·
                    refine ⟨670218570358470374822287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14297996167647367996208789 670218570358470374822287)
                    ·
                      rfl

theorem cell22_1957869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_1957869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957869 prefixEnd_1957869 := by exact prefixLift 1957869
  have htrace : WordTrace (prefixWord ++ tailWord_1957869) baseStart_1957869 baseEnd_1957869 := by
    simpa [prefixWord, tailWord_1957869, baseEnd_1957869] using wordTrace_append hprefix tailTrace_1957869
  have hstable : (prefixWord ++ tailWord_1957869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957869).length < 2 ^ (prefixWord ++ tailWord_1957869).sum := by decide
  have hdescent : baseEnd_1957869 < baseStart_1957869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957899 : List Nat := [1, 1, 1, 1, 6, 1, 1, 6, 1, 3]
def baseStart_1957899 : Nat := 118140960795 + 1957899 * 2 ^ 59
def prefixEnd_1957899 : Nat := 4983230072969 + 3 ^ 40 * 1957899 * 2
def baseEnd_1957899 : Nat := 670228839971560296572195

theorem tailTrace_1957899 : CollatzResearch.WordTrace tailWord_1957899 prefixEnd_1957899 670228839971560296572195 := by
  unfold tailWord_1957899
  simp only [CollatzResearch.WordTrace]
  refine ⟨71410443133873780372756751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47606962089249186915171167 71410443133873780372756751)
  ·
    refine ⟨107115664700810670559135127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71410443133873780372756751 107115664700810670559135127)
    ·
      refine ⟨160673497051216005838702691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107115664700810670559135127 160673497051216005838702691)
      ·
        refine ⟨241010245576824008758054037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160673497051216005838702691 241010245576824008758054037)
        ·
          refine ⟨11297355261413625410533783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241010245576824008758054037 11297355261413625410533783)
          ·
            refine ⟨16946032892120438115800675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11297355261413625410533783 16946032892120438115800675)
            ·
              refine ⟨25419049338180657173701013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16946032892120438115800675 25419049338180657173701013)
              ·
                refine ⟨1191517937727218305017235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25419049338180657173701013 1191517937727218305017235)
                ·
                  refine ⟨1787276906590827457525853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191517937727218305017235 1787276906590827457525853)
                  ·
                    refine ⟨670228839971560296572195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1787276906590827457525853 670228839971560296572195)
                    ·
                      rfl

theorem cell22_1957899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 1, 3].length) (baseStart_1957899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957899 prefixEnd_1957899 := by exact prefixLift 1957899
  have htrace : WordTrace (prefixWord ++ tailWord_1957899) baseStart_1957899 baseEnd_1957899 := by
    simpa [prefixWord, tailWord_1957899, baseEnd_1957899] using wordTrace_append hprefix tailTrace_1957899
  have hstable : (prefixWord ++ tailWord_1957899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957899).length < 2 ^ (prefixWord ++ tailWord_1957899).sum := by decide
  have hdescent : baseEnd_1957899 < baseStart_1957899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957950 : List Nat := [4, 2, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_1957950 : Nat := 118140960795 + 1957950 * 2 ^ 59
def prefixEnd_1957950 : Nat := 4983230072969 + 3 ^ 40 * 1957950 * 2
def baseEnd_1957950 : Nat := 670246298313813163547039

theorem tailTrace_1957950 : CollatzResearch.WordTrace tailWord_1957950 prefixEnd_1957950 670246298313813163547039 := by
  unfold tailWord_1957950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8926537907086127010357913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47608202171126010721908869 8926537907086127010357913)
  ·
    refine ⟨6694903430314595257768435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8926537907086127010357913 6694903430314595257768435)
    ·
      refine ⟨10042355145471892886652653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6694903430314595257768435 10042355145471892886652653)
      ·
        refine ⟨3765883179551959832494745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10042355145471892886652653 3765883179551959832494745)
        ·
          refine ⟨2824412384663969874371059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3765883179551959832494745 2824412384663969874371059)
          ·
            refine ⟨4236618576995954811556589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824412384663969874371059 4236618576995954811556589)
            ·
              refine ⟨1588731966373483054333721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4236618576995954811556589 1588731966373483054333721)
              ·
                refine ⟨1191548974780112290750291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1588731966373483054333721 1191548974780112290750291)
                ·
                  refine ⟨1787323462170168436125437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191548974780112290750291 1787323462170168436125437)
                  ·
                    refine ⟨670246298313813163547039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1787323462170168436125437 670246298313813163547039)
                    ·
                      rfl

theorem cell22_1957950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_1957950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957950 prefixEnd_1957950 := by exact prefixLift 1957950
  have htrace : WordTrace (prefixWord ++ tailWord_1957950) baseStart_1957950 baseEnd_1957950 := by
    simpa [prefixWord, tailWord_1957950, baseEnd_1957950] using wordTrace_append hprefix tailTrace_1957950
  have hstable : (prefixWord ++ tailWord_1957950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957950).length < 2 ^ (prefixWord ++ tailWord_1957950).sum := by decide
  have hdescent : baseEnd_1957950 < baseStart_1957950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957955 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 5, 5]
def baseStart_1957955 : Nat := 118140960795 + 1957955 * 2 ^ 59
def prefixEnd_1957955 : Nat := 4983230072969 + 3 ^ 40 * 1957955 * 2
def baseEnd_1957955 : Nat := 670248009915994817172023

theorem tailTrace_1957955 : CollatzResearch.WordTrace tailWord_1957955 prefixEnd_1957955 670248009915994817172023 := by
  unfold tailWord_1957955
  simp only [CollatzResearch.WordTrace]
  refine ⟨71412485621670901936795319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47608323747780601291196879 71412485621670901936795319)
  ·
    refine ⟨107118728432506352905192979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71412485621670901936795319 107118728432506352905192979)
    ·
      refine ⟨160678092648759529357789469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107118728432506352905192979 160678092648759529357789469)
      ·
        refine ⟨60254284743284823509171051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160678092648759529357789469 60254284743284823509171051)
        ·
          refine ⟨90381427114927235263756577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60254284743284823509171051 90381427114927235263756577)
          ·
            refine ⟨67786070336195426447817433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90381427114927235263756577 67786070336195426447817433)
            ·
              refine ⟨50839552752146569835863075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67786070336195426447817433 50839552752146569835863075)
              ·
                refine ⟨76259329128219854753794613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50839552752146569835863075 76259329128219854753794613)
                ·
                  refine ⟨7149312105770611383168245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76259329128219854753794613 7149312105770611383168245)
                  ·
                    refine ⟨670248009915994817172023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7149312105770611383168245 670248009915994817172023)
                    ·
                      rfl

theorem cell22_1957955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_1957955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957955 prefixEnd_1957955 := by exact prefixLift 1957955
  have htrace : WordTrace (prefixWord ++ tailWord_1957955) baseStart_1957955 baseEnd_1957955 := by
    simpa [prefixWord, tailWord_1957955, baseEnd_1957955] using wordTrace_append hprefix tailTrace_1957955
  have hstable : (prefixWord ++ tailWord_1957955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957955).length < 2 ^ (prefixWord ++ tailWord_1957955).sum := by decide
  have hdescent : baseEnd_1957955 < baseStart_1957955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957972 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1957972 : Nat := 118140960795 + 1957972 * 2 ^ 59
def prefixEnd_1957972 : Nat := 4983230072969 + 3 ^ 40 * 1957972 * 2
def baseEnd_1957972 : Nat := 670253829363412439496971

theorem tailTrace_1957972 : CollatzResearch.WordTrace tailWord_1957972 prefixEnd_1957972 670253829363412439496971 := by
  unfold tailWord_1957972
  simp only [CollatzResearch.WordTrace]
  refine ⟨35706552831304656920082085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47608737108406209226776113 35706552831304656920082085)
  ·
    refine ⟨6694978655869623172515391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35706552831304656920082085 6694978655869623172515391)
    ·
      refine ⟨10042467983804434758773087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6694978655869623172515391 10042467983804434758773087)
      ·
        refine ⟨15063701975706652138159631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10042467983804434758773087 15063701975706652138159631)
        ·
          refine ⟨22595552963559978207239447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15063701975706652138159631 22595552963559978207239447)
          ·
            refine ⟨33893329445339967310859171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22595552963559978207239447 33893329445339967310859171)
            ·
              refine ⟨50839994168009950966288757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33893329445339967310859171 50839994168009950966288757)
              ·
                refine ⟨4766249453250932903089571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50839994168009950966288757 4766249453250932903089571)
                ·
                  refine ⟨7149374179876399354634357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766249453250932903089571 7149374179876399354634357)
                  ·
                    refine ⟨670253829363412439496971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7149374179876399354634357 670253829363412439496971)
                    ·
                      rfl

theorem cell22_1957972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1957972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957972 prefixEnd_1957972 := by exact prefixLift 1957972
  have htrace : WordTrace (prefixWord ++ tailWord_1957972) baseStart_1957972 baseEnd_1957972 := by
    simpa [prefixWord, tailWord_1957972, baseEnd_1957972] using wordTrace_append hprefix tailTrace_1957972
  have hstable : (prefixWord ++ tailWord_1957972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957972).length < 2 ^ (prefixWord ++ tailWord_1957972).sum := by decide
  have hdescent : baseEnd_1957972 < baseStart_1957972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957987 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 2, 4]
def baseStart_1957987 : Nat := 118140960795 + 1957987 * 2 ^ 59
def prefixEnd_1957987 : Nat := 4983230072969 + 3 ^ 40 * 1957987 * 2
def baseEnd_1957987 : Nat := 670258964169957400371925

theorem tailTrace_1957987 : CollatzResearch.WordTrace tailWord_1957987 prefixEnd_1957987 670258964169957400371925 := by
  unfold tailWord_1957987
  simp only [CollatzResearch.WordTrace]
  refine ⟨71413652757554971401960215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47609101838369980934640143 71413652757554971401960215)
  ·
    refine ⟨107120479136332457102940323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71413652757554971401960215 107120479136332457102940323)
    ·
      refine ⟨160680718704498685654410485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107120479136332457102940323 160680718704498685654410485)
      ·
        refine ⟨15063817378546751780100983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160680718704498685654410485 15063817378546751780100983)
        ·
          refine ⟨22595726067820127670151475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15063817378546751780100983 22595726067820127670151475)
          ·
            refine ⟨33893589101730191505227213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22595726067820127670151475 33893589101730191505227213)
            ·
              refine ⟨12710095913148821814460205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33893589101730191505227213 12710095913148821814460205)
              ·
                refine ⟨4766285967430808180422577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12710095913148821814460205 4766285967430808180422577)
                ·
                  refine ⟨3574714475573106135316933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4766285967430808180422577 3574714475573106135316933)
                  ·
                    refine ⟨670258964169957400371925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3574714475573106135316933 670258964169957400371925)
                    ·
                      rfl

theorem cell22_1957987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 4].length) (baseStart_1957987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1957987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1957987 prefixEnd_1957987 := by exact prefixLift 1957987
  have htrace : WordTrace (prefixWord ++ tailWord_1957987) baseStart_1957987 baseEnd_1957987 := by
    simpa [prefixWord, tailWord_1957987, baseEnd_1957987] using wordTrace_append hprefix tailTrace_1957987
  have hstable : (prefixWord ++ tailWord_1957987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957987).length < 2 ^ (prefixWord ++ tailWord_1957987).sum := by decide
  have hdescent : baseEnd_1957987 < baseStart_1957987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958006 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1958006 : Nat := 118140960795 + 1958006 * 2 ^ 59
def prefixEnd_1958006 : Nat := 4983230072969 + 3 ^ 40 * 1958006 * 2
def baseEnd_1958006 : Nat := 670265468258247684146867

theorem tailTrace_1958006 : CollatzResearch.WordTrace tailWord_1958006 prefixEnd_1958006 670265468258247684146867 := by
  unfold tailWord_1958006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4463396609030383602931367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47609563829657425097934581 4463396609030383602931367)
  ·
    refine ⟨6695094913545575404397051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4463396609030383602931367 6695094913545575404397051)
    ·
      refine ⟨10042642370318363106595577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6695094913545575404397051 10042642370318363106595577)
      ·
        refine ⟨7531981777738772329946683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10042642370318363106595577 7531981777738772329946683)
        ·
          refine ⟨11297972666608158494920025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7531981777738772329946683 11297972666608158494920025)
          ·
            refine ⟨8473479499956118871190019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11297972666608158494920025 8473479499956118871190019)
            ·
              refine ⟨12710219249934178306785029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8473479499956118871190019 12710219249934178306785029)
              ·
                refine ⟨2383166109362658432522193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12710219249934178306785029 2383166109362658432522193)
                ·
                  refine ⟨1787374582021993824391645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2383166109362658432522193 1787374582021993824391645)
                  ·
                    refine ⟨670265468258247684146867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1787374582021993824391645 670265468258247684146867)
                    ·
                      rfl

theorem cell22_1958006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1958006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958006 prefixEnd_1958006 := by exact prefixLift 1958006
  have htrace : WordTrace (prefixWord ++ tailWord_1958006) baseStart_1958006 baseEnd_1958006 := by
    simpa [prefixWord, tailWord_1958006, baseEnd_1958006] using wordTrace_append hprefix tailTrace_1958006
  have hstable : (prefixWord ++ tailWord_1958006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958006).length < 2 ^ (prefixWord ++ tailWord_1958006).sum := by decide
  have hdescent : baseEnd_1958006 < baseStart_1958006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958102 : List Nat := [5, 2, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1958102 : Nat := 118140960795 + 1958102 * 2 ^ 59
def prefixEnd_1958102 : Nat := 4983230072969 + 3 ^ 40 * 1958102 * 2
def baseEnd_1958102 : Nat := 670298331020135433746573

theorem tailTrace_1958102 : CollatzResearch.WordTrace tailWord_1958102 prefixEnd_1958102 670298331020135433746573 := by
  unfold tailWord_1958102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4463615447008646627649785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47611898101425564028264373 4463615447008646627649785)
  ·
    refine ⟨3347711585256484970737339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4463615447008646627649785 3347711585256484970737339)
    ·
      refine ⟨5021567377884727456106009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3347711585256484970737339 5021567377884727456106009)
      ·
        refine ⟨3766175533413545592079507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5021567377884727456106009 3766175533413545592079507)
        ·
          refine ⟨5649263300120318388119261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766175533413545592079507 5649263300120318388119261)
          ·
            refine ⟨2118473737545119395544723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5649263300120318388119261 2118473737545119395544723)
            ·
              refine ⟨3177710606317679093317085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118473737545119395544723 3177710606317679093317085)
              ·
                refine ⟨1191641477369129659993907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3177710606317679093317085 1191641477369129659993907)
                ·
                  refine ⟨1787462216053694489990861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191641477369129659993907 1787462216053694489990861)
                  ·
                    refine ⟨670298331020135433746573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1787462216053694489990861 670298331020135433746573)
                    ·
                      rfl

theorem cell22_1958102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1958102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958102 prefixEnd_1958102 := by exact prefixLift 1958102
  have htrace : WordTrace (prefixWord ++ tailWord_1958102) baseStart_1958102 baseEnd_1958102 := by
    simpa [prefixWord, tailWord_1958102, baseEnd_1958102] using wordTrace_append hprefix tailTrace_1958102
  have hstable : (prefixWord ++ tailWord_1958102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958102).length < 2 ^ (prefixWord ++ tailWord_1958102).sum := by decide
  have hdescent : baseEnd_1958102 < baseStart_1958102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958124 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 4, 3]
def baseStart_1958124 : Nat := 118140960795 + 1958124 * 2 ^ 59
def prefixEnd_1958124 : Nat := 4983230072969 + 3 ^ 40 * 1958124 * 2
def baseEnd_1958124 : Nat := 670305862069734709696505

theorem tailTrace_1958124 : CollatzResearch.WordTrace tailWord_1958124 prefixEnd_1958124 670305862069734709696505 := by
  unfold tailWord_1958124
  simp only [CollatzResearch.WordTrace]
  refine ⟨35709324779029321899848713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47612433038705762533131617 35709324779029321899848713)
  ·
    refine ⟨26781993584271991424886535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35709324779029321899848713 26781993584271991424886535)
    ·
      refine ⟨40172990376407987137329803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26781993584271991424886535 40172990376407987137329803)
      ·
        refine ⟨60259485564611980705994705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40172990376407987137329803 60259485564611980705994705)
        ·
          refine ⟨45194614173458985529496029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60259485564611980705994705 45194614173458985529496029)
          ·
            refine ⟨16947980315047119573561011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45194614173458985529496029 16947980315047119573561011)
            ·
              refine ⟨25421970472570679360341517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16947980315047119573561011 25421970472570679360341517)
              ·
                refine ⟨9533238927214004760128069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25421970472570679360341517 9533238927214004760128069)
                ·
                  refine ⟨1787482298852625892524013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9533238927214004760128069 1787482298852625892524013)
                  ·
                    refine ⟨670305862069734709696505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1787482298852625892524013 670305862069734709696505)
                    ·
                      rfl

theorem cell22_1958124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_1958124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958124 prefixEnd_1958124 := by exact prefixLift 1958124
  have htrace : WordTrace (prefixWord ++ tailWord_1958124) baseStart_1958124 baseEnd_1958124 := by
    simpa [prefixWord, tailWord_1958124, baseEnd_1958124] using wordTrace_append hprefix tailTrace_1958124
  have hstable : (prefixWord ++ tailWord_1958124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958124).length < 2 ^ (prefixWord ++ tailWord_1958124).sum := by decide
  have hdescent : baseEnd_1958124 < baseStart_1958124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958261 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 6]
def baseStart_1958261 : Nat := 118140960795 + 1958261 * 2 ^ 59
def prefixEnd_1958261 : Nat := 4983230072969 + 3 ^ 40 * 1958261 * 2
def baseEnd_1958261 : Nat := 223450919989837339673695

theorem tailTrace_1958261 : CollatzResearch.WordTrace tailWord_1958261 prefixEnd_1958261 223450919989837339673695 := by
  unfold tailWord_1958261
  simp only [CollatzResearch.WordTrace]
  refine ⟨71423646358562316197434637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47615764239041544131623091 71423646358562316197434637)
  ·
    refine ⟨26783867384460868574037989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71423646358562316197434637 26783867384460868574037989)
    ·
      refine ⟨5021975134586412857632123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26783867384460868574037989 5021975134586412857632123)
      ·
        refine ⟨7532962701879619286448185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5021975134586412857632123 7532962701879619286448185)
        ·
          refine ⟨5649722026409714464836139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7532962701879619286448185 5649722026409714464836139)
          ·
            refine ⟨8474583039614571697254209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5649722026409714464836139 8474583039614571697254209)
            ·
              refine ⟨6355937279710928772940657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8474583039614571697254209 6355937279710928772940657)
              ·
                refine ⟨4766952959783196579705493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6355937279710928772940657 4766952959783196579705493)
                ·
                  refine ⟨223450919989837339673695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4766952959783196579705493 223450919989837339673695)
                  ·
                    rfl

theorem cell22_1958261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_1958261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958261 prefixEnd_1958261 := by exact prefixLift 1958261
  have htrace : WordTrace (prefixWord ++ tailWord_1958261) baseStart_1958261 baseEnd_1958261 := by
    simpa [prefixWord, tailWord_1958261, baseEnd_1958261] using wordTrace_append hprefix tailTrace_1958261
  have hstable : (prefixWord ++ tailWord_1958261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958261).length < 2 ^ (prefixWord ++ tailWord_1958261).sum := by decide
  have hdescent : baseEnd_1958261 < baseStart_1958261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958276 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1958276 : Nat := 118140960795 + 1958276 * 2 ^ 59
def prefixEnd_1958276 : Nat := 4983230072969 + 3 ^ 40 * 1958276 * 2
def baseEnd_1958276 : Nat := 670357894776056979896039

theorem tailTrace_1958276 : CollatzResearch.WordTrace tailWord_1958276 prefixEnd_1958276 670357894776056979896039 := by
  unfold tailWord_1958276
  simp only [CollatzResearch.WordTrace]
  refine ⟨35712096726753986879615341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47616128969005315839487121 35712096726753986879615341)
  ·
    refine ⟨13392036272532745079855753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35712096726753986879615341 13392036272532745079855753)
    ·
      refine ⟨10044027204399558809891815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13392036272532745079855753 10044027204399558809891815)
      ·
        refine ⟨15066040806599338214837723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10044027204399558809891815 15066040806599338214837723)
        ·
          refine ⟨22599061209899007322256585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15066040806599338214837723 22599061209899007322256585)
          ·
            refine ⟨16949295907424255491692439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22599061209899007322256585 16949295907424255491692439)
            ·
              refine ⟨25423943861136383237538659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16949295907424255491692439 25423943861136383237538659)
              ·
                refine ⟨38135915791704574856307989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25423943861136383237538659 38135915791704574856307989)
                ·
                  refine ⟨1787621052736151946389437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38135915791704574856307989 1787621052736151946389437)
                  ·
                    refine ⟨670357894776056979896039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1787621052736151946389437 670357894776056979896039)
                    ·
                      rfl

theorem cell22_1958276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1958276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958276 prefixEnd_1958276 := by exact prefixLift 1958276
  have htrace : WordTrace (prefixWord ++ tailWord_1958276) baseStart_1958276 baseEnd_1958276 := by
    simpa [prefixWord, tailWord_1958276, baseEnd_1958276] using wordTrace_append hprefix tailTrace_1958276
  have hstable : (prefixWord ++ tailWord_1958276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958276).length < 2 ^ (prefixWord ++ tailWord_1958276).sum := by decide
  have hdescent : baseEnd_1958276 < baseStart_1958276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958306 : List Nat := [3, 3, 1, 2, 1, 1, 4, 7]
def baseStart_1958306 : Nat := 118140960795 + 1958306 * 2 ^ 59
def prefixEnd_1958306 : Nat := 4983230072969 + 3 ^ 40 * 1958306 * 2
def baseEnd_1958306 : Nat := 74485351598794100182883

theorem tailTrace_1958306 : CollatzResearch.WordTrace tailWord_1958306 prefixEnd_1958306 74485351598794100182883 := by
  unfold tailWord_1958306
  simp only [CollatzResearch.WordTrace]
  refine ⟨17856321910849822220705693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47616858428932859255215181 17856321910849822220705693)
  ·
    refine ⟨6696120716568683332764635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17856321910849822220705693 6696120716568683332764635)
    ·
      refine ⟨10044181074853024999146953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6696120716568683332764635 10044181074853024999146953)
      ·
        refine ⟨7533135806139768749360215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10044181074853024999146953 7533135806139768749360215)
        ·
          refine ⟨11299703709209653124040323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7533135806139768749360215 11299703709209653124040323)
          ·
            refine ⟨16949555563814479686060485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11299703709209653124040323 16949555563814479686060485)
            ·
              refine ⟨3178041668215214941136341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16949555563814479686060485 3178041668215214941136341)
              ·
                refine ⟨74485351598794100182883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3178041668215214941136341 74485351598794100182883)
                ·
                  rfl

theorem cell22_1958306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_1958306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958306 prefixEnd_1958306 := by exact prefixLift 1958306
  have htrace : WordTrace (prefixWord ++ tailWord_1958306) baseStart_1958306 baseEnd_1958306 := by
    simpa [prefixWord, tailWord_1958306, baseEnd_1958306] using wordTrace_append hprefix tailTrace_1958306
  have hstable : (prefixWord ++ tailWord_1958306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958306).length < 2 ^ (prefixWord ++ tailWord_1958306).sum := by decide
  have hdescent : baseEnd_1958306 < baseStart_1958306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958314 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1958314 : Nat := 118140960795 + 1958314 * 2 ^ 59
def prefixEnd_1958314 : Nat := 4983230072969 + 3 ^ 40 * 1958314 * 2
def baseEnd_1958314 : Nat := 670370902952637547445923

theorem tailTrace_1958314 : CollatzResearch.WordTrace tailWord_1958314 prefixEnd_1958314 670370902952637547445923 := by
  unfold tailWord_1958314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17856394856842576562278499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47617052951580204166075997 17856394856842576562278499)
  ·
    refine ⟨26784592285263864843417749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17856394856842576562278499 26784592285263864843417749)
    ·
      refine ⟨1255527763371743664535207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26784592285263864843417749 1255527763371743664535207)
      ·
        refine ⟨1883291645057615496802811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255527763371743664535207 1883291645057615496802811)
        ·
          refine ⟨2824937467586423245204217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883291645057615496802811 2824937467586423245204217)
          ·
            refine ⟨2118703100689817433903163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2824937467586423245204217 2118703100689817433903163)
            ·
              refine ⟨3178054651034726150854745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118703100689817433903163 3178054651034726150854745)
              ·
                refine ⟨2383540988276044613141059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178054651034726150854745 2383540988276044613141059)
                ·
                  refine ⟨3575311482414066919711589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383540988276044613141059 3575311482414066919711589)
                  ·
                    refine ⟨670370902952637547445923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3575311482414066919711589 670370902952637547445923)
                    ·
                      rfl

theorem cell22_1958314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1958314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958314 prefixEnd_1958314 := by exact prefixLift 1958314
  have htrace : WordTrace (prefixWord ++ tailWord_1958314) baseStart_1958314 baseEnd_1958314 := by
    simpa [prefixWord, tailWord_1958314, baseEnd_1958314] using wordTrace_append hprefix tailTrace_1958314
  have hstable : (prefixWord ++ tailWord_1958314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958314).length < 2 ^ (prefixWord ++ tailWord_1958314).sum := by decide
  have hdescent : baseEnd_1958314 < baseStart_1958314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958389 : List Nat := [1, 3, 5, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1958389 : Nat := 118140960795 + 1958389 * 2 ^ 59
def prefixEnd_1958389 : Nat := 4983230072969 + 3 ^ 40 * 1958389 * 2
def baseEnd_1958389 : Nat := 670396576985362351820693

theorem tailTrace_1958389 : CollatzResearch.WordTrace tailWord_1958389 prefixEnd_1958389 670396576985362351820693 := by
  unfold tailWord_1958389
  simp only [CollatzResearch.WordTrace]
  refine ⟨71428314902098594058094221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47618876601399062705396147 71428314902098594058094221)
  ·
    refine ⟨26785618088286972771785333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71428314902098594058094221 26785618088286972771785333)
    ·
      refine ⟨2511151695776903697354875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26785618088286972771785333 2511151695776903697354875)
      ·
        refine ⟨3766727543665355546032313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511151695776903697354875 3766727543665355546032313)
        ·
          refine ⟨2825045657749016659524235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3766727543665355546032313 2825045657749016659524235)
          ·
            refine ⟨4237568486623524989286353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825045657749016659524235 4237568486623524989286353)
            ·
              refine ⟨3178176364967643741964765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4237568486623524989286353 3178176364967643741964765)
              ·
                refine ⟨1191816136862866403236787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3178176364967643741964765 1191816136862866403236787)
                ·
                  refine ⟨1787724205294299604855181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191816136862866403236787 1787724205294299604855181)
                  ·
                    refine ⟨670396576985362351820693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1787724205294299604855181 670396576985362351820693)
                    ·
                      rfl

theorem cell22_1958389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1958389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958389 prefixEnd_1958389 := by exact prefixLift 1958389
  have htrace : WordTrace (prefixWord ++ tailWord_1958389) baseStart_1958389 baseEnd_1958389 := by
    simpa [prefixWord, tailWord_1958389, baseEnd_1958389] using wordTrace_append hprefix tailTrace_1958389
  have hstable : (prefixWord ++ tailWord_1958389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958389).length < 2 ^ (prefixWord ++ tailWord_1958389).sum := by decide
  have hdescent : baseEnd_1958389 < baseStart_1958389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958402 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1958402 : Nat := 118140960795 + 1958402 * 2 ^ 59
def prefixEnd_1958402 : Nat := 4983230072969 + 3 ^ 40 * 1958402 * 2
def baseEnd_1958402 : Nat := 223467009050344883748551

theorem tailTrace_1958402 : CollatzResearch.WordTrace tailWord_1958402 prefixEnd_1958402 223467009050344883748551 := by
  unfold tailWord_1958402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17857197262762874319579365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47619192700700998185544973 17857197262762874319579365)
  ·
    refine ⟨3348224486768038934921131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17857197262762874319579365 3348224486768038934921131)
    ·
      refine ⟨5022336730152058402381697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3348224486768038934921131 5022336730152058402381697)
      ·
        refine ⟨3766752547614043801786273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5022336730152058402381697 3766752547614043801786273)
        ·
          refine ⟨2825064410710532851339705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3766752547614043801786273 2825064410710532851339705)
          ·
            refine ⟨2118798308032899638504779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2825064410710532851339705 2118798308032899638504779)
            ·
              refine ⟨3178197462049349457757169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118798308032899638504779 3178197462049349457757169)
              ·
                refine ⟨2383648096537012093317877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178197462049349457757169 2383648096537012093317877)
                ·
                  refine ⟨223467009050344883748551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2383648096537012093317877 223467009050344883748551)
                  ·
                    rfl

theorem cell22_1958402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1958402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958402 prefixEnd_1958402 := by exact prefixLift 1958402
  have htrace : WordTrace (prefixWord ++ tailWord_1958402) baseStart_1958402 baseEnd_1958402 := by
    simpa [prefixWord, tailWord_1958402, baseEnd_1958402] using wordTrace_append hprefix tailTrace_1958402
  have hstable : (prefixWord ++ tailWord_1958402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958402).length < 2 ^ (prefixWord ++ tailWord_1958402).sum := by decide
  have hdescent : baseEnd_1958402 < baseStart_1958402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958406 : List Nat := [6, 2, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1958406 : Nat := 118140960795 + 1958406 * 2 ^ 59
def prefixEnd_1958406 : Nat := 4983230072969 + 3 ^ 40 * 1958406 * 2
def baseEnd_1958406 : Nat := 670402396432779974145641

theorem tailTrace_1958406 : CollatzResearch.WordTrace tailWord_1958406 prefixEnd_1958406 670402396432779974145641 := by
  unfold tailWord_1958406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232154216969906436295721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47619289962024670640975381 2232154216969906436295721)
  ·
    refine ⟨1674115662727429827221791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2232154216969906436295721 1674115662727429827221791)
    ·
      refine ⟨2511173494091144740832687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674115662727429827221791 2511173494091144740832687)
      ·
        refine ⟨3766760241136717111249031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511173494091144740832687 3766760241136717111249031)
        ·
          refine ⟨5650140361705075666873547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766760241136717111249031 5650140361705075666873547)
          ·
            refine ⟨8475210542557613500310321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650140361705075666873547 8475210542557613500310321)
            ·
              refine ⟨6356407906918210125232741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8475210542557613500310321 6356407906918210125232741)
              ·
                refine ⟨1191826482547164398481139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6356407906918210125232741 1191826482547164398481139)
                ·
                  refine ⟨1787739723820746597721709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191826482547164398481139 1787739723820746597721709)
                  ·
                    refine ⟨670402396432779974145641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1787739723820746597721709 670402396432779974145641)
                    ·
                      rfl

theorem cell22_1958406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1958406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958406 prefixEnd_1958406 := by exact prefixLift 1958406
  have htrace : WordTrace (prefixWord ++ tailWord_1958406) baseStart_1958406 baseEnd_1958406 := by
    simpa [prefixWord, tailWord_1958406, baseEnd_1958406] using wordTrace_append hprefix tailTrace_1958406
  have hstable : (prefixWord ++ tailWord_1958406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958406).length < 2 ^ (prefixWord ++ tailWord_1958406).sum := by decide
  have hdescent : baseEnd_1958406 < baseStart_1958406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958426 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_1958426 : Nat := 118140960795 + 1958426 * 2 ^ 59
def prefixEnd_1958426 : Nat := 4983230072969 + 3 ^ 40 * 1958426 * 2
def baseEnd_1958426 : Nat := 670409242841506588645579

theorem tailTrace_1958426 : CollatzResearch.WordTrace tailWord_1958426 prefixEnd_1958426 670409242841506588645579 := by
  unfold tailWord_1958426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17857416100741137344297783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47619776268643032918127421 17857416100741137344297783)
  ·
    refine ⟨26786124151111706016446675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17857416100741137344297783 26786124151111706016446675)
    ·
      refine ⟨40179186226667559024670013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26786124151111706016446675 40179186226667559024670013)
      ·
        refine ⟨15067194835000334634251255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40179186226667559024670013 15067194835000334634251255)
        ·
          refine ⟨22600792252500501951376883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15067194835000334634251255 22600792252500501951376883)
          ·
            refine ⟨33901188378750752927065325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22600792252500501951376883 33901188378750752927065325)
            ·
              refine ⟨12712945642031532347649497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33901188378750752927065325 12712945642031532347649497)
              ·
                refine ⟨9534709231523649260737123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12712945642031532347649497 9534709231523649260737123)
                ·
                  refine ⟨14302063847285473891105685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9534709231523649260737123 14302063847285473891105685)
                  ·
                    refine ⟨670409242841506588645579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14302063847285473891105685 670409242841506588645579)
                    ·
                      rfl

theorem cell22_1958426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_1958426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958426 prefixEnd_1958426 := by exact prefixLift 1958426
  have htrace : WordTrace (prefixWord ++ tailWord_1958426) baseStart_1958426 baseEnd_1958426 := by
    simpa [prefixWord, tailWord_1958426, baseEnd_1958426] using wordTrace_append hprefix tailTrace_1958426
  have hstable : (prefixWord ++ tailWord_1958426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958426).length < 2 ^ (prefixWord ++ tailWord_1958426).sum := by decide
  have hdescent : baseEnd_1958426 < baseStart_1958426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958428 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_1958428 : Nat := 118140960795 + 1958428 * 2 ^ 59
def prefixEnd_1958428 : Nat := 4983230072969 + 3 ^ 40 * 1958428 * 2
def baseEnd_1958428 : Nat := 670409927482379250095573

theorem tailTrace_1958428 : CollatzResearch.WordTrace tailWord_1958428 prefixEnd_1958428 670409927482379250095573 := by
  unfold tailWord_1958428
  simp only [CollatzResearch.WordTrace]
  refine ⟨35714868674478651859381969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47619824899304869145842625 35714868674478651859381969)
  ·
    refine ⟨26786151505858988894536477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35714868674478651859381969 26786151505858988894536477)
    ·
      refine ⟨10044806814697120835451179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26786151505858988894536477 10044806814697120835451179)
      ·
        refine ⟨15067210222045681253176769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10044806814697120835451179 15067210222045681253176769)
        ·
          refine ⟨11300407666534260939882577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15067210222045681253176769 11300407666534260939882577)
          ·
            refine ⟨8475305749900695704911933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11300407666534260939882577 8475305749900695704911933)
            ·
              refine ⟨3178239656212760889341975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8475305749900695704911933 3178239656212760889341975)
              ·
                refine ⟨4767359484319141334012963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178239656212760889341975 4767359484319141334012963)
                ·
                  refine ⟨7151039226478712001019445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767359484319141334012963 7151039226478712001019445)
                  ·
                    refine ⟨670409927482379250095573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7151039226478712001019445 670409927482379250095573)
                    ·
                      rfl

theorem cell22_1958428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_1958428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958428 prefixEnd_1958428 := by exact prefixLift 1958428
  have htrace : WordTrace (prefixWord ++ tailWord_1958428) baseStart_1958428 baseEnd_1958428 := by
    simpa [prefixWord, tailWord_1958428, baseEnd_1958428] using wordTrace_append hprefix tailTrace_1958428
  have hstable : (prefixWord ++ tailWord_1958428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958428).length < 2 ^ (prefixWord ++ tailWord_1958428).sum := by decide
  have hdescent : baseEnd_1958428 < baseStart_1958428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958533 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_1958533 : Nat := 118140960795 + 1958533 * 2 ^ 59
def prefixEnd_1958533 : Nat := 4983230072969 + 3 ^ 40 * 1958533 * 2
def baseEnd_1958533 : Nat := 670445871128193976220251

theorem tailTrace_1958533 : CollatzResearch.WordTrace tailWord_1958533 prefixEnd_1958533 670445871128193976220251 := by
  unfold tailWord_1958533
  simp only [CollatzResearch.WordTrace]
  refine ⟨71433567013576906651336253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47622378009051271100890835 71433567013576906651336253)
  ·
    refine ⟨26787587630091339994251095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71433567013576906651336253 26787587630091339994251095)
    ·
      refine ⟨40181381445137009991376643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26787587630091339994251095 40181381445137009991376643)
      ·
        refine ⟨60272072167705514987064965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40181381445137009991376643 60272072167705514987064965)
        ·
          refine ⟨11301013531444784060074681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60272072167705514987064965 11301013531444784060074681)
          ·
            refine ⟨8475760148583588045056011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11301013531444784060074681 8475760148583588045056011)
            ·
              refine ⟨12713640222875382067584017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8475760148583588045056011 12713640222875382067584017)
              ·
                refine ⟨9535230167156536550688013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12713640222875382067584017 9535230167156536550688013)
                ·
                  refine ⟨3575711312683701206508005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9535230167156536550688013 3575711312683701206508005)
                  ·
                    refine ⟨670445871128193976220251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3575711312683701206508005 670445871128193976220251)
                    ·
                      rfl

theorem cell22_1958533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_1958533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958533 prefixEnd_1958533 := by exact prefixLift 1958533
  have htrace : WordTrace (prefixWord ++ tailWord_1958533) baseStart_1958533 baseEnd_1958533 := by
    simpa [prefixWord, tailWord_1958533, baseEnd_1958533] using wordTrace_append hprefix tailTrace_1958533
  have hstable : (prefixWord ++ tailWord_1958533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958533).length < 2 ^ (prefixWord ++ tailWord_1958533).sum := by decide
  have hdescent : baseEnd_1958533 < baseStart_1958533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958578 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_1958578 : Nat := 118140960795 + 1958578 * 2 ^ 59
def prefixEnd_1958578 : Nat := 4983230072969 + 3 ^ 40 * 1958578 * 2
def baseEnd_1958578 : Nat := 670461275547828858845113

theorem tailTrace_1958578 : CollatzResearch.WordTrace tailWord_1958578 prefixEnd_1958578 670461275547828858845113 := by
  unfold tailWord_1958578
  simp only [CollatzResearch.WordTrace]
  refine ⟨17858802074603469834181097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47623472198942586224482925 17858802074603469834181097)
  ·
    refine ⟨13394101555952602375635823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17858802074603469834181097 13394101555952602375635823)
    ·
      refine ⟨20091152333928903563453735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13394101555952602375635823 20091152333928903563453735)
      ·
        refine ⟨30136728500893355345180603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20091152333928903563453735 30136728500893355345180603)
        ·
          refine ⟨45205092751340033017770905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30136728500893355345180603 45205092751340033017770905)
          ·
            refine ⟨33903819563505024763328179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45205092751340033017770905 33903819563505024763328179)
            ·
              refine ⟨50855729345257537144992269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33903819563505024763328179 50855729345257537144992269)
              ·
                refine ⟨19070898504471576429372101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50855729345257537144992269 19070898504471576429372101)
                ·
                  refine ⟨3575793469588420580507269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19070898504471576429372101 3575793469588420580507269)
                  ·
                    refine ⟨670461275547828858845113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3575793469588420580507269 670461275547828858845113)
                    ·
                      rfl

theorem cell22_1958578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_1958578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958578 prefixEnd_1958578 := by exact prefixLift 1958578
  have htrace : WordTrace (prefixWord ++ tailWord_1958578) baseStart_1958578 baseEnd_1958578 := by
    simpa [prefixWord, tailWord_1958578, baseEnd_1958578] using wordTrace_append hprefix tailTrace_1958578
  have hstable : (prefixWord ++ tailWord_1958578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958578).length < 2 ^ (prefixWord ++ tailWord_1958578).sum := by decide
  have hdescent : baseEnd_1958578 < baseStart_1958578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958610 : List Nat := [3, 2, 2, 2, 3, 1, 1, 8]
def baseStart_1958610 : Nat := 118140960795 + 1958610 * 2 ^ 59
def prefixEnd_1958610 : Nat := 4983230072969 + 3 ^ 40 * 1958610 * 2
def baseEnd_1958610 : Nat := 74496914422421271338335

theorem tailTrace_1958610 : CollatzResearch.WordTrace tailWord_1958610 prefixEnd_1958610 74496914422421271338335 := by
  unfold tailWord_1958610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17859093858574487200472321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47624250289531965867926189 17859093858574487200472321)
  ·
    refine ⟨13394320393930865400354241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17859093858574487200472321 13394320393930865400354241)
    ·
      refine ⟨10045740295448149050265681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13394320393930865400354241 10045740295448149050265681)
      ·
        refine ⟨7534305221586111787699261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10045740295448149050265681 7534305221586111787699261)
        ·
          refine ⟨2825364458094791920387223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7534305221586111787699261 2825364458094791920387223)
          ·
            refine ⟨4238046687142187880580835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825364458094791920387223 4238046687142187880580835)
            ·
              refine ⟨6357070030713281820871253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238046687142187880580835 6357070030713281820871253)
              ·
                refine ⟨74496914422421271338335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6357070030713281820871253 74496914422421271338335)
                ·
                  rfl

theorem cell22_1958610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_1958610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958610 prefixEnd_1958610 := by exact prefixLift 1958610
  have htrace : WordTrace (prefixWord ++ tailWord_1958610) baseStart_1958610 baseEnd_1958610 := by
    simpa [prefixWord, tailWord_1958610, baseEnd_1958610] using wordTrace_append hprefix tailTrace_1958610
  have hstable : (prefixWord ++ tailWord_1958610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958610).length < 2 ^ (prefixWord ++ tailWord_1958610).sum := by decide
  have hdescent : baseEnd_1958610 < baseStart_1958610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958642 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_1958642 : Nat := 118140960795 + 1958642 * 2 ^ 59
def prefixEnd_1958642 : Nat := 4983230072969 + 3 ^ 40 * 1958642 * 2
def baseEnd_1958642 : Nat := 670483184055754025244917

theorem tailTrace_1958642 : CollatzResearch.WordTrace tailWord_1958642 prefixEnd_1958642 670483184055754025244917 := by
  unfold tailWord_1958642
  simp only [CollatzResearch.WordTrace]
  refine ⟨17859385642545504566763545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47625028380121345511369453 17859385642545504566763545)
  ·
    refine ⟨13394539231909128425072659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17859385642545504566763545 13394539231909128425072659)
    ·
      refine ⟨20091808847863692637608989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13394539231909128425072659 20091808847863692637608989)
      ·
        refine ⟨7534428317948884739103371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20091808847863692637608989 7534428317948884739103371)
        ·
          refine ⟨11301642476923327108655057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7534428317948884739103371 11301642476923327108655057)
          ·
            refine ⟨8476231857692495331491293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11301642476923327108655057 8476231857692495331491293)
            ·
              refine ⟨3178586946634685749309235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8476231857692495331491293 3178586946634685749309235)
              ·
                refine ⟨4767880419952028623963853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178586946634685749309235 4767880419952028623963853)
                ·
                  refine ⟨1787955157482010733986445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4767880419952028623963853 1787955157482010733986445)
                  ·
                    refine ⟨670483184055754025244917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1787955157482010733986445 670483184055754025244917)
                    ·
                      rfl

theorem cell22_1958642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_1958642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958642 prefixEnd_1958642 := by exact prefixLift 1958642
  have htrace : WordTrace (prefixWord ++ tailWord_1958642) baseStart_1958642 baseEnd_1958642 := by
    simpa [prefixWord, tailWord_1958642, baseEnd_1958642] using wordTrace_append hprefix tailTrace_1958642
  have hstable : (prefixWord ++ tailWord_1958642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958642).length < 2 ^ (prefixWord ++ tailWord_1958642).sum := by decide
  have hdescent : baseEnd_1958642 < baseStart_1958642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958644 : List Nat := [2, 6, 1, 1, 2, 1, 2, 7]
def baseStart_1958644 : Nat := 118140960795 + 1958644 * 2 ^ 59
def prefixEnd_1958644 : Nat := 4983230072969 + 3 ^ 40 * 1958644 * 2
def baseEnd_1958644 : Nat := 74498207632958520743879

theorem tailTrace_1958644 : CollatzResearch.WordTrace tailWord_1958644 prefixEnd_1958644 74498207632958520743879 := by
  unfold tailWord_1958644
  simp only [CollatzResearch.WordTrace]
  refine ⟨35718807758087386304313493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47625077010783181739084657 35718807758087386304313493)
  ·
    refine ⟨1674319113660346233014695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35718807758087386304313493 1674319113660346233014695)
    ·
      refine ⟨2511478670490519349522043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674319113660346233014695 2511478670490519349522043)
      ·
        refine ⟨3767218005735779024283065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511478670490519349522043 3767218005735779024283065)
        ·
          refine ⟨2825413504301834268212299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3767218005735779024283065 2825413504301834268212299)
          ·
            refine ⟨4238120256452751402318449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825413504301834268212299 4238120256452751402318449)
            ·
              refine ⟨3178590192339563551738837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4238120256452751402318449 3178590192339563551738837)
              ·
                refine ⟨74498207632958520743879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3178590192339563551738837 74498207632958520743879)
                ·
                  rfl

theorem cell22_1958644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 7].length) (baseStart_1958644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958644 prefixEnd_1958644 := by exact prefixLift 1958644
  have htrace : WordTrace (prefixWord ++ tailWord_1958644) baseStart_1958644 baseEnd_1958644 := by
    simpa [prefixWord, tailWord_1958644, baseEnd_1958644] using wordTrace_append hprefix tailTrace_1958644
  have hstable : (prefixWord ++ tailWord_1958644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958644).length < 2 ^ (prefixWord ++ tailWord_1958644).sum := by decide
  have hdescent : baseEnd_1958644 < baseStart_1958644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958653 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1958653 : Nat := 118140960795 + 1958653 * 2 ^ 59
def prefixEnd_1958653 : Nat := 4983230072969 + 3 ^ 40 * 1958653 * 2
def baseEnd_1958653 : Nat := 670486949580553663219883

theorem tailTrace_1958653 : CollatzResearch.WordTrace tailWord_1958653 prefixEnd_1958653 670486949580553663219883 := by
  unfold tailWord_1958653
  simp only [CollatzResearch.WordTrace]
  refine ⟨71437943773142167145704613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47625295848761444763803075 71437943773142167145704613)
  ·
    refine ⟨13394614457464156339819615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71437943773142167145704613 13394614457464156339819615)
    ·
      refine ⟨20091921686196234509729423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13394614457464156339819615 20091921686196234509729423)
      ·
        refine ⟨30137882529294351764594135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20091921686196234509729423 30137882529294351764594135)
        ·
          refine ⟨45206823793941527646891203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30137882529294351764594135 45206823793941527646891203)
          ·
            refine ⟨67810235690912291470336805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45206823793941527646891203 67810235690912291470336805)
            ·
              refine ⟨12714419192046054650688151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67810235690912291470336805 12714419192046054650688151)
              ·
                refine ⟨19071628788069081976032227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12714419192046054650688151 19071628788069081976032227)
                ·
                  refine ⟨28607443182103622964048341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19071628788069081976032227 28607443182103622964048341)
                  ·
                    refine ⟨670486949580553663219883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28607443182103622964048341 670486949580553663219883)
                    ·
                      rfl

theorem cell22_1958653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1958653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958653 prefixEnd_1958653 := by exact prefixLift 1958653
  have htrace : WordTrace (prefixWord ++ tailWord_1958653) baseStart_1958653 baseEnd_1958653 := by
    simpa [prefixWord, tailWord_1958653, baseEnd_1958653] using wordTrace_append hprefix tailTrace_1958653
  have hstable : (prefixWord ++ tailWord_1958653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958653).length < 2 ^ (prefixWord ++ tailWord_1958653).sum := by decide
  have hdescent : baseEnd_1958653 < baseStart_1958653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958702 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1958702 : Nat := 118140960795 + 1958702 * 2 ^ 59
def prefixEnd_1958702 : Nat := 4983230072969 + 3 ^ 40 * 1958702 * 2
def baseEnd_1958702 : Nat := 670503723281933868744733

theorem tailTrace_1958702 : CollatzResearch.WordTrace tailWord_1958702 prefixEnd_1958702 670503723281933868744733 := by
  unfold tailWord_1958702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8929966368745581064279795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47626487299976432342825573 8929966368745581064279795)
  ·
    refine ⟨13394949553118371596419693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8929966368745581064279795 13394949553118371596419693)
    ·
      refine ⟨5023106082419389348657385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13394949553118371596419693 5023106082419389348657385)
      ·
        refine ⟨3767329561814542011493039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5023106082419389348657385 3767329561814542011493039)
        ·
          refine ⟨5650994342721813017239559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3767329561814542011493039 5650994342721813017239559)
          ·
            refine ⟨8476491514082719525859339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650994342721813017239559 8476491514082719525859339)
            ·
              refine ⟨12714737271124079288789009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8476491514082719525859339 12714737271124079288789009)
              ·
                refine ⟨9536052953343059466591757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12714737271124079288789009 9536052953343059466591757)
                ·
                  refine ⟨3576019857503647299971909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9536052953343059466591757 3576019857503647299971909)
                  ·
                    refine ⟨670503723281933868744733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3576019857503647299971909 670503723281933868744733)
                    ·
                      rfl

theorem cell22_1958702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1958702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958702 prefixEnd_1958702 := by exact prefixLift 1958702
  have htrace : WordTrace (prefixWord ++ tailWord_1958702) baseStart_1958702 baseEnd_1958702 := by
    simpa [prefixWord, tailWord_1958702, baseEnd_1958702] using wordTrace_append hprefix tailTrace_1958702
  have hstable : (prefixWord ++ tailWord_1958702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958702).length < 2 ^ (prefixWord ++ tailWord_1958702).sum := by decide
  have hdescent : baseEnd_1958702 < baseStart_1958702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958717 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 6]
def baseStart_1958717 : Nat := 118140960795 + 1958717 * 2 ^ 59
def prefixEnd_1958717 : Nat := 4983230072969 + 3 ^ 40 * 1958717 * 2
def baseEnd_1958717 : Nat := 223502952696159609873229

theorem tailTrace_1958717 : CollatzResearch.WordTrace tailWord_1958717 prefixEnd_1958717 223502952696159609873229 := by
  unfold tailWord_1958717
  simp only [CollatzResearch.WordTrace]
  refine ⟨71440278044910306076034405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47626852029940204050689603 71440278044910306076034405)
  ·
    refine ⟨13395052133420682389256451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71440278044910306076034405 13395052133420682389256451)
    ·
      refine ⟨20092578200131023583884677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13395052133420682389256451 20092578200131023583884677)
      ·
        refine ⟨3767358412524566921978377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20092578200131023583884677 3767358412524566921978377)
        ·
          refine ⟨2825518809393425191483783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3767358412524566921978377 2825518809393425191483783)
          ·
            refine ⟨4238278214090137787225675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825518809393425191483783 4238278214090137787225675)
            ·
              refine ⟨6357417321135206680838513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238278214090137787225675 6357417321135206680838513)
              ·
                refine ⟨4768062990851405010628885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357417321135206680838513 4768062990851405010628885)
                ·
                  refine ⟨223502952696159609873229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4768062990851405010628885 223502952696159609873229)
                  ·
                    rfl

theorem cell22_1958717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_1958717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958717 prefixEnd_1958717 := by exact prefixLift 1958717
  have htrace : WordTrace (prefixWord ++ tailWord_1958717) baseStart_1958717 baseEnd_1958717 := by
    simpa [prefixWord, tailWord_1958717, baseEnd_1958717] using wordTrace_append hprefix tailTrace_1958717
  have hstable : (prefixWord ++ tailWord_1958717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958717).length < 2 ^ (prefixWord ++ tailWord_1958717).sum := by decide
  have hdescent : baseEnd_1958717 < baseStart_1958717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958730 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_1958730 : Nat := 118140960795 + 1958730 * 2 ^ 59
def prefixEnd_1958730 : Nat := 4983230072969 + 3 ^ 40 * 1958730 * 2
def baseEnd_1958730 : Nat := 670513308254151129044647

theorem tailTrace_1958730 : CollatzResearch.WordTrace tailWord_1958730 prefixEnd_1958730 670513308254151129044647 := by
  unfold tailWord_1958730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17860188048465802324064411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47627168129242139530838429 17860188048465802324064411)
  ·
    refine ⟨26790282072698703486096617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17860188048465802324064411 26790282072698703486096617)
    ·
      refine ⟨20092711554524027614572463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26790282072698703486096617 20092711554524027614572463)
      ·
        refine ⟨30139067331786041421858695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20092711554524027614572463 30139067331786041421858695)
        ·
          refine ⟨45208600997679062132788043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30139067331786041421858695 45208600997679062132788043)
          ·
            refine ⟨67812901496518593199182065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45208600997679062132788043 67812901496518593199182065)
            ·
              refine ⟨50859676122388944899386549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67812901496518593199182065 50859676122388944899386549)
              ·
                refine ⟨4768094636473963584317489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50859676122388944899386549 4768094636473963584317489)
                ·
                  refine ⟨3576070977355472688238117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4768094636473963584317489 3576070977355472688238117)
                  ·
                    refine ⟨670513308254151129044647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3576070977355472688238117 670513308254151129044647)
                    ·
                      rfl

theorem cell22_1958730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_1958730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958730 prefixEnd_1958730 := by exact prefixLift 1958730
  have htrace : WordTrace (prefixWord ++ tailWord_1958730) baseStart_1958730 baseEnd_1958730 := by
    simpa [prefixWord, tailWord_1958730, baseEnd_1958730] using wordTrace_append hprefix tailTrace_1958730
  have hstable : (prefixWord ++ tailWord_1958730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958730).length < 2 ^ (prefixWord ++ tailWord_1958730).sum := by decide
  have hdescent : baseEnd_1958730 < baseStart_1958730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958766 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_1958766 : Nat := 118140960795 + 1958766 * 2 ^ 59
def prefixEnd_1958766 : Nat := 4983230072969 + 3 ^ 40 * 1958766 * 2
def baseEnd_1958766 : Nat := 670525631789859035144537

theorem tailTrace_1958766 : CollatzResearch.WordTrace tailWord_1958766 prefixEnd_1958766 670525631789859035144537 := by
  unfold tailWord_1958766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8930258152716598430571019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47628043481155191629712101 8930258152716598430571019)
  ·
    refine ⟨13395387229074897645856529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8930258152716598430571019 13395387229074897645856529)
    ·
      refine ⟨10046540421806173234392397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13395387229074897645856529 10046540421806173234392397)
      ·
        refine ⟨3767452658177314962897149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10046540421806173234392397 3767452658177314962897149)
        ·
          refine ⟨1412794746816493111086431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3767452658177314962897149 1412794746816493111086431)
          ·
            refine ⟨2119192120224739666629647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412794746816493111086431 2119192120224739666629647)
            ·
              refine ⟨3178788180337109499944471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119192120224739666629647 3178788180337109499944471)
              ·
                refine ⟨4768182270505664249916707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178788180337109499944471 4768182270505664249916707)
                ·
                  refine ⟨7152273405758496374875061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768182270505664249916707 7152273405758496374875061)
                  ·
                    refine ⟨670525631789859035144537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7152273405758496374875061 670525631789859035144537)
                    ·
                      rfl

theorem cell22_1958766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_1958766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958766 prefixEnd_1958766 := by exact prefixLift 1958766
  have htrace : WordTrace (prefixWord ++ tailWord_1958766) baseStart_1958766 baseEnd_1958766 := by
    simpa [prefixWord, tailWord_1958766, baseEnd_1958766] using wordTrace_append hprefix tailTrace_1958766
  have hstable : (prefixWord ++ tailWord_1958766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958766).length < 2 ^ (prefixWord ++ tailWord_1958766).sum := by decide
  have hdescent : baseEnd_1958766 < baseStart_1958766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958777 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 3, 3]
def baseStart_1958777 : Nat := 118140960795 + 1958777 * 2 ^ 59
def prefixEnd_1958777 : Nat := 4983230072969 + 3 ^ 40 * 1958777 * 2
def baseEnd_1958777 : Nat := 670529397314658673119503

theorem tailTrace_1958777 : CollatzResearch.WordTrace tailWord_1958777 prefixEnd_1958777 670529397314658673119503 := by
  unfold tailWord_1958777
  simp only [CollatzResearch.WordTrace]
  refine ⟨71442466424692936323218585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47628310949795290882145723 71442466424692936323218585)
  ·
    refine ⟨53581849818519702242413939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71442466424692936323218585 53581849818519702242413939)
    ·
      refine ⟨80372774727779553363620909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53581849818519702242413939 80372774727779553363620909)
      ·
        refine ⟨30139790522917332511357841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80372774727779553363620909 30139790522917332511357841)
        ·
          refine ⟨22604842892187999383518381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30139790522917332511357841 22604842892187999383518381)
          ·
            refine ⟨8476816084570499768819393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22604842892187999383518381 8476816084570499768819393)
            ·
              refine ⟨6357612063427874826614545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8476816084570499768819393 6357612063427874826614545)
              ·
                refine ⟨4768209047570906119960909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357612063427874826614545 4768209047570906119960909)
                ·
                  refine ⟨1788078392839089794985341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4768209047570906119960909 1788078392839089794985341)
                  ·
                    refine ⟨670529397314658673119503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1788078392839089794985341 670529397314658673119503)
                    ·
                      rfl

theorem cell22_1958777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 3].length) (baseStart_1958777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958777 prefixEnd_1958777 := by exact prefixLift 1958777
  have htrace : WordTrace (prefixWord ++ tailWord_1958777) baseStart_1958777 baseEnd_1958777 := by
    simpa [prefixWord, tailWord_1958777, baseEnd_1958777] using wordTrace_append hprefix tailTrace_1958777
  have hstable : (prefixWord ++ tailWord_1958777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958777).length < 2 ^ (prefixWord ++ tailWord_1958777).sum := by decide
  have hdescent : baseEnd_1958777 < baseStart_1958777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958837 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1958837 : Nat := 118140960795 + 1958837 * 2 ^ 59
def prefixEnd_1958837 : Nat := 4983230072969 + 3 ^ 40 * 1958837 * 2
def baseEnd_1958837 : Nat := 670549936540838516619319

theorem tailTrace_1958837 : CollatzResearch.WordTrace tailWord_1958837 prefixEnd_1958837 670549936540838516619319 := by
  unfold tailWord_1958837
  simp only [CollatzResearch.WordTrace]
  refine ⟨71444654804475566570402765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47629769869650377713601843 71444654804475566570402765)
  ·
    refine ⟨26791745551678337463901037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71444654804475566570402765 26791745551678337463901037)
    ·
      refine ⟨10046904581879376548962889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26791745551678337463901037 10046904581879376548962889)
      ·
        refine ⟨7535178436409532411722167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10046904581879376548962889 7535178436409532411722167)
        ·
          refine ⟨11302767654614298617583251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7535178436409532411722167 11302767654614298617583251)
          ·
            refine ⟨16954151481921447926374877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11302767654614298617583251 16954151481921447926374877)
            ·
              refine ⟨6357806805720542972390579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16954151481921447926374877 6357806805720542972390579)
              ·
                refine ⟨9536710208580814458585869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6357806805720542972390579 9536710208580814458585869)
                ·
                  refine ⟨3576266328217805421969701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9536710208580814458585869 3576266328217805421969701)
                  ·
                    refine ⟨670549936540838516619319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3576266328217805421969701 670549936540838516619319)
                    ·
                      rfl

theorem cell22_1958837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1958837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1958837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1958837 prefixEnd_1958837 := by exact prefixLift 1958837
  have htrace : WordTrace (prefixWord ++ tailWord_1958837) baseStart_1958837 baseEnd_1958837 := by
    simpa [prefixWord, tailWord_1958837, baseEnd_1958837] using wordTrace_append hprefix tailTrace_1958837
  have hstable : (prefixWord ++ tailWord_1958837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958837).length < 2 ^ (prefixWord ++ tailWord_1958837).sum := by decide
  have hdescent : baseEnd_1958837 < baseStart_1958837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959036 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 2, 3]
def baseStart_1959036 : Nat := 118140960795 + 1959036 * 2 ^ 59
def prefixEnd_1959036 : Nat := 4983230072969 + 3 ^ 40 * 1959036 * 2
def baseEnd_1959036 : Nat := 670618058307668330893709

theorem tailTrace_1959036 : CollatzResearch.WordTrace tailWord_1959036 prefixEnd_1959036 670618058307668330893709 := by
  unfold tailWord_1959036
  simp only [CollatzResearch.WordTrace]
  refine ⟨35725956465377311778448481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47634608620503082371264641 35725956465377311778448481)
  ·
    refine ⟨26794467349032983833836361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35725956465377311778448481 26794467349032983833836361)
    ·
      refine ⟨20095850511774737875377271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26794467349032983833836361 20095850511774737875377271)
      ·
        refine ⟨30143775767662106813065907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20095850511774737875377271 30143775767662106813065907)
        ·
          refine ⟨45215663651493160219598861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30143775767662106813065907 45215663651493160219598861)
          ·
            refine ⟨16955873869309935082349573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45215663651493160219598861 16955873869309935082349573)
            ·
              refine ⟨3179226350495612827940545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16955873869309935082349573 3179226350495612827940545)
              ·
                refine ⟨2384419762871709620955409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3179226350495612827940545 2384419762871709620955409)
                ·
                  refine ⟨1788314822153782215716557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2384419762871709620955409 1788314822153782215716557)
                  ·
                    refine ⟨670618058307668330893709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1788314822153782215716557 670618058307668330893709)
                    ·
                      rfl

theorem cell22_1959036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_1959036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959036 prefixEnd_1959036 := by exact prefixLift 1959036
  have htrace : WordTrace (prefixWord ++ tailWord_1959036) baseStart_1959036 baseEnd_1959036 := by
    simpa [prefixWord, tailWord_1959036, baseEnd_1959036] using wordTrace_append hprefix tailTrace_1959036
  have hstable : (prefixWord ++ tailWord_1959036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959036).length < 2 ^ (prefixWord ++ tailWord_1959036).sum := by decide
  have hdescent : baseEnd_1959036 < baseStart_1959036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959047 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1959047 : Nat := 118140960795 + 1959047 * 2 ^ 59
def prefixEnd_1959047 : Nat := 4983230072969 + 3 ^ 40 * 1959047 * 2
def baseEnd_1959047 : Nat := 670621823832467968868675

theorem tailTrace_1959047 : CollatzResearch.WordTrace tailWord_1959047 prefixEnd_1959047 670621823832467968868675 := by
  unfold tailWord_1959047
  simp only [CollatzResearch.WordTrace]
  refine ⟨71452314133714772435547395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47634876089143181623698263 71452314133714772435547395)
  ·
    refine ⟨107178471200572158653321093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71452314133714772435547395 107178471200572158653321093)
    ·
      refine ⟨20095963350107279747497705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107178471200572158653321093 20095963350107279747497705)
      ·
        refine ⟨15071972512580459810623279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20095963350107279747497705 15071972512580459810623279)
        ·
          refine ⟨22607958768870689715934919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15071972512580459810623279 22607958768870689715934919)
          ·
            refine ⟨33911938153306034573902379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22607958768870689715934919 33911938153306034573902379)
            ·
              refine ⟨50867907229959051860853569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33911938153306034573902379 50867907229959051860853569)
              ·
                refine ⟨38150930422469288895640177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50867907229959051860853569 38150930422469288895640177)
                ·
                  refine ⟨28613197816851966671730133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38150930422469288895640177 28613197816851966671730133)
                  ·
                    refine ⟨670621823832467968868675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28613197816851966671730133 670621823832467968868675)
                    ·
                      rfl

theorem cell22_1959047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1959047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959047 prefixEnd_1959047 := by exact prefixLift 1959047
  have htrace : WordTrace (prefixWord ++ tailWord_1959047) baseStart_1959047 baseEnd_1959047 := by
    simpa [prefixWord, tailWord_1959047, baseEnd_1959047] using wordTrace_append hprefix tailTrace_1959047
  have hstable : (prefixWord ++ tailWord_1959047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959047).length < 2 ^ (prefixWord ++ tailWord_1959047).sum := by decide
  have hdescent : baseEnd_1959047 < baseStart_1959047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959049 : List Nat := [1, 2, 1, 1, 4, 5, 1, 7]
def baseStart_1959049 : Nat := 118140960795 + 1959049 * 2 ^ 59
def prefixEnd_1959049 : Nat := 4983230072969 + 3 ^ 40 * 1959049 * 2
def baseEnd_1959049 : Nat := 74513612052593403368741

theorem tailTrace_1959049 : CollatzResearch.WordTrace tailWord_1959049 prefixEnd_1959049 74513612052593403368741 := by
  unfold tailWord_1959049
  simp only [CollatzResearch.WordTrace]
  refine ⟨71452387079707526777120201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47634924719805017851413467 71452387079707526777120201)
  ·
    refine ⟨53589290309780645082840151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71452387079707526777120201 53589290309780645082840151)
    ·
      refine ⟨80383935464670967624260227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53589290309780645082840151 80383935464670967624260227)
      ·
        refine ⟨120575903197006451436390341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80383935464670967624260227 120575903197006451436390341)
        ·
          refine ⟨22607981849438709644323189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120575903197006451436390341 22607981849438709644323189)
          ·
            refine ⟨2119498298384879029155299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22607981849438709644323189 2119498298384879029155299)
            ·
              refine ⟨3179247447577318543732949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119498298384879029155299 3179247447577318543732949)
              ·
                refine ⟨74513612052593403368741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3179247447577318543732949 74513612052593403368741)
                ·
                  rfl

theorem cell22_1959049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 7].length) (baseStart_1959049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959049 prefixEnd_1959049 := by exact prefixLift 1959049
  have htrace : WordTrace (prefixWord ++ tailWord_1959049) baseStart_1959049 baseEnd_1959049 := by
    simpa [prefixWord, tailWord_1959049, baseEnd_1959049] using wordTrace_append hprefix tailTrace_1959049
  have hstable : (prefixWord ++ tailWord_1959049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959049).length < 2 ^ (prefixWord ++ tailWord_1959049).sum := by decide
  have hdescent : baseEnd_1959049 < baseStart_1959049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959066 : List Nat := [3, 1, 1, 5, 1, 2, 3, 6]
def baseStart_1959066 : Nat := 118140960795 + 1959066 * 2 ^ 59
def prefixEnd_1959066 : Nat := 4983230072969 + 3 ^ 40 * 1959066 * 2
def baseEnd_1959066 : Nat := 74514258657862028071513

theorem tailTrace_1959066 : CollatzResearch.WordTrace tailWord_1959066 prefixEnd_1959066 74514258657862028071513 := by
  unfold tailWord_1959066
  simp only [CollatzResearch.WordTrace]
  refine ⟨17863251780161484670122263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47635338080430625786992701 17863251780161484670122263)
  ·
    refine ⟨26794877670242227005183395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17863251780161484670122263 26794877670242227005183395)
    ·
      refine ⟨40192316505363340507775093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26794877670242227005183395 40192316505363340507775093)
      ·
        refine ⟨3768029672377813172603915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40192316505363340507775093 3768029672377813172603915)
        ·
          refine ⟨5652044508566719758905873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768029672377813172603915 5652044508566719758905873)
          ·
            refine ⟨4239033381425039819179405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5652044508566719758905873 4239033381425039819179405)
            ·
              refine ⟨1589637518034389932192277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4239033381425039819179405 1589637518034389932192277)
              ·
                refine ⟨74514258657862028071513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1589637518034389932192277 74514258657862028071513)
                ·
                  rfl

theorem cell22_1959066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_1959066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959066 prefixEnd_1959066 := by exact prefixLift 1959066
  have htrace : WordTrace (prefixWord ++ tailWord_1959066) baseStart_1959066 baseEnd_1959066 := by
    simpa [prefixWord, tailWord_1959066, baseEnd_1959066] using wordTrace_append hprefix tailTrace_1959066
  have hstable : (prefixWord ++ tailWord_1959066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959066).length < 2 ^ (prefixWord ++ tailWord_1959066).sum := by decide
  have hdescent : baseEnd_1959066 < baseStart_1959066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959107 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 2, 8]
def baseStart_1959107 : Nat := 118140960795 + 1959107 * 2 ^ 59
def prefixEnd_1959107 : Nat := 4983230072969 + 3 ^ 40 * 1959107 * 2
def baseEnd_1959107 : Nat := 670642363058647812368491

theorem tailTrace_1959107 : CollatzResearch.WordTrace tailWord_1959107 prefixEnd_1959107 670642363058647812368491 := by
  unfold tailWord_1959107
  simp only [CollatzResearch.WordTrace]
  refine ⟨71454502513497402682731575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47636335008998268455154383 71454502513497402682731575)
  ·
    refine ⟨107181753770246104024097363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71454502513497402682731575 107181753770246104024097363)
    ·
      refine ⟨160772630655369156036146045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107181753770246104024097363 160772630655369156036146045)
      ·
        refine ⟨60289736495763433513554767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160772630655369156036146045 60289736495763433513554767)
        ·
          refine ⟨90434604743645150270332151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60289736495763433513554767 90434604743645150270332151)
          ·
            refine ⟨135651907115467725405498227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90434604743645150270332151 135651907115467725405498227)
            ·
              refine ⟨203477860673201588108247341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135651907115467725405498227 203477860673201588108247341)
              ·
                refine ⟨76304197752450595540592753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203477860673201588108247341 76304197752450595540592753)
                ·
                  refine ⟨57228148314337946655444565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76304197752450595540592753 57228148314337946655444565)
                  ·
                    refine ⟨670642363058647812368491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57228148314337946655444565 670642363058647812368491)
                    ·
                      rfl

theorem cell22_1959107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_1959107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959107 prefixEnd_1959107 := by exact prefixLift 1959107
  have htrace : WordTrace (prefixWord ++ tailWord_1959107) baseStart_1959107 baseEnd_1959107 := by
    simpa [prefixWord, tailWord_1959107, baseEnd_1959107] using wordTrace_append hprefix tailTrace_1959107
  have hstable : (prefixWord ++ tailWord_1959107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959107).length < 2 ^ (prefixWord ++ tailWord_1959107).sum := by decide
  have hdescent : baseEnd_1959107 < baseStart_1959107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959117 : List Nat := [1, 6, 2, 2, 2, 1, 2, 6]
def baseStart_1959117 : Nat := 118140960795 + 1959117 * 2 ^ 59
def prefixEnd_1959117 : Nat := 4983230072969 + 3 ^ 40 * 1959117 * 2
def baseEnd_1959117 : Nat := 74516198473667902179829

theorem tailTrace_1959117 : CollatzResearch.WordTrace tailWord_1959117 prefixEnd_1959117 74516198473667902179829 := by
  unfold tailWord_1959117
  simp only [CollatzResearch.WordTrace]
  refine ⟨71454867243461174390595605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47636578162307449593730403 71454867243461174390595605)
  ·
    refine ⟨3349446902037242549559169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71454867243461174390595605 3349446902037242549559169)
    ·
      refine ⟨2512085176527931912169377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3349446902037242549559169 2512085176527931912169377)
      ·
        refine ⟨1884063882395948934127033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2512085176527931912169377 1884063882395948934127033)
        ·
          refine ⟨1413047911796961700595275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1884063882395948934127033 1413047911796961700595275)
          ·
            refine ⟨2119571867695442550892913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413047911796961700595275 2119571867695442550892913)
            ·
              refine ⟨1589678900771581913169685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2119571867695442550892913 1589678900771581913169685)
              ·
                refine ⟨74516198473667902179829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1589678900771581913169685 74516198473667902179829)
                ·
                  rfl

theorem cell22_1959117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 6].length) (baseStart_1959117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959117 prefixEnd_1959117 := by exact prefixLift 1959117
  have htrace : WordTrace (prefixWord ++ tailWord_1959117) baseStart_1959117 baseEnd_1959117 := by
    simpa [prefixWord, tailWord_1959117, baseEnd_1959117] using wordTrace_append hprefix tailTrace_1959117
  have hstable : (prefixWord ++ tailWord_1959117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959117).length < 2 ^ (prefixWord ++ tailWord_1959117).sum := by decide
  have hdescent : baseEnd_1959117 < baseStart_1959117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959216 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 3, 3]
def baseStart_1959216 : Nat := 118140960795 + 1959216 * 2 ^ 59
def prefixEnd_1959216 : Nat := 4983230072969 + 3 ^ 40 * 1959216 * 2
def baseEnd_1959216 : Nat := 670679675986207861393157

theorem tailTrace_1959216 : CollatzResearch.WordTrace tailWord_1959216 prefixEnd_1959216 670679675986207861393157 := by
  unfold tailWord_1959216
  simp only [CollatzResearch.WordTrace]
  refine ⟨35729239035051257149224751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47638985380068342865633001 35729239035051257149224751)
  ·
    refine ⟨53593858552576885723837127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35729239035051257149224751 53593858552576885723837127)
    ·
      refine ⟨80390787828865328585755691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53593858552576885723837127 80390787828865328585755691)
      ·
        refine ⟨120586181743297992878633537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80390787828865328585755691 120586181743297992878633537)
        ·
          refine ⟨90439636307473494658975153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120586181743297992878633537 90439636307473494658975153)
          ·
            refine ⟨67829727230605120994231365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90439636307473494658975153 67829727230605120994231365)
            ·
              refine ⟨12718073855738460186418381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67829727230605120994231365 12718073855738460186418381)
              ·
                refine ⟨4769277695901922569906893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12718073855738460186418381 4769277695901922569906893)
                ·
                  refine ⟨1788479135963220963715085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4769277695901922569906893 1788479135963220963715085)
                  ·
                    refine ⟨670679675986207861393157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1788479135963220963715085 670679675986207861393157)
                    ·
                      rfl

theorem cell22_1959216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3, 3].length) (baseStart_1959216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959216 prefixEnd_1959216 := by exact prefixLift 1959216
  have htrace : WordTrace (prefixWord ++ tailWord_1959216) baseStart_1959216 baseEnd_1959216 := by
    simpa [prefixWord, tailWord_1959216, baseEnd_1959216] using wordTrace_append hprefix tailTrace_1959216
  have hstable : (prefixWord ++ tailWord_1959216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959216).length < 2 ^ (prefixWord ++ tailWord_1959216).sum := by decide
  have hdescent : baseEnd_1959216 < baseStart_1959216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959233 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1959233 : Nat := 118140960795 + 1959233 * 2 ^ 59
def prefixEnd_1959233 : Nat := 4983230072969 + 3 ^ 40 * 1959233 * 2
def baseEnd_1959233 : Nat := 670685495433625483718105

theorem tailTrace_1959233 : CollatzResearch.WordTrace tailWord_1959233 prefixEnd_1959233 670685495433625483718105 := by
  unfold tailWord_1959233
  simp only [CollatzResearch.WordTrace]
  refine ⟨71459098111040926201818353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47639398740693950801212235 71459098111040926201818353)
  ·
    refine ⟨53594323583280694651363765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71459098111040926201818353 53594323583280694651363765)
    ·
      refine ⟨5024467835932565123565353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53594323583280694651363765 5024467835932565123565353)
      ·
        refine ⟨3768350876949423842674015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5024467835932565123565353 3768350876949423842674015)
        ·
          refine ⟨5652526315424135764011023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768350876949423842674015 5652526315424135764011023)
          ·
            refine ⟨8478789473136203646016535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652526315424135764011023 8478789473136203646016535)
            ·
              refine ⟨12718184209704305469024803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478789473136203646016535 12718184209704305469024803)
              ·
                refine ⟨19077276314556458203537205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12718184209704305469024803 19077276314556458203537205)
                ·
                  refine ⟨1788494654489667956581613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19077276314556458203537205 1788494654489667956581613)
                  ·
                    refine ⟨670685495433625483718105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1788494654489667956581613 670685495433625483718105)
                    ·
                      rfl

theorem cell22_1959233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1959233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959233 prefixEnd_1959233 := by exact prefixLift 1959233
  have htrace : WordTrace (prefixWord ++ tailWord_1959233) baseStart_1959233 baseEnd_1959233 := by
    simpa [prefixWord, tailWord_1959233, baseEnd_1959233] using wordTrace_append hprefix tailTrace_1959233
  have hstable : (prefixWord ++ tailWord_1959233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959233).length < 2 ^ (prefixWord ++ tailWord_1959233).sum := by decide
  have hdescent : baseEnd_1959233 < baseStart_1959233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959293 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_1959293 : Nat := 118140960795 + 1959293 * 2 ^ 59
def prefixEnd_1959293 : Nat := 4983230072969 + 3 ^ 40 * 1959293 * 2
def baseEnd_1959293 : Nat := 670706034659805327217921

theorem tailTrace_1959293 : CollatzResearch.WordTrace tailWord_1959293 prefixEnd_1959293 670706034659805327217921 := by
  unfold tailWord_1959293
  simp only [CollatzResearch.WordTrace]
  refine ⟨71461286490823556449002533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47640857660549037632668355 71461286490823556449002533)
  ·
    refine ⟨13398991217029416834187975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71461286490823556449002533 13398991217029416834187975)
    ·
      refine ⟨20098486825544125251281963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13398991217029416834187975 20098486825544125251281963)
      ·
        refine ⟨30147730238316187876922945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20098486825544125251281963 30147730238316187876922945)
        ·
          refine ⟨22610797678737140907692209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30147730238316187876922945 22610797678737140907692209)
          ·
            refine ⟨16958098259052855680769157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22610797678737140907692209 16958098259052855680769157)
            ·
              refine ⟨3179643423572410440144217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16958098259052855680769157 3179643423572410440144217)
              ·
                refine ⟨2384732567679307830108163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3179643423572410440144217 2384732567679307830108163)
                ·
                  refine ⟨3577098851518961745162245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384732567679307830108163 3577098851518961745162245)
                  ·
                    refine ⟨670706034659805327217921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3577098851518961745162245 670706034659805327217921)
                    ·
                      rfl

theorem cell22_1959293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_1959293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959293 prefixEnd_1959293 := by exact prefixLift 1959293
  have htrace : WordTrace (prefixWord ++ tailWord_1959293) baseStart_1959293 baseEnd_1959293 := by
    simpa [prefixWord, tailWord_1959293, baseEnd_1959293] using wordTrace_append hprefix tailTrace_1959293
  have hstable : (prefixWord ++ tailWord_1959293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959293).length < 2 ^ (prefixWord ++ tailWord_1959293).sum := by decide
  have hdescent : baseEnd_1959293 < baseStart_1959293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959321 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_1959321 : Nat := 118140960795 + 1959321 * 2 ^ 59
def prefixEnd_1959321 : Nat := 4983230072969 + 3 ^ 40 * 1959321 * 2
def baseEnd_1959321 : Nat := 670715619632022587517835

theorem tailTrace_1959321 : CollatzResearch.WordTrace tailWord_1959321 prefixEnd_1959321 670715619632022587517835 := by
  unfold tailWord_1959321
  simp only [CollatzResearch.WordTrace]
  refine ⟨71462307734722117231021817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47641538489814744820681211 71462307734722117231021817)
  ·
    refine ⟨53596730801041587923266363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71462307734722117231021817 53596730801041587923266363)
    ·
      refine ⟨80395096201562381884899545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53596730801041587923266363 80395096201562381884899545)
      ·
        refine ⟨60296322151171786413674659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80395096201562381884899545 60296322151171786413674659)
        ·
          refine ⟨90444483226757679620511989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60296322151171786413674659 90444483226757679620511989)
          ·
            refine ⟨8479170302508532464422999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90444483226757679620511989 8479170302508532464422999)
            ·
              refine ⟨12718755453762798696634499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479170302508532464422999 12718755453762798696634499)
              ·
                refine ⟨19078133180644198044951749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12718755453762798696634499 19078133180644198044951749)
                ·
                  refine ⟨3577149971370787133428453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19078133180644198044951749 3577149971370787133428453)
                  ·
                    refine ⟨670715619632022587517835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3577149971370787133428453 670715619632022587517835)
                    ·
                      rfl

theorem cell22_1959321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_1959321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959321 prefixEnd_1959321 := by exact prefixLift 1959321
  have htrace : WordTrace (prefixWord ++ tailWord_1959321) baseStart_1959321 baseEnd_1959321 := by
    simpa [prefixWord, tailWord_1959321, baseEnd_1959321] using wordTrace_append hprefix tailTrace_1959321
  have hstable : (prefixWord ++ tailWord_1959321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959321).length < 2 ^ (prefixWord ++ tailWord_1959321).sum := by decide
  have hdescent : baseEnd_1959321 < baseStart_1959321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959340 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 2, 3]
def baseStart_1959340 : Nat := 118140960795 + 1959340 * 2 ^ 59
def prefixEnd_1959340 : Nat := 4983230072969 + 3 ^ 40 * 1959340 * 2
def baseEnd_1959340 : Nat := 670722123720312871292777

theorem tailTrace_1959340 : CollatzResearch.WordTrace tailWord_1959340 prefixEnd_1959340 670722123720312871292777 := by
  unfold tailWord_1959340
  simp only [CollatzResearch.WordTrace]
  refine ⟨35731500360826641737981737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47642000481102188983975649 35731500360826641737981737)
  ·
    refine ⟨26798625270619981303486303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35731500360826641737981737 26798625270619981303486303)
    ·
      refine ⟨40197937905929971955229455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26798625270619981303486303 40197937905929971955229455)
      ·
        refine ⟨60296906858894957932844183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40197937905929971955229455 60296906858894957932844183)
        ·
          refine ⟨90445360288342436899266275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60296906858894957932844183 90445360288342436899266275)
          ·
            refine ⟨135668040432513655348899413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90445360288342436899266275 135668040432513655348899413)
            ·
              refine ⟨1589859848818519398619915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 135668040432513655348899413 1589859848818519398619915)
              ·
                refine ⟨2384789773227779097929873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589859848818519398619915 2384789773227779097929873)
                ·
                  refine ⟨1788592329920834323447405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2384789773227779097929873 1788592329920834323447405)
                  ·
                    refine ⟨670722123720312871292777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1788592329920834323447405 670722123720312871292777)
                    ·
                      rfl

theorem cell22_1959340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_1959340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959340 prefixEnd_1959340 := by exact prefixLift 1959340
  have htrace : WordTrace (prefixWord ++ tailWord_1959340) baseStart_1959340 baseEnd_1959340 := by
    simpa [prefixWord, tailWord_1959340, baseEnd_1959340] using wordTrace_append hprefix tailTrace_1959340
  have hstable : (prefixWord ++ tailWord_1959340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959340).length < 2 ^ (prefixWord ++ tailWord_1959340).sum := by decide
  have hdescent : baseEnd_1959340 < baseStart_1959340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959443 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 6]
def baseStart_1959443 : Nat := 118140960795 + 1959443 * 2 ^ 59
def prefixEnd_1959443 : Nat := 4983230072969 + 3 ^ 40 * 1959443 * 2
def baseEnd_1959443 : Nat := 223585794241751645322487

theorem tailTrace_1959443 : CollatzResearch.WordTrace tailWord_1959443 prefixEnd_1959443 223585794241751645322487 := by
  unfold tailWord_1959443
  simp only [CollatzResearch.WordTrace]
  refine ⟨71466757440280132066962983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47644504960186754711308655 71466757440280132066962983)
  ·
    refine ⟨107200136160420198100444475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71466757440280132066962983 107200136160420198100444475)
    ·
      refine ⟨160800204240630297150666713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107200136160420198100444475 160800204240630297150666713)
      ·
        refine ⟨120600153180472722863000035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160800204240630297150666713 120600153180472722863000035)
        ·
          refine ⟨180900229770709084294500053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120600153180472722863000035 180900229770709084294500053)
          ·
            refine ⟨4239849135250994163152345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 180900229770709084294500053 4239849135250994163152345)
            ·
              refine ⟨3179886851438245622364259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4239849135250994163152345 3179886851438245622364259)
              ·
                refine ⟨4769830277157368433546389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3179886851438245622364259 4769830277157368433546389)
                ·
                  refine ⟨223585794241751645322487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4769830277157368433546389 223585794241751645322487)
                  ·
                    rfl

theorem cell22_1959443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 6].length) (baseStart_1959443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959443 prefixEnd_1959443 := by exact prefixLift 1959443
  have htrace : WordTrace (prefixWord ++ tailWord_1959443) baseStart_1959443 baseEnd_1959443 := by
    simpa [prefixWord, tailWord_1959443, baseEnd_1959443] using wordTrace_append hprefix tailTrace_1959443
  have hstable : (prefixWord ++ tailWord_1959443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959443).length < 2 ^ (prefixWord ++ tailWord_1959443).sum := by decide
  have hdescent : baseEnd_1959443 < baseStart_1959443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959473 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_1959473 : Nat := 118140960795 + 1959473 * 2 ^ 59
def prefixEnd_1959473 : Nat := 4983230072969 + 3 ^ 40 * 1959473 * 2
def baseEnd_1959473 : Nat := 670767652338344857717369

theorem tailTrace_1959473 : CollatzResearch.WordTrace tailWord_1959473 prefixEnd_1959473 670767652338344857717369 := by
  unfold tailWord_1959473
  simp only [CollatzResearch.WordTrace]
  refine ⟨71467851630171447190555073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47645234420114298127036715 71467851630171447190555073)
  ·
    refine ⟨53600888722628585392916305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71467851630171447190555073 53600888722628585392916305)
    ·
      refine ⟨40200666541971439044687229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53600888722628585392916305 40200666541971439044687229)
      ·
        refine ⟨15075249953239289641757711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40200666541971439044687229 15075249953239289641757711)
        ·
          refine ⟨22612874929858934462636567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15075249953239289641757711 22612874929858934462636567)
          ·
            refine ⟨33919312394788401693954851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22612874929858934462636567 33919312394788401693954851)
            ·
              refine ⟨50878968592182602540932277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33919312394788401693954851 50878968592182602540932277)
              ·
                refine ⟨4769903305517118988212401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50878968592182602540932277 4769903305517118988212401)
                ·
                  refine ⟨3577427479137839241159301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4769903305517118988212401 3577427479137839241159301)
                  ·
                    refine ⟨670767652338344857717369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3577427479137839241159301 670767652338344857717369)
                    ·
                      rfl

theorem cell22_1959473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_1959473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959473 prefixEnd_1959473 := by exact prefixLift 1959473
  have htrace : WordTrace (prefixWord ++ tailWord_1959473) baseStart_1959473 baseEnd_1959473 := by
    simpa [prefixWord, tailWord_1959473, baseEnd_1959473] using wordTrace_append hprefix tailTrace_1959473
  have hstable : (prefixWord ++ tailWord_1959473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959473).length < 2 ^ (prefixWord ++ tailWord_1959473).sum := by decide
  have hdescent : baseEnd_1959473 < baseStart_1959473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959477 : List Nat := [1, 3, 3, 1, 1, 5, 1, 3, 4]
def baseStart_1959477 : Nat := 118140960795 + 1959477 * 2 ^ 59
def prefixEnd_1959477 : Nat := 4983230072969 + 3 ^ 40 * 1959477 * 2
def baseEnd_1959477 : Nat := 223589673873363393539119

theorem tailTrace_1959477 : CollatzResearch.WordTrace tailWord_1959477 prefixEnd_1959477 223589673873363393539119 := by
  unfold tailWord_1959477
  simp only [CollatzResearch.WordTrace]
  refine ⟨71467997522156955873700685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47645331681437970582467123 71467997522156955873700685)
  ·
    refine ⟨26800499070808858452637757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71467997522156955873700685 26800499070808858452637757)
    ·
      refine ⟨10050187151553321919739159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26800499070808858452637757 10050187151553321919739159)
      ·
        refine ⟨15075280727329982879608739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10050187151553321919739159 15075280727329982879608739)
        ·
          refine ⟨22612921090994974319413109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15075280727329982879608739 22612921090994974319413109)
          ·
            refine ⟨2119961352280778842444979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22612921090994974319413109 2119961352280778842444979)
            ·
              refine ⟨3179942028421168263667469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119961352280778842444979 3179942028421168263667469)
              ·
                refine ⟨1192478260657938098875301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3179942028421168263667469 1192478260657938098875301)
                ·
                  refine ⟨223589673873363393539119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192478260657938098875301 223589673873363393539119)
                  ·
                    rfl

theorem cell22_1959477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_1959477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959477 prefixEnd_1959477 := by exact prefixLift 1959477
  have htrace : WordTrace (prefixWord ++ tailWord_1959477) baseStart_1959477 baseEnd_1959477 := by
    simpa [prefixWord, tailWord_1959477, baseEnd_1959477] using wordTrace_append hprefix tailTrace_1959477
  have hstable : (prefixWord ++ tailWord_1959477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959477).length < 2 ^ (prefixWord ++ tailWord_1959477).sum := by decide
  have hdescent : baseEnd_1959477 < baseStart_1959477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959494 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1959494 : Nat := 118140960795 + 1959494 * 2 ^ 59
def prefixEnd_1959494 : Nat := 4983230072969 + 3 ^ 40 * 1959494 * 2
def baseEnd_1959494 : Nat := 223591613689169267647435

theorem tailTrace_1959494 : CollatzResearch.WordTrace tailWord_1959494 prefixEnd_1959494 223591613689169267647435 := by
  unfold tailWord_1959494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2233394298846730243033423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47645745042063578518046357 2233394298846730243033423)
  ·
    refine ⟨3350091448270095364550135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2233394298846730243033423 3350091448270095364550135)
    ·
      refine ⟨5025137172405143046825203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350091448270095364550135 5025137172405143046825203)
      ·
        refine ⟨7537705758607714570237805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025137172405143046825203 7537705758607714570237805)
        ·
          refine ⟨2826639659477892963839177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7537705758607714570237805 2826639659477892963839177)
          ·
            refine ⟨2119979744608419722879383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2826639659477892963839177 2119979744608419722879383)
            ·
              refine ⟨3179969616912629584319075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119979744608419722879383 3179969616912629584319075)
              ·
                refine ⟨4769954425368944376478613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3179969616912629584319075 4769954425368944376478613)
                ·
                  refine ⟨223591613689169267647435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4769954425368944376478613 223591613689169267647435)
                  ·
                    rfl

theorem cell22_1959494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1959494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959494 prefixEnd_1959494 := by exact prefixLift 1959494
  have htrace : WordTrace (prefixWord ++ tailWord_1959494) baseStart_1959494 baseEnd_1959494 := by
    simpa [prefixWord, tailWord_1959494, baseEnd_1959494] using wordTrace_append hprefix tailTrace_1959494
  have hstable : (prefixWord ++ tailWord_1959494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959494).length < 2 ^ (prefixWord ++ tailWord_1959494).sum := by decide
  have hdescent : baseEnd_1959494 < baseStart_1959494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959548 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_1959548 : Nat := 118140960795 + 1959548 * 2 ^ 59
def prefixEnd_1959548 : Nat := 4983230072969 + 3 ^ 40 * 1959548 * 2
def baseEnd_1959548 : Nat := 670793326371069662092139

theorem tailTrace_1959548 : CollatzResearch.WordTrace tailWord_1959548 prefixEnd_1959548 670793326371069662092139 := by
  unfold tailWord_1959548
  simp only [CollatzResearch.WordTrace]
  refine ⟨35735293552449867499767649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47647058069933156666356865 35735293552449867499767649)
  ·
    refine ⟨26801470164337400624825737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35735293552449867499767649 26801470164337400624825737)
    ·
      refine ⟨20101102623253050468619303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26801470164337400624825737 20101102623253050468619303)
      ·
        refine ⟨30151653934879575702928955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20101102623253050468619303 30151653934879575702928955)
        ·
          refine ⟨45227480902319363554393433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30151653934879575702928955 45227480902319363554393433)
          ·
            refine ⟨33920610676739522665795075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45227480902319363554393433 33920610676739522665795075)
            ·
              refine ⟨50880916015109283998692613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33920610676739522665795075 50880916015109283998692613)
              ·
                refine ⟨9540171752832990749754865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50880916015109283998692613 9540171752832990749754865)
                ·
                  refine ⟨7155128814624743062316149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9540171752832990749754865 7155128814624743062316149)
                  ·
                    refine ⟨670793326371069662092139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7155128814624743062316149 670793326371069662092139)
                    ·
                      rfl

theorem cell22_1959548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_1959548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959548 prefixEnd_1959548 := by exact prefixLift 1959548
  have htrace : WordTrace (prefixWord ++ tailWord_1959548) baseStart_1959548 baseEnd_1959548 := by
    simpa [prefixWord, tailWord_1959548, baseEnd_1959548] using wordTrace_append hprefix tailTrace_1959548
  have hstable : (prefixWord ++ tailWord_1959548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959548).length < 2 ^ (prefixWord ++ tailWord_1959548).sum := by decide
  have hdescent : baseEnd_1959548 < baseStart_1959548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959563 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 5, 4]
def baseStart_1959563 : Nat := 118140960795 + 1959563 * 2 ^ 59
def prefixEnd_1959563 : Nat := 4983230072969 + 3 ^ 40 * 1959563 * 2
def baseEnd_1959563 : Nat := 670798461177614622967093

theorem tailTrace_1959563 : CollatzResearch.WordTrace tailWord_1959563 prefixEnd_1959563 670798461177614622967093 := by
  unfold tailWord_1959563
  simp only [CollatzResearch.WordTrace]
  refine ⟨71471134199845392561331343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47647422799896928374220895 71471134199845392561331343)
  ·
    refine ⟨107206701299768088841997015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71471134199845392561331343 107206701299768088841997015)
    ·
      refine ⟨160810051949652133262995523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107206701299768088841997015 160810051949652133262995523)
      ·
        refine ⟨241215077924478199894493285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160810051949652133262995523 241215077924478199894493285)
        ·
          refine ⟨45227827110839662480217491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241215077924478199894493285 45227827110839662480217491)
          ·
            refine ⟨67841740666259493720326237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45227827110839662480217491 67841740666259493720326237)
            ·
              refine ⟨25440652749847310145122339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67841740666259493720326237 25440652749847310145122339)
              ·
                refine ⟨38160979124770965217683509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25440652749847310145122339 38160979124770965217683509)
                ·
                  refine ⟨3577591792947277989157829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38160979124770965217683509 3577591792947277989157829)
                  ·
                    refine ⟨670798461177614622967093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3577591792947277989157829 670798461177614622967093)
                    ·
                      rfl

theorem cell22_1959563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 4].length) (baseStart_1959563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959563 prefixEnd_1959563 := by exact prefixLift 1959563
  have htrace : WordTrace (prefixWord ++ tailWord_1959563) baseStart_1959563 baseEnd_1959563 := by
    simpa [prefixWord, tailWord_1959563, baseEnd_1959563] using wordTrace_append hprefix tailTrace_1959563
  have hstable : (prefixWord ++ tailWord_1959563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959563).length < 2 ^ (prefixWord ++ tailWord_1959563).sum := by decide
  have hdescent : baseEnd_1959563 < baseStart_1959563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959597 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1959597 : Nat := 118140960795 + 1959597 * 2 ^ 59
def prefixEnd_1959597 : Nat := 4983230072969 + 3 ^ 40 * 1959597 * 2
def baseEnd_1959597 : Nat := 670810100072449867616989

theorem tailTrace_1959597 : CollatzResearch.WordTrace tailWord_1959597 prefixEnd_1959597 670810100072449867616989 := by
  unfold tailWord_1959597
  simp only [CollatzResearch.WordTrace]
  refine ⟨71472374281722216368069045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47648249521148144245379363 71472374281722216368069045)
  ·
    refine ⟨6700535088911457784506473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71472374281722216368069045 6700535088911457784506473)
    ·
      refine ⟨5025401316683593338379855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6700535088911457784506473 5025401316683593338379855)
      ·
        refine ⟨7538101975025390007569783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025401316683593338379855 7538101975025390007569783)
        ·
          refine ⟨11307152962538085011354675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7538101975025390007569783 11307152962538085011354675)
          ·
            refine ⟨16960729443807127517032013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11307152962538085011354675 16960729443807127517032013)
            ·
              refine ⟨6360273541427672818887005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16960729443807127517032013 6360273541427672818887005)
              ·
                refine ⟨2385102578035377307082627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6360273541427672818887005 2385102578035377307082627)
                ·
                  refine ⟨3577653867053065960623941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385102578035377307082627 3577653867053065960623941)
                  ·
                    refine ⟨670810100072449867616989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3577653867053065960623941 670810100072449867616989)
                    ·
                      rfl

theorem cell22_1959597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1959597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959597 prefixEnd_1959597 := by exact prefixLift 1959597
  have htrace : WordTrace (prefixWord ++ tailWord_1959597) baseStart_1959597 baseEnd_1959597 := by
    simpa [prefixWord, tailWord_1959597, baseEnd_1959597] using wordTrace_append hprefix tailTrace_1959597
  have hstable : (prefixWord ++ tailWord_1959597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959597).length < 2 ^ (prefixWord ++ tailWord_1959597).sum := by decide
  have hdescent : baseEnd_1959597 < baseStart_1959597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959612 : List Nat := [2, 2, 2, 3, 1, 2, 2, 4, 4]
def baseStart_1959612 : Nat := 118140960795 + 1959612 * 2 ^ 59
def prefixEnd_1959612 : Nat := 4983230072969 + 3 ^ 40 * 1959612 * 2
def baseEnd_1959612 : Nat := 223605078292998276163981

theorem tailTrace_1959612 : CollatzResearch.WordTrace tailWord_1959612 prefixEnd_1959612 223605078292998276163981 := by
  unfold tailWord_1959612
  simp only [CollatzResearch.WordTrace]
  refine ⟨35736460688333936964932545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47648614251111915953243393 35736460688333936964932545)
  ·
    refine ⟨26802345516250452723699409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35736460688333936964932545 26802345516250452723699409)
    ·
      refine ⟨20101759137187839542774557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26802345516250452723699409 20101759137187839542774557)
      ·
        refine ⟨7538159676445439828540459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20101759137187839542774557 7538159676445439828540459)
        ·
          refine ⟨11307239514668159742810689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7538159676445439828540459 11307239514668159742810689)
          ·
            refine ⟨8480429636001119807108017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11307239514668159742810689 8480429636001119807108017)
            ·
              refine ⟨6360322227000839855331013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8480429636001119807108017 6360322227000839855331013)
              ·
                refine ⟨1192560417562657472874565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6360322227000839855331013 1192560417562657472874565)
                ·
                  refine ⟨223605078292998276163981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192560417562657472874565 223605078292998276163981)
                  ·
                    rfl

theorem cell22_1959612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_1959612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959612 prefixEnd_1959612 := by exact prefixLift 1959612
  have htrace : WordTrace (prefixWord ++ tailWord_1959612) baseStart_1959612 baseEnd_1959612 := by
    simpa [prefixWord, tailWord_1959612, baseEnd_1959612] using wordTrace_append hprefix tailTrace_1959612
  have hstable : (prefixWord ++ tailWord_1959612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959612).length < 2 ^ (prefixWord ++ tailWord_1959612).sum := by decide
  have hdescent : baseEnd_1959612 < baseStart_1959612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959618 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1959618 : Nat := 118140960795 + 1959618 * 2 ^ 59
def prefixEnd_1959618 : Nat := 4983230072969 + 3 ^ 40 * 1959618 * 2
def baseEnd_1959618 : Nat := 223605762933870937613975

theorem tailTrace_1959618 : CollatzResearch.WordTrace tailWord_1959618 prefixEnd_1959618 223605762933870937613975 := by
  unfold tailWord_1959618
  simp only [CollatzResearch.WordTrace]
  refine ⟨17868285053661534238645877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47648760143097424636389005 17868285053661534238645877)
  ·
    refine ⟨1675151723780768834873051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17868285053661534238645877 1675151723780768834873051)
    ·
      refine ⟨2512727585671153252309577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1675151723780768834873051 2512727585671153252309577)
      ·
        refine ⟨1884545689253364939232183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2512727585671153252309577 1884545689253364939232183)
        ·
          refine ⟨2826818533880047408848275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884545689253364939232183 2826818533880047408848275)
          ·
            refine ⟨4240227800820071113272413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826818533880047408848275 4240227800820071113272413)
            ·
              refine ⟨1590085425307526667477155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4240227800820071113272413 1590085425307526667477155)
              ·
                refine ⟨2385128137961290001215733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590085425307526667477155 2385128137961290001215733)
                ·
                  refine ⟨223605762933870937613975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2385128137961290001215733 223605762933870937613975)
                  ·
                    rfl

theorem cell22_1959618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1959618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959618 prefixEnd_1959618 := by exact prefixLift 1959618
  have htrace : WordTrace (prefixWord ++ tailWord_1959618) baseStart_1959618 baseEnd_1959618 := by
    simpa [prefixWord, tailWord_1959618, baseEnd_1959618] using wordTrace_append hprefix tailTrace_1959618
  have hstable : (prefixWord ++ tailWord_1959618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959618).length < 2 ^ (prefixWord ++ tailWord_1959618).sum := by decide
  have hdescent : baseEnd_1959618 < baseStart_1959618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959623 : List Nat := [1, 1, 4, 1, 1, 1, 4, 9]
def baseStart_1959623 : Nat := 118140960795 + 1959623 * 2 ^ 59
def prefixEnd_1959623 : Nat := 4983230072969 + 3 ^ 40 * 1959623 * 2
def baseEnd_1959623 : Nat := 74535444489310496274101

theorem tailTrace_1959623 : CollatzResearch.WordTrace tailWord_1959623 prefixEnd_1959623 74535444489310496274101 := by
  unfold tailWord_1959623
  simp only [CollatzResearch.WordTrace]
  refine ⟨71473322579628022808515523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47648881719752015205677015 71473322579628022808515523)
  ·
    refine ⟨107209983869442034212773285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71473322579628022808515523 107209983869442034212773285)
    ·
      refine ⟨20101871975520381414894991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107209983869442034212773285 20101871975520381414894991)
      ·
        refine ⟨30152807963280572122342487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20101871975520381414894991 30152807963280572122342487)
        ·
          refine ⟨45229211944920858183513731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30152807963280572122342487 45229211944920858183513731)
          ·
            refine ⟨67843817917381287275270597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45229211944920858183513731 67843817917381287275270597)
            ·
              refine ⟨12720715859508991364113237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67843817917381287275270597 12720715859508991364113237)
              ·
                refine ⟨74535444489310496274101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12720715859508991364113237 74535444489310496274101)
                ·
                  rfl

theorem cell22_1959623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 9].length) (baseStart_1959623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959623 prefixEnd_1959623 := by exact prefixLift 1959623
  have htrace : WordTrace (prefixWord ++ tailWord_1959623) baseStart_1959623 baseEnd_1959623 := by
    simpa [prefixWord, tailWord_1959623, baseEnd_1959623] using wordTrace_append hprefix tailTrace_1959623
  have hstable : (prefixWord ++ tailWord_1959623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959623).length < 2 ^ (prefixWord ++ tailWord_1959623).sum := by decide
  have hdescent : baseEnd_1959623 < baseStart_1959623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959678 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1959678 : Nat := 118140960795 + 1959678 * 2 ^ 59
def prefixEnd_1959678 : Nat := 4983230072969 + 3 ^ 40 * 1959678 * 2
def baseEnd_1959678 : Nat := 670837828027792656341741

theorem tailTrace_1959678 : CollatzResearch.WordTrace tailWord_1959678 prefixEnd_1959678 670837828027792656341741 := by
  unfold tailWord_1959678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8934416074303595900220961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47650219062952511467845125 8934416074303595900220961)
  ·
    refine ⟨6700812055727696925165721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8934416074303595900220961 6700812055727696925165721)
    ·
      refine ⟨5025609041795772693874291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6700812055727696925165721 5025609041795772693874291)
      ·
        refine ⟨7538413562693659040811437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025609041795772693874291 7538413562693659040811437)
        ·
          refine ⟨2826905086010122140304289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7538413562693659040811437 2826905086010122140304289)
          ·
            refine ⟨2120178814507591605228217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2826905086010122140304289 2120178814507591605228217)
            ·
              refine ⟨1590134110880693703921163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120178814507591605228217 1590134110880693703921163)
              ·
                refine ⟨2385201166321040555881745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590134110880693703921163 2385201166321040555881745)
                ·
                  refine ⟨1788900874740780416911309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2385201166321040555881745 1788900874740780416911309)
                  ·
                    refine ⟨670837828027792656341741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1788900874740780416911309 670837828027792656341741)
                    ·
                      rfl

theorem cell22_1959678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1959678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959678 prefixEnd_1959678 := by exact prefixLift 1959678
  have htrace : WordTrace (prefixWord ++ tailWord_1959678) baseStart_1959678 baseEnd_1959678 := by
    simpa [prefixWord, tailWord_1959678, baseEnd_1959678] using wordTrace_append hprefix tailTrace_1959678
  have hstable : (prefixWord ++ tailWord_1959678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959678).length < 2 ^ (prefixWord ++ tailWord_1959678).sum := by decide
  have hdescent : baseEnd_1959678 < baseStart_1959678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959734 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1959734 : Nat := 118140960795 + 1959734 * 2 ^ 59
def prefixEnd_1959734 : Nat := 4983230072969 + 3 ^ 40 * 1959734 * 2
def baseEnd_1959734 : Nat := 670856997972227176941569

theorem tailTrace_1959734 : CollatzResearch.WordTrace tailWord_1959734 prefixEnd_1959734 670856997972227176941569 := by
  unfold tailWord_1959734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467335692639118047862891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47651580721483925843870837 4467335692639118047862891)
  ·
    refine ⟨6701003538958677071794337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4467335692639118047862891 6701003538958677071794337)
    ·
      refine ⟨5025752654219007803845753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6701003538958677071794337 5025752654219007803845753)
      ·
        refine ⟨3769314490664255852884315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5025752654219007803845753 3769314490664255852884315)
        ·
          refine ⟨5653971735996383779326473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3769314490664255852884315 5653971735996383779326473)
          ·
            refine ⟨4240478801997287834494855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5653971735996383779326473 4240478801997287834494855)
            ·
              refine ⟨6360718202995931751742283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240478801997287834494855 6360718202995931751742283)
              ·
                refine ⟨9541077304493897627613425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360718202995931751742283 9541077304493897627613425)
                ·
                  refine ⟨7155807978370423220710069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9541077304493897627613425 7155807978370423220710069)
                  ·
                    refine ⟨670856997972227176941569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7155807978370423220710069 670856997972227176941569)
                    ·
                      rfl

theorem cell22_1959734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1959734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959734 prefixEnd_1959734 := by exact prefixLift 1959734
  have htrace : WordTrace (prefixWord ++ tailWord_1959734) baseStart_1959734 baseEnd_1959734 := by
    simpa [prefixWord, tailWord_1959734, baseEnd_1959734] using wordTrace_append hprefix tailTrace_1959734
  have hstable : (prefixWord ++ tailWord_1959734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959734).length < 2 ^ (prefixWord ++ tailWord_1959734).sum := by decide
  have hdescent : baseEnd_1959734 < baseStart_1959734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959762 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1959762 : Nat := 118140960795 + 1959762 * 2 ^ 59
def prefixEnd_1959762 : Nat := 4983230072969 + 3 ^ 40 * 1959762 * 2
def baseEnd_1959762 : Nat := 670866582944444437241483

theorem tailTrace_1959762 : CollatzResearch.WordTrace tailWord_1959762 prefixEnd_1959762 670866582944444437241483 := by
  unfold tailWord_1959762
  simp only [CollatzResearch.WordTrace]
  refine ⟨17869598081531112386956385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47652261550749633031883693 17869598081531112386956385)
  ·
    refine ⟨13402198561148334290217289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17869598081531112386956385 13402198561148334290217289)
    ·
      refine ⟨10051648920861250717662967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13402198561148334290217289 10051648920861250717662967)
      ·
        refine ⟨15077473381291876076494451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10051648920861250717662967 15077473381291876076494451)
        ·
          refine ⟨22616210071937814114741677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15077473381291876076494451 22616210071937814114741677)
          ·
            refine ⟨8481078776976680293028129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22616210071937814114741677 8481078776976680293028129)
            ·
              refine ⟨6360809082732510219771097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8481078776976680293028129 6360809082732510219771097)
              ·
                refine ⟨4770606812049382664828323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6360809082732510219771097 4770606812049382664828323)
                ·
                  refine ⟨7155910218074073997242485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770606812049382664828323 7155910218074073997242485)
                  ·
                    refine ⟨670866582944444437241483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7155910218074073997242485 670866582944444437241483)
                    ·
                      rfl

theorem cell22_1959762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1959762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959762 prefixEnd_1959762 := by exact prefixLift 1959762
  have htrace : WordTrace (prefixWord ++ tailWord_1959762) baseStart_1959762 baseEnd_1959762 := by
    simpa [prefixWord, tailWord_1959762, baseEnd_1959762] using wordTrace_append hprefix tailTrace_1959762
  have hstable : (prefixWord ++ tailWord_1959762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959762).length < 2 ^ (prefixWord ++ tailWord_1959762).sum := by decide
  have hdescent : baseEnd_1959762 < baseStart_1959762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959764 : List Nat := [2, 4, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1959764 : Nat := 118140960795 + 1959764 * 2 ^ 59
def prefixEnd_1959764 : Nat := 4983230072969 + 3 ^ 40 * 1959764 * 2
def baseEnd_1959764 : Nat := 223622422528439032897159

theorem tailTrace_1959764 : CollatzResearch.WordTrace tailWord_1959764 prefixEnd_1959764 223622422528439032897159 := by
  unfold tailWord_1959764
  simp only [CollatzResearch.WordTrace]
  refine ⟨35739232636058601944699173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47652310181411469259598897 35739232636058601944699173)
  ·
    refine ⟨6701106119260987864631095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35739232636058601944699173 6701106119260987864631095)
    ·
      refine ⟨10051659178891481796946643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6701106119260987864631095 10051659178891481796946643)
      ·
        refine ⟨15077488768337222695419965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10051659178891481796946643 15077488768337222695419965)
        ·
          refine ⟨5654058288126458510782487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15077488768337222695419965 5654058288126458510782487)
          ·
            refine ⟨8481087432189687766173731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5654058288126458510782487 8481087432189687766173731)
            ·
              refine ⟨12721631148284531649260597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8481087432189687766173731 12721631148284531649260597)
              ·
                refine ⟨1192652920151674842118181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12721631148284531649260597 1192652920151674842118181)
                ·
                  refine ⟨223622422528439032897159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192652920151674842118181 223622422528439032897159)
                  ·
                    rfl

theorem cell22_1959764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1959764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959764 prefixEnd_1959764 := by exact prefixLift 1959764
  have htrace : WordTrace (prefixWord ++ tailWord_1959764) baseStart_1959764 baseEnd_1959764 := by
    simpa [prefixWord, tailWord_1959764, baseEnd_1959764] using wordTrace_append hprefix tailTrace_1959764
  have hstable : (prefixWord ++ tailWord_1959764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959764).length < 2 ^ (prefixWord ++ tailWord_1959764).sum := by decide
  have hdescent : baseEnd_1959764 < baseStart_1959764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959775 : List Nat := [1, 1, 2, 3, 1, 5, 9]
def baseStart_1959775 : Nat := 118140960795 + 1959775 * 2 ^ 59
def prefixEnd_1959775 : Nat := 4983230072969 + 3 ^ 40 * 1959775 * 2
def baseEnd_1959775 : Nat := 24847075300374693950609

theorem tailTrace_1959775 : CollatzResearch.WordTrace tailWord_1959775 prefixEnd_1959775 24847075300374693950609 := by
  unfold tailWord_1959775
  simp only [CollatzResearch.WordTrace]
  refine ⟨71478866475077352768048779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47652577650051568512032519 71478866475077352768048779)
  ·
    refine ⟨107218299712616029152073169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71478866475077352768048779 107218299712616029152073169)
    ·
      refine ⟨80413724784462021864054877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107218299712616029152073169 80413724784462021864054877)
      ·
        refine ⟨30155146794173258199020579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80413724784462021864054877 30155146794173258199020579)
        ·
          refine ⟨45232720191259887298530869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30155146794173258199020579 45232720191259887298530869)
          ·
            refine ⟨4240567517930614434237269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45232720191259887298530869 4240567517930614434237269)
            ·
              refine ⟨24847075300374693950609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4240567517930614434237269 24847075300374693950609)
              ·
                rfl

theorem cell22_1959775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 9].length) (baseStart_1959775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959775 prefixEnd_1959775 := by exact prefixLift 1959775
  have htrace : WordTrace (prefixWord ++ tailWord_1959775) baseStart_1959775 baseEnd_1959775 := by
    simpa [prefixWord, tailWord_1959775, baseEnd_1959775] using wordTrace_append hprefix tailTrace_1959775
  have hstable : (prefixWord ++ tailWord_1959775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959775).length < 2 ^ (prefixWord ++ tailWord_1959775).sum := by decide
  have hdescent : baseEnd_1959775 < baseStart_1959775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959779 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 4, 3]
def baseStart_1959779 : Nat := 118140960795 + 1959779 * 2 ^ 59
def prefixEnd_1959779 : Nat := 4983230072969 + 3 ^ 40 * 1959779 * 2
def baseEnd_1959779 : Nat := 670872402391862059566431

theorem tailTrace_1959779 : CollatzResearch.WordTrace tailWord_1959779 prefixEnd_1959779 670872402391862059566431 := by
  unfold tailWord_1959779
  simp only [CollatzResearch.WordTrace]
  refine ⟨71479012367062861451194391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47652674911375240967462927 71479012367062861451194391)
  ·
    refine ⟨107218518550594292176791587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71479012367062861451194391 107218518550594292176791587)
    ·
      refine ⟨160827777825891438265187381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107218518550594292176791587 160827777825891438265187381)
      ·
        refine ⟨15077604171177322337361317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160827777825891438265187381 15077604171177322337361317)
        ·
          refine ⟨2827050782095747938255247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15077604171177322337361317 2827050782095747938255247)
          ·
            refine ⟨4240576173143621907382871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827050782095747938255247 4240576173143621907382871)
            ·
              refine ⟨6360864259715432861074307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240576173143621907382871 6360864259715432861074307)
              ·
                refine ⟨9541296389573149291611461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360864259715432861074307 9541296389573149291611461)
                ·
                  refine ⟨1788993073044965492177149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9541296389573149291611461 1788993073044965492177149)
                  ·
                    refine ⟨670872402391862059566431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1788993073044965492177149 670872402391862059566431)
                    ·
                      rfl

theorem cell22_1959779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 3].length) (baseStart_1959779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959779 prefixEnd_1959779 := by exact prefixLift 1959779
  have htrace : WordTrace (prefixWord ++ tailWord_1959779) baseStart_1959779 baseEnd_1959779 := by
    simpa [prefixWord, tailWord_1959779, baseEnd_1959779] using wordTrace_append hprefix tailTrace_1959779
  have hstable : (prefixWord ++ tailWord_1959779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959779).length < 2 ^ (prefixWord ++ tailWord_1959779).sum := by decide
  have hdescent : baseEnd_1959779 < baseStart_1959779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959809 : List Nat := [1, 2, 4, 4, 1, 1, 1, 8]
def baseStart_1959809 : Nat := 118140960795 + 1959809 * 2 ^ 59
def prefixEnd_1959809 : Nat := 4983230072969 + 3 ^ 40 * 1959809 * 2
def baseEnd_1959809 : Nat := 74542519111661331257371

theorem tailTrace_1959809 : CollatzResearch.WordTrace tailWord_1959809 prefixEnd_1959809 74542519111661331257371 := by
  unfold tailWord_1959809
  simp only [CollatzResearch.WordTrace]
  refine ⟨71480106556954176574786481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47653404371302784383190987 71480106556954176574786481)
  ·
    refine ⟨53610079917715632431089861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71480106556954176574786481 53610079917715632431089861)
    ·
      refine ⟨10051889984571681080829349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53610079917715632431089861 10051889984571681080829349)
      ·
        refine ⟨1884729372107190202655503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10051889984571681080829349 1884729372107190202655503)
        ·
          refine ⟨2827094058160785303983255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884729372107190202655503 2827094058160785303983255)
          ·
            refine ⟨4240641087241177955974883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827094058160785303983255 4240641087241177955974883)
            ·
              refine ⟨6360961630861766933962325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240641087241177955974883 6360961630861766933962325)
              ·
                refine ⟨74542519111661331257371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6360961630861766933962325 74542519111661331257371)
                ·
                  rfl

theorem cell22_1959809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 8].length) (baseStart_1959809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959809 prefixEnd_1959809 := by exact prefixLift 1959809
  have htrace : WordTrace (prefixWord ++ tailWord_1959809) baseStart_1959809 baseEnd_1959809 := by
    simpa [prefixWord, tailWord_1959809, baseEnd_1959809] using wordTrace_append hprefix tailTrace_1959809
  have hstable : (prefixWord ++ tailWord_1959809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959809).length < 2 ^ (prefixWord ++ tailWord_1959809).sum := by decide
  have hdescent : baseEnd_1959809 < baseStart_1959809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959837 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 7]
def baseStart_1959837 : Nat := 118140960795 + 1959837 * 2 ^ 59
def prefixEnd_1959837 : Nat := 4983230072969 + 3 ^ 40 * 1959837 * 2
def baseEnd_1959837 : Nat := 223630752325723080538751

theorem tailTrace_1959837 : CollatzResearch.WordTrace tailWord_1959837 prefixEnd_1959837 223630752325723080538751 := by
  unfold tailWord_1959837
  simp only [CollatzResearch.WordTrace]
  refine ⟨71481127800852737356805765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47654085200568491571203843 71481127800852737356805765)
  ·
    refine ⟨13402711462659888254401081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71481127800852737356805765 13402711462659888254401081)
    ·
      refine ⟨10052033596994916190800811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13402711462659888254401081 10052033596994916190800811)
      ·
        refine ⟨15078050395492374286201217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10052033596994916190800811 15078050395492374286201217)
        ·
          refine ⟨11308537796619280714650913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15078050395492374286201217 11308537796619280714650913)
          ·
            refine ⟨8481403347464460535988185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11308537796619280714650913 8481403347464460535988185)
            ·
              refine ⟨6361052510598345401991139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8481403347464460535988185 6361052510598345401991139)
              ·
                refine ⟨9541578765897518102986709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361052510598345401991139 9541578765897518102986709)
                ·
                  refine ⟨223630752325723080538751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9541578765897518102986709 223630752325723080538751)
                  ·
                    rfl

theorem cell22_1959837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_1959837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959837 prefixEnd_1959837 := by exact prefixLift 1959837
  have htrace : WordTrace (prefixWord ++ tailWord_1959837) baseStart_1959837 baseEnd_1959837 := by
    simpa [prefixWord, tailWord_1959837, baseEnd_1959837] using wordTrace_append hprefix tailTrace_1959837
  have hstable : (prefixWord ++ tailWord_1959837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959837).length < 2 ^ (prefixWord ++ tailWord_1959837).sum := by decide
  have hdescent : baseEnd_1959837 < baseStart_1959837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959912 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_1959912 : Nat := 118140960795 + 1959912 * 2 ^ 59
def prefixEnd_1959912 : Nat := 4983230072969 + 3 ^ 40 * 1959912 * 2
def baseEnd_1959912 : Nat := 670917931009894045991023

theorem tailTrace_1959912 : CollatzResearch.WordTrace tailWord_1959912 prefixEnd_1959912 670917931009894045991023 := by
  unfold tailWord_1959912
  simp only [CollatzResearch.WordTrace]
  refine ⟨35741931637790512582892995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47655908850387350110523993 35741931637790512582892995)
  ·
    refine ⟨53612897456685768874339493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35741931637790512582892995 53612897456685768874339493)
    ·
      refine ⟨10052418273128581663938655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53612897456685768874339493 10052418273128581663938655)
      ·
        refine ⟨15078627409692872495907983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10052418273128581663938655 15078627409692872495907983)
        ·
          refine ⟨22617941114539308743861975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15078627409692872495907983 22617941114539308743861975)
          ·
            refine ⟨33926911671808963115792963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22617941114539308743861975 33926911671808963115792963)
            ·
              refine ⟨50890367507713444673689445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33926911671808963115792963 50890367507713444673689445)
              ·
                refine ⟨9541943907696270876316771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50890367507713444673689445 9541943907696270876316771)
                ·
                  refine ⟨14312915861544406314475157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9541943907696270876316771 14312915861544406314475157)
                  ·
                    refine ⟨670917931009894045991023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14312915861544406314475157 670917931009894045991023)
                    ·
                      rfl

theorem cell22_1959912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_1959912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959912 prefixEnd_1959912 := by exact prefixLift 1959912
  have htrace : WordTrace (prefixWord ++ tailWord_1959912) baseStart_1959912 baseEnd_1959912 := by
    simpa [prefixWord, tailWord_1959912, baseEnd_1959912] using wordTrace_append hprefix tailTrace_1959912
  have hstable : (prefixWord ++ tailWord_1959912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959912).length < 2 ^ (prefixWord ++ tailWord_1959912).sum := by decide
  have hdescent : baseEnd_1959912 < baseStart_1959912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959914 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1959914 : Nat := 118140960795 + 1959914 * 2 ^ 59
def prefixEnd_1959914 : Nat := 4983230072969 + 3 ^ 40 * 1959914 * 2
def baseEnd_1959914 : Nat := 670918615650766707441017

theorem tailTrace_1959914 : CollatzResearch.WordTrace tailWord_1959914 prefixEnd_1959914 670918615650766707441017 := by
  unfold tailWord_1959914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17870984055393444876839699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47655957481049186338239197 17870984055393444876839699)
  ·
    refine ⟨26806476083090167315259549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17870984055393444876839699 26806476083090167315259549)
    ·
      refine ⟨10052428531158812743222331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26806476083090167315259549 10052428531158812743222331)
      ·
        refine ⟨15078642796738219114833497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10052428531158812743222331 15078642796738219114833497)
        ·
          refine ⟨11308982097553664336125123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15078642796738219114833497 11308982097553664336125123)
          ·
            refine ⟨16963473146330496504187685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11308982097553664336125123 16963473146330496504187685)
            ·
              refine ⟨3180651214936968094535191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16963473146330496504187685 3180651214936968094535191)
              ·
                refine ⟨4770976822405452141802787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180651214936968094535191 4770976822405452141802787)
                ·
                  refine ⟨7156465233608178212704181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770976822405452141802787 7156465233608178212704181)
                  ·
                    refine ⟨670918615650766707441017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7156465233608178212704181 670918615650766707441017)
                    ·
                      rfl

theorem cell22_1959914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1959914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959914 prefixEnd_1959914 := by exact prefixLift 1959914
  have htrace : WordTrace (prefixWord ++ tailWord_1959914) baseStart_1959914 baseEnd_1959914 := by
    simpa [prefixWord, tailWord_1959914, baseEnd_1959914] using wordTrace_append hprefix tailTrace_1959914
  have hstable : (prefixWord ++ tailWord_1959914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959914).length < 2 ^ (prefixWord ++ tailWord_1959914).sum := by decide
  have hdescent : baseEnd_1959914 < baseStart_1959914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959929 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 2, 4]
def baseStart_1959929 : Nat := 118140960795 + 1959929 * 2 ^ 59
def prefixEnd_1959929 : Nat := 4983230072969 + 3 ^ 40 * 1959929 * 2
def baseEnd_1959929 : Nat := 670923750457311668315971

theorem tailTrace_1959929 : CollatzResearch.WordTrace tailWord_1959929 prefixEnd_1959929 670923750457311668315971 := by
  unfold tailWord_1959929
  simp only [CollatzResearch.WordTrace]
  refine ⟨71484483316519437069154841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47656322211012958046103227 71484483316519437069154841)
  ·
    refine ⟨53613362487389577801866131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71484483316519437069154841 53613362487389577801866131)
    ·
      refine ⟨80420043731084366702799197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53613362487389577801866131 80420043731084366702799197)
      ·
        refine ⟨30157516399156637513549699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80420043731084366702799197 30157516399156637513549699)
        ·
          refine ⟨45236274598734956270324549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30157516399156637513549699 45236274598734956270324549)
          ·
            refine ⟨8481801487262804300685853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45236274598734956270324549 8481801487262804300685853)
            ·
              refine ⟨3180675557723551612757195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8481801487262804300685853 3180675557723551612757195)
              ·
                refine ⟨4771013336585327419135793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180675557723551612757195 4771013336585327419135793)
                ·
                  refine ⟨3578260002438995564351845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4771013336585327419135793 3578260002438995564351845)
                  ·
                    refine ⟨670923750457311668315971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3578260002438995564351845 670923750457311668315971)
                    ·
                      rfl

theorem cell22_1959929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_1959929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959929 prefixEnd_1959929 := by exact prefixLift 1959929
  have htrace : WordTrace (prefixWord ++ tailWord_1959929) baseStart_1959929 baseEnd_1959929 := by
    simpa [prefixWord, tailWord_1959929, baseEnd_1959929] using wordTrace_append hprefix tailTrace_1959929
  have hstable : (prefixWord ++ tailWord_1959929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959929).length < 2 ^ (prefixWord ++ tailWord_1959929).sum := by decide
  have hdescent : baseEnd_1959929 < baseStart_1959929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959987 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 1, 7]
def baseStart_1959987 : Nat := 118140960795 + 1959987 * 2 ^ 59
def prefixEnd_1959987 : Nat := 4983230072969 + 3 ^ 40 * 1959987 * 2
def baseEnd_1959987 : Nat := 670943605042618850365793

theorem tailTrace_1959987 : CollatzResearch.WordTrace tailWord_1959987 prefixEnd_1959987 670943605042618850365793 := by
  unfold tailWord_1959987
  simp only [CollatzResearch.WordTrace]
  refine ⟨71486598750309312974766215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47657732500206208649844143 71486598750309312974766215)
  ·
    refine ⟨107229898125463969462149323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71486598750309312974766215 107229898125463969462149323)
    ·
      refine ⟨160844847188195954193223985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107229898125463969462149323 160844847188195954193223985)
      ·
        refine ⟨120633635391146965644917989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160844847188195954193223985 120633635391146965644917989)
        ·
          refine ⟨22618806635840056058422123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120633635391146965644917989 22618806635840056058422123)
          ·
            refine ⟨33928209953760084087633185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22618806635840056058422123 33928209953760084087633185)
            ·
              refine ⟨25446157465320063065724889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33928209953760084087633185 25446157465320063065724889)
              ·
                refine ⟨19084618098990047299293667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25446157465320063065724889 19084618098990047299293667)
                ·
                  refine ⟨28626927148485070948940501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19084618098990047299293667 28626927148485070948940501)
                  ·
                    refine ⟨670943605042618850365793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28626927148485070948940501 670943605042618850365793)
                    ·
                      rfl

theorem cell22_1959987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_1959987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1959987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1959987 prefixEnd_1959987 := by exact prefixLift 1959987
  have htrace : WordTrace (prefixWord ++ tailWord_1959987) baseStart_1959987 baseEnd_1959987 := by
    simpa [prefixWord, tailWord_1959987, baseEnd_1959987] using wordTrace_append hprefix tailTrace_1959987
  have hstable : (prefixWord ++ tailWord_1959987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959987).length < 2 ^ (prefixWord ++ tailWord_1959987).sum := by decide
  have hdescent : baseEnd_1959987 < baseStart_1959987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960006 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1960006 : Nat := 118140960795 + 1960006 * 2 ^ 59
def prefixEnd_1960006 : Nat := 4983230072969 + 3 ^ 40 * 1960006 * 2
def baseEnd_1960006 : Nat := 223650036376969711380245

theorem tailTrace_1960006 : CollatzResearch.WordTrace tailWord_1960006 prefixEnd_1960006 223650036376969711380245 := by
  unfold tailWord_1960006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2233977866788764975615871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47658194491493652813138581 2233977866788764975615871)
  ·
    refine ⟨3350966800183147463423807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2233977866788764975615871 3350966800183147463423807)
    ·
      refine ⟨5026450200274721195135711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350966800183147463423807 5026450200274721195135711)
      ·
        refine ⟨7539675300412081792703567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5026450200274721195135711 7539675300412081792703567)
        ·
          refine ⟨11309512950618122689055351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7539675300412081792703567 11309512950618122689055351)
          ·
            refine ⟨16964269425927184033583027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11309512950618122689055351 16964269425927184033583027)
            ·
              refine ⟨25446404138890776050374541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16964269425927184033583027 25446404138890776050374541)
              ·
                refine ⟨9542401552084041018890453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25446404138890776050374541 9542401552084041018890453)
                ·
                  refine ⟨223650036376969711380245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9542401552084041018890453 223650036376969711380245)
                  ·
                    rfl

theorem cell22_1960006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1960006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960006 prefixEnd_1960006 := by exact prefixLift 1960006
  have htrace : WordTrace (prefixWord ++ tailWord_1960006) baseStart_1960006 baseEnd_1960006 := by
    simpa [prefixWord, tailWord_1960006, baseEnd_1960006] using wordTrace_append hprefix tailTrace_1960006
  have hstable : (prefixWord ++ tailWord_1960006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960006).length < 2 ^ (prefixWord ++ tailWord_1960006).sum := by decide
  have hdescent : baseEnd_1960006 < baseStart_1960006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960036 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_1960036 : Nat := 118140960795 + 1960036 * 2 ^ 59
def prefixEnd_1960036 : Nat := 4983230072969 + 3 ^ 40 * 1960036 * 2
def baseEnd_1960036 : Nat := 670960378743999055890643

theorem tailTrace_1960036 : CollatzResearch.WordTrace tailWord_1960036 prefixEnd_1960036 670960378743999055890643 := by
  unfold tailWord_1960036
  simp only [CollatzResearch.WordTrace]
  refine ⟨35744192963565897171649981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47658923951421196228866641 35744192963565897171649981)
  ·
    refine ⟨13404072361337211439368743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35744192963565897171649981 13404072361337211439368743)
    ·
      refine ⟨20106108542005817159053115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13404072361337211439368743 20106108542005817159053115)
      ·
        refine ⟨30159162813008725738579673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20106108542005817159053115 30159162813008725738579673)
        ·
          refine ⟨22619372109756544303934755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30159162813008725738579673 22619372109756544303934755)
          ·
            refine ⟨33929058164634816455902133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22619372109756544303934755 33929058164634816455902133)
            ·
              refine ⟨3180849202934514042740825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33929058164634816455902133 3180849202934514042740825)
              ·
                refine ⟨2385636902200885532055619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3180849202934514042740825 2385636902200885532055619)
                ·
                  refine ⟨3578455353301328298083429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385636902200885532055619 3578455353301328298083429)
                  ·
                    refine ⟨670960378743999055890643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3578455353301328298083429 670960378743999055890643)
                    ·
                      rfl

theorem cell22_1960036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_1960036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960036 prefixEnd_1960036 := by exact prefixLift 1960036
  have htrace : WordTrace (prefixWord ++ tailWord_1960036) baseStart_1960036 baseEnd_1960036 := by
    simpa [prefixWord, tailWord_1960036, baseEnd_1960036] using wordTrace_append hprefix tailTrace_1960036
  have hstable : (prefixWord ++ tailWord_1960036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960036).length < 2 ^ (prefixWord ++ tailWord_1960036).sum := by decide
  have hdescent : baseEnd_1960036 < baseStart_1960036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960049 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_1960049 : Nat := 118140960795 + 1960049 * 2 ^ 59
def prefixEnd_1960049 : Nat := 4983230072969 + 3 ^ 40 * 1960049 * 2
def baseEnd_1960049 : Nat := 670964828909671355315603

theorem tailTrace_1960049 : CollatzResearch.WordTrace tailWord_1960049 prefixEnd_1960049 670964828909671355315603 := by
  unfold tailWord_1960049
  simp only [CollatzResearch.WordTrace]
  refine ⟨71488860076084697563523201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47659240050723131709015467 71488860076084697563523201)
  ·
    refine ⟨53616645057063523172642401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71488860076084697563523201 53616645057063523172642401)
    ·
      refine ⟨40212483792797642379481801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53616645057063523172642401 40212483792797642379481801)
      ·
        refine ⟨30159362844598231784611351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40212483792797642379481801 30159362844598231784611351)
        ·
          refine ⟨45239044266897347676917027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30159362844598231784611351 45239044266897347676917027)
          ·
            refine ⟨67858566400346021515375541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45239044266897347676917027 67858566400346021515375541)
            ·
              refine ⟨6361740600032439517066457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67858566400346021515375541 6361740600032439517066457)
              ·
                refine ⟨4771305450024329637799843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6361740600032439517066457 4771305450024329637799843)
                ·
                  refine ⟨7156958175036494456699765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771305450024329637799843 7156958175036494456699765)
                  ·
                    refine ⟨670964828909671355315603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7156958175036494456699765 670964828909671355315603)
                    ·
                      rfl

theorem cell22_1960049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_1960049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960049 prefixEnd_1960049 := by exact prefixLift 1960049
  have htrace : WordTrace (prefixWord ++ tailWord_1960049) baseStart_1960049 baseEnd_1960049 := by
    simpa [prefixWord, tailWord_1960049, baseEnd_1960049] using wordTrace_append hprefix tailTrace_1960049
  have hstable : (prefixWord ++ tailWord_1960049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960049).length < 2 ^ (prefixWord ++ tailWord_1960049).sum := by decide
  have hdescent : baseEnd_1960049 < baseStart_1960049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960096 : List Nat := [2, 1, 1, 4, 2, 3, 3, 6]
def baseStart_1960096 : Nat := 118140960795 + 1960096 * 2 ^ 59
def prefixEnd_1960096 : Nat := 4983230072969 + 3 ^ 40 * 1960096 * 2
def baseEnd_1960096 : Nat := 74553435330019877710051

theorem tailTrace_1960096 : CollatzResearch.WordTrace tailWord_1960096 prefixEnd_1960096 74553435330019877710051 := by
  unfold tailWord_1960096
  simp only [CollatzResearch.WordTrace]
  refine ⟨35745287153457212295242071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47660382871276283060322761 35745287153457212295242071)
  ·
    refine ⟨53617930730185818442863107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35745287153457212295242071 53617930730185818442863107)
    ·
      refine ⟨80426896095278727664294661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53617930730185818442863107 80426896095278727664294661)
      ·
        refine ⟨15080043017864761437055249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80426896095278727664294661 15080043017864761437055249)
        ·
          refine ⟨11310032263398571077791437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15080043017864761437055249 11310032263398571077791437)
          ·
            refine ⟨4241262098774464154171789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11310032263398571077791437 4241262098774464154171789)
            ·
              refine ⟨1590473287040424057814421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4241262098774464154171789 1590473287040424057814421)
              ·
                refine ⟨74553435330019877710051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1590473287040424057814421 74553435330019877710051)
                ·
                  rfl

theorem cell22_1960096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 6].length) (baseStart_1960096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960096 prefixEnd_1960096 := by exact prefixLift 1960096
  have htrace : WordTrace (prefixWord ++ tailWord_1960096) baseStart_1960096 baseEnd_1960096 := by
    simpa [prefixWord, tailWord_1960096, baseEnd_1960096] using wordTrace_append hprefix tailTrace_1960096
  have hstable : (prefixWord ++ tailWord_1960096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960096).length < 2 ^ (prefixWord ++ tailWord_1960096).sum := by decide
  have hdescent : baseEnd_1960096 < baseStart_1960096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960098 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1960098 : Nat := 118140960795 + 1960098 * 2 ^ 59
def prefixEnd_1960098 : Nat := 4983230072969 + 3 ^ 40 * 1960098 * 2
def baseEnd_1960098 : Nat := 670981602611051560840453

theorem tailTrace_1960098 : CollatzResearch.WordTrace tailWord_1960098 prefixEnd_1960098 670981602611051560840453 := by
  unfold tailWord_1960098
  simp only [CollatzResearch.WordTrace]
  refine ⟨17872661813226794733014237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47660431501938119288037965 17872661813226794733014237)
  ·
    refine ⟨6702248179960048024880339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17872661813226794733014237 6702248179960048024880339)
    ·
      refine ⟨10053372269940072037320509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702248179960048024880339 10053372269940072037320509)
      ·
        refine ⟨3770014601227527013995191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10053372269940072037320509 3770014601227527013995191)
        ·
          refine ⟨5655021901841290520992787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770014601227527013995191 5655021901841290520992787)
          ·
            refine ⟨8482532852761935781489181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5655021901841290520992787 8482532852761935781489181)
            ·
              refine ⟨3180949819785725918058443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8482532852761935781489181 3180949819785725918058443)
              ·
                refine ⟨4771424729678588877087665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180949819785725918058443 4771424729678588877087665)
                ·
                  refine ⟨3578568547258941657815749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4771424729678588877087665 3578568547258941657815749)
                  ·
                    refine ⟨670981602611051560840453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3578568547258941657815749 670981602611051560840453)
                    ·
                      rfl

theorem cell22_1960098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1960098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960098 prefixEnd_1960098 := by exact prefixLift 1960098
  have htrace : WordTrace (prefixWord ++ tailWord_1960098) baseStart_1960098 baseEnd_1960098 := by
    simpa [prefixWord, tailWord_1960098, baseEnd_1960098] using wordTrace_append hprefix tailTrace_1960098
  have hstable : (prefixWord ++ tailWord_1960098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960098).length < 2 ^ (prefixWord ++ tailWord_1960098).sum := by decide
  have hdescent : baseEnd_1960098 < baseStart_1960098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960117 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1960117 : Nat := 118140960795 + 1960117 * 2 ^ 59
def prefixEnd_1960117 : Nat := 4983230072969 + 3 ^ 40 * 1960117 * 2
def baseEnd_1960117 : Nat := 670988106699341844615395

theorem tailTrace_1960117 : CollatzResearch.WordTrace tailWord_1960117 prefixEnd_1960117 670988106699341844615395 := by
  unfold tailWord_1960117
  simp only [CollatzResearch.WordTrace]
  refine ⟨71491340239838345176998605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47660893493225563451332403 71491340239838345176998605)
  ·
    refine ⟨26809252589939379441374477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71491340239838345176998605 26809252589939379441374477)
    ·
      refine ⟨10053469721227267290515429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26809252589939379441374477 10053469721227267290515429)
      ·
        refine ⟨1885025572730112616971643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10053469721227267290515429 1885025572730112616971643)
        ·
          refine ⟨2827538359095168925457465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885025572730112616971643 2827538359095168925457465)
          ·
            refine ⟨2120653769321376694093099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2827538359095168925457465 2120653769321376694093099)
            ·
              refine ⟨3180980653982065041139649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120653769321376694093099 3180980653982065041139649)
              ·
                refine ⟨2385735490486548780854737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3180980653982065041139649 2385735490486548780854737)
                ·
                  refine ⟨1789301617864911585641053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2385735490486548780854737 1789301617864911585641053)
                  ·
                    refine ⟨670988106699341844615395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789301617864911585641053 670988106699341844615395)
                    ·
                      rfl

theorem cell22_1960117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1960117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960117 prefixEnd_1960117 := by exact prefixLift 1960117
  have htrace : WordTrace (prefixWord ++ tailWord_1960117) baseStart_1960117 baseEnd_1960117 := by
    simpa [prefixWord, tailWord_1960117, baseEnd_1960117] using wordTrace_append hprefix tailTrace_1960117
  have hstable : (prefixWord ++ tailWord_1960117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960117).length < 2 ^ (prefixWord ++ tailWord_1960117).sum := by decide
  have hdescent : baseEnd_1960117 < baseStart_1960117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960128 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 3, 3]
def baseStart_1960128 : Nat := 118140960795 + 1960128 * 2 ^ 59
def prefixEnd_1960128 : Nat := 4983230072969 + 3 ^ 40 * 1960128 * 2
def baseEnd_1960128 : Nat := 670991872224141482590361

theorem tailTrace_1960128 : CollatzResearch.WordTrace tailWord_1960128 prefixEnd_1960128 670991872224141482590361 := by
  unfold tailWord_1960128
  simp only [CollatzResearch.WordTrace]
  refine ⟨35745870721399247027824519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47661160961865662703766025 35745870721399247027824519)
  ·
    refine ⟨53618806082098870541736779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35745870721399247027824519 53618806082098870541736779)
    ·
      refine ⟨80428209123148305812605169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53618806082098870541736779 80428209123148305812605169)
      ·
        refine ⟨60321156842361229359453877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80428209123148305812605169 60321156842361229359453877)
        ·
          refine ⟨5655108453971365252448801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60321156842361229359453877 5655108453971365252448801)
          ·
            refine ⟨4241331340478523939336601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5655108453971365252448801 4241331340478523939336601)
            ·
              refine ⟨3180998505358892954502451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4241331340478523939336601 3180998505358892954502451)
              ·
                refine ⟨4771497758038339431753677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180998505358892954502451 4771497758038339431753677)
                ·
                  refine ⟨1789311659264377286907629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4771497758038339431753677 1789311659264377286907629)
                  ·
                    refine ⟨670991872224141482590361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789311659264377286907629 670991872224141482590361)
                    ·
                      rfl

theorem cell22_1960128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3, 3].length) (baseStart_1960128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960128 prefixEnd_1960128 := by exact prefixLift 1960128
  have htrace : WordTrace (prefixWord ++ tailWord_1960128) baseStart_1960128 baseEnd_1960128 := by
    simpa [prefixWord, tailWord_1960128, baseEnd_1960128] using wordTrace_append hprefix tailTrace_1960128
  have hstable : (prefixWord ++ tailWord_1960128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960128).length < 2 ^ (prefixWord ++ tailWord_1960128).sum := by decide
  have hdescent : baseEnd_1960128 < baseStart_1960128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960139 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 2, 5]
def baseStart_1960139 : Nat := 118140960795 + 1960139 * 2 ^ 59
def prefixEnd_1960139 : Nat := 4983230072969 + 3 ^ 40 * 1960139 * 2
def baseEnd_1960139 : Nat := 670995637748941120565327

theorem tailTrace_1960139 : CollatzResearch.WordTrace tailWord_1960139 prefixEnd_1960139 670995637748941120565327 := by
  unfold tailWord_1960139
  simp only [CollatzResearch.WordTrace]
  refine ⟨71492142645758642934299471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47661428430505761956199647 71492142645758642934299471)
  ·
    refine ⟨107238213968637964401449207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71492142645758642934299471 107238213968637964401449207)
    ·
      refine ⟨160857320952956946602173811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107238213968637964401449207 160857320952956946602173811)
      ·
        refine ⟨241285981429435419903260717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160857320952956946602173811 241285981429435419903260717)
        ·
          refine ⟨90482243036038282463722769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241285981429435419903260717 90482243036038282463722769)
          ·
            refine ⟨67861682277028711847792077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90482243036038282463722769 67861682277028711847792077)
            ·
              refine ⟨25448130853885766942922029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67861682277028711847792077 25448130853885766942922029)
              ·
                refine ⟨9543049070207162603595761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25448130853885766942922029 9543049070207162603595761)
                ·
                  refine ⟨7157286802655371952696821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9543049070207162603595761 7157286802655371952696821)
                  ·
                    refine ⟨670995637748941120565327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7157286802655371952696821 670995637748941120565327)
                    ·
                      rfl

theorem cell22_1960139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_1960139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960139 prefixEnd_1960139 := by exact prefixLift 1960139
  have htrace : WordTrace (prefixWord ++ tailWord_1960139) baseStart_1960139 baseEnd_1960139 := by
    simpa [prefixWord, tailWord_1960139, baseEnd_1960139] using wordTrace_append hprefix tailTrace_1960139
  have hstable : (prefixWord ++ tailWord_1960139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960139).length < 2 ^ (prefixWord ++ tailWord_1960139).sum := by decide
  have hdescent : baseEnd_1960139 < baseStart_1960139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960171 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 1, 4]
def baseStart_1960171 : Nat := 118140960795 + 1960171 * 2 ^ 59
def prefixEnd_1960171 : Nat := 4983230072969 + 3 ^ 40 * 1960171 * 2
def baseEnd_1960171 : Nat := 671006592002903703765229

theorem tailTrace_1960171 : CollatzResearch.WordTrace tailWord_1960171 prefixEnd_1960171 671006592002903703765229 := by
  unfold tailWord_1960171
  simp only [CollatzResearch.WordTrace]
  refine ⟨71493309781642712399464367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47662206521095141599642911 71493309781642712399464367)
  ·
    refine ⟨107239964672464068599196551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71493309781642712399464367 107239964672464068599196551)
    ·
      refine ⟨160859947008696102898794827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107239964672464068599196551 160859947008696102898794827)
      ·
        refine ⟨241289920513044154348192241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160859947008696102898794827 241289920513044154348192241)
        ·
          refine ⟨180967440384783115761144181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241289920513044154348192241 180967440384783115761144181)
          ·
            refine ⟨16965697536073417102607267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180967440384783115761144181 16965697536073417102607267)
            ·
              refine ⟨25448546304110125653910901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16965697536073417102607267 25448546304110125653910901)
              ·
                refine ⟨2385801216010324280054147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25448546304110125653910901 2385801216010324280054147)
                ·
                  refine ⟨3578701824015486420081221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385801216010324280054147 3578701824015486420081221)
                  ·
                    refine ⟨671006592002903703765229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3578701824015486420081221 671006592002903703765229)
                    ·
                      rfl

theorem cell22_1960171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 4].length) (baseStart_1960171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960171 prefixEnd_1960171 := by exact prefixLift 1960171
  have htrace : WordTrace (prefixWord ++ tailWord_1960171) baseStart_1960171 baseEnd_1960171 := by
    simpa [prefixWord, tailWord_1960171, baseEnd_1960171] using wordTrace_append hprefix tailTrace_1960171
  have hstable : (prefixWord ++ tailWord_1960171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960171).length < 2 ^ (prefixWord ++ tailWord_1960171).sum := by decide
  have hdescent : baseEnd_1960171 < baseStart_1960171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960186 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_1960186 : Nat := 118140960795 + 1960186 * 2 ^ 59
def prefixEnd_1960186 : Nat := 4983230072969 + 3 ^ 40 * 1960186 * 2
def baseEnd_1960186 : Nat := 223670575603149554880061

theorem tailTrace_1960186 : CollatzResearch.WordTrace tailWord_1960186 prefixEnd_1960186 223670575603149554880061 := by
  unfold tailWord_1960186
  simp only [CollatzResearch.WordTrace]
  refine ⟨17873464219147092490315103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47662571251058913307506941 17873464219147092490315103)
  ·
    refine ⟨26810196328720638735472655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17873464219147092490315103 26810196328720638735472655)
    ·
      refine ⟨40215294493080958103208983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26810196328720638735472655 40215294493080958103208983)
      ·
        refine ⟨60322941739621437154813475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40215294493080958103208983 60322941739621437154813475)
        ·
          refine ⟨90484412609432155732220213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60322941739621437154813475 90484412609432155732220213)
          ·
            refine ⟨8482913682134264599895645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90484412609432155732220213 8482913682134264599895645)
            ·
              refine ⟨3181092630800349224960867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8482913682134264599895645 3181092630800349224960867)
              ·
                refine ⟨4771638946200523837441301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181092630800349224960867 4771638946200523837441301)
                ·
                  refine ⟨223670575603149554880061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4771638946200523837441301 223670575603149554880061)
                  ·
                    rfl

theorem cell22_1960186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_1960186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960186 prefixEnd_1960186 := by exact prefixLift 1960186
  have htrace : WordTrace (prefixWord ++ tailWord_1960186) baseStart_1960186 baseEnd_1960186 := by
    simpa [prefixWord, tailWord_1960186, baseEnd_1960186] using wordTrace_append hprefix tailTrace_1960186
  have hstable : (prefixWord ++ tailWord_1960186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960186).length < 2 ^ (prefixWord ++ tailWord_1960186).sum := by decide
  have hdescent : baseEnd_1960186 < baseStart_1960186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960218 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_1960218 : Nat := 118140960795 + 1960218 * 2 ^ 59
def prefixEnd_1960218 : Nat := 4983230072969 + 3 ^ 40 * 1960218 * 2
def baseEnd_1960218 : Nat := 671022681063411247840085

theorem tailTrace_1960218 : CollatzResearch.WordTrace tailWord_1960218 prefixEnd_1960218 671022681063411247840085 := by
  unfold tailWord_1960218
  simp only [CollatzResearch.WordTrace]
  refine ⟨17873756003118109856606327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47663349341648292950950205 17873756003118109856606327)
  ·
    refine ⟨26810634004677164784909491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17873756003118109856606327 26810634004677164784909491)
    ·
      refine ⟨40215951007015747177364237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26810634004677164784909491 40215951007015747177364237)
      ·
        refine ⟨15080981627630905191511589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40215951007015747177364237 15080981627630905191511589)
        ·
          refine ⟨2827684055180794723408423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15080981627630905191511589 2827684055180794723408423)
          ·
            refine ⟨4241526082771192085112635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827684055180794723408423 4241526082771192085112635)
            ·
              refine ⟨6362289124156788127668953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241526082771192085112635 6362289124156788127668953)
              ·
                refine ⟨4771716843117591095751715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6362289124156788127668953 4771716843117591095751715)
                ·
                  refine ⟨7157575264676386643627573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771716843117591095751715 7157575264676386643627573)
                  ·
                    refine ⟨671022681063411247840085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7157575264676386643627573 671022681063411247840085)
                    ·
                      rfl

theorem cell22_1960218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_1960218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960218 prefixEnd_1960218 := by exact prefixLift 1960218
  have htrace : WordTrace (prefixWord ++ tailWord_1960218) baseStart_1960218 baseEnd_1960218 := by
    simpa [prefixWord, tailWord_1960218, baseEnd_1960218] using wordTrace_append hprefix tailTrace_1960218
  have hstable : (prefixWord ++ tailWord_1960218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960218).length < 2 ^ (prefixWord ++ tailWord_1960218).sum := by decide
  have hdescent : baseEnd_1960218 < baseStart_1960218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960237 : List Nat := [1, 5, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1960237 : Nat := 118140960795 + 1960237 * 2 ^ 59
def prefixEnd_1960237 : Nat := 4983230072969 + 3 ^ 40 * 1960237 * 2
def baseEnd_1960237 : Nat := 223676395050567177205009

theorem tailTrace_1960237 : CollatzResearch.WordTrace tailWord_1960237 prefixEnd_1960237 223676395050567177205009 := by
  unfold tailWord_1960237
  simp only [CollatzResearch.WordTrace]
  refine ⟨71495716999403605671366965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47663811332935737114244643 71495716999403605671366965)
  ·
    refine ⟨6702723468694088031690653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71495716999403605671366965 6702723468694088031690653)
    ·
      refine ⟨2513521300760283011883995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6702723468694088031690653 2513521300760283011883995)
      ·
        refine ⟨3770281951140424517825993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513521300760283011883995 3770281951140424517825993)
        ·
          refine ⟨2827711463355318388369495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3770281951140424517825993 2827711463355318388369495)
          ·
            refine ⟨4241567195032977582554243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827711463355318388369495 4241567195032977582554243)
            ·
              refine ⟨6362350792549466373831365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241567195032977582554243 6362350792549466373831365)
              ·
                refine ⟨1192940773603024945093381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6362350792549466373831365 1192940773603024945093381)
                ·
                  refine ⟨223676395050567177205009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192940773603024945093381 223676395050567177205009)
                  ·
                    rfl

theorem cell22_1960237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1960237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960237 prefixEnd_1960237 := by exact prefixLift 1960237
  have htrace : WordTrace (prefixWord ++ tailWord_1960237) baseStart_1960237 baseEnd_1960237 := by
    simpa [prefixWord, tailWord_1960237, baseEnd_1960237] using wordTrace_append hprefix tailTrace_1960237
  have hstable : (prefixWord ++ tailWord_1960237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960237).length < 2 ^ (prefixWord ++ tailWord_1960237).sum := by decide
  have hdescent : baseEnd_1960237 < baseStart_1960237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960263 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 3, 3]
def baseStart_1960263 : Nat := 118140960795 + 1960263 * 2 ^ 59
def prefixEnd_1960263 : Nat := 4983230072969 + 3 ^ 40 * 1960263 * 2
def baseEnd_1960263 : Nat := 671038085483046130464947

theorem tailTrace_1960263 : CollatzResearch.WordTrace tailWord_1960263 prefixEnd_1960263 671038085483046130464947 := by
  unfold tailWord_1960263
  simp only [CollatzResearch.WordTrace]
  refine ⟨71496665297309412111813443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47664443531539608074542295 71496665297309412111813443)
  ·
    refine ⟨107244997945964118167720165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71496665297309412111813443 107244997945964118167720165)
    ·
      refine ⟨20108437114868272156447531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107244997945964118167720165 20108437114868272156447531)
      ·
        refine ⟨30162655672302408234671297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20108437114868272156447531 30162655672302408234671297)
        ·
          refine ⟨22621991754226806176003473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30162655672302408234671297 22621991754226806176003473)
          ·
            refine ⟨16966493815670104632002605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22621991754226806176003473 16966493815670104632002605)
            ·
              refine ⟨6362435180876289237000977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16966493815670104632002605 6362435180876289237000977)
              ·
                refine ⟨4771826385657216927750733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6362435180876289237000977 4771826385657216927750733)
                ·
                  refine ⟨1789434894621456347906525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4771826385657216927750733 1789434894621456347906525)
                  ·
                    refine ⟨671038085483046130464947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789434894621456347906525 671038085483046130464947)
                    ·
                      rfl

theorem cell22_1960263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_1960263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960263 prefixEnd_1960263 := by exact prefixLift 1960263
  have htrace : WordTrace (prefixWord ++ tailWord_1960263) baseStart_1960263 baseEnd_1960263 := by
    simpa [prefixWord, tailWord_1960263, baseEnd_1960263] using wordTrace_append hprefix tailTrace_1960263
  have hstable : (prefixWord ++ tailWord_1960263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960263).length < 2 ^ (prefixWord ++ tailWord_1960263).sum := by decide
  have hdescent : baseEnd_1960263 < baseStart_1960263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960286 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1960286 : Nat := 118140960795 + 1960286 * 2 ^ 59
def prefixEnd_1960286 : Nat := 4983230072969 + 3 ^ 40 * 1960286 * 2
def baseEnd_1960286 : Nat := 671045958853081737139877

theorem tailTrace_1960286 : CollatzResearch.WordTrace tailWord_1960286 prefixEnd_1960286 671045958853081737139877 := by
  unfold tailWord_1960286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8937188022028260879987589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47665002784150724693267141 8937188022028260879987589)
  ·
    refine ⟨1675722754130298914997673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8937188022028260879987589 1675722754130298914997673)
    ·
      refine ⟨1256792065597724186248255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1675722754130298914997673 1256792065597724186248255)
      ·
        refine ⟨1885188098396586279372383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256792065597724186248255 1885188098396586279372383)
        ·
          refine ⟨2827782147594879419058575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885188098396586279372383 2827782147594879419058575)
          ·
            refine ⟨4241673221392319128587863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827782147594879419058575 4241673221392319128587863)
            ·
              refine ⟨6362509832088478692881795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241673221392319128587863 6362509832088478692881795)
              ·
                refine ⟨9543764748132718039322693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362509832088478692881795 9543764748132718039322693)
                ·
                  refine ⟨1789455890274884632373005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9543764748132718039322693 1789455890274884632373005)
                  ·
                    refine ⟨671045958853081737139877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789455890274884632373005 671045958853081737139877)
                    ·
                      rfl

theorem cell22_1960286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1960286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960286 prefixEnd_1960286 := by exact prefixLift 1960286
  have htrace : WordTrace (prefixWord ++ tailWord_1960286) baseStart_1960286 baseEnd_1960286 := by
    simpa [prefixWord, tailWord_1960286, baseEnd_1960286] using wordTrace_append hprefix tailTrace_1960286
  have hstable : (prefixWord ++ tailWord_1960286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960286).length < 2 ^ (prefixWord ++ tailWord_1960286).sum := by decide
  have hdescent : baseEnd_1960286 < baseStart_1960286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960291 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 4, 5]
def baseStart_1960291 : Nat := 118140960795 + 1960291 * 2 ^ 59
def prefixEnd_1960291 : Nat := 4983230072969 + 3 ^ 40 * 1960291 * 2
def baseEnd_1960291 : Nat := 671047670455263390764861

theorem tailTrace_1960291 : CollatzResearch.WordTrace tailWord_1960291 prefixEnd_1960291 671047670455263390764861 := by
  unfold tailWord_1960291
  simp only [CollatzResearch.WordTrace]
  refine ⟨71497686541207972893832727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47665124360805315262555151 71497686541207972893832727)
  ·
    refine ⟨107246529811811959340749091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71497686541207972893832727 107246529811811959340749091)
    ·
      refine ⟨160869794717717939011123637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107246529811811959340749091 160869794717717939011123637)
      ·
        refine ⟨15081543254786056782292841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160869794717717939011123637 15081543254786056782292841)
        ·
          refine ⟨11311157441089542586719631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15081543254786056782292841 11311157441089542586719631)
          ·
            refine ⟨16966736161634313880079447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311157441089542586719631 16966736161634313880079447)
            ·
              refine ⟨25450104242451470820119171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16966736161634313880079447 25450104242451470820119171)
              ·
                refine ⟨38175156363677206230178757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25450104242451470820119171 38175156363677206230178757)
                ·
                  refine ⟨7157841818189476168158517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38175156363677206230178757 7157841818189476168158517)
                  ·
                    refine ⟨671047670455263390764861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7157841818189476168158517 671047670455263390764861)
                    ·
                      rfl

theorem cell22_1960291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_1960291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960291 prefixEnd_1960291 := by exact prefixLift 1960291
  have htrace : WordTrace (prefixWord ++ tailWord_1960291) baseStart_1960291 baseEnd_1960291 := by
    simpa [prefixWord, tailWord_1960291, baseEnd_1960291] using wordTrace_append hprefix tailTrace_1960291
  have hstable : (prefixWord ++ tailWord_1960291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960291).length < 2 ^ (prefixWord ++ tailWord_1960291).sum := by decide
  have hdescent : baseEnd_1960291 < baseStart_1960291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960293 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 5]
def baseStart_1960293 : Nat := 118140960795 + 1960293 * 2 ^ 59
def prefixEnd_1960293 : Nat := 4983230072969 + 3 ^ 40 * 1960293 * 2
def baseEnd_1960293 : Nat := 223682785032045350738285

theorem tailTrace_1960293 : CollatzResearch.WordTrace tailWord_1960293 prefixEnd_1960293 223682785032045350738285 := by
  unfold tailWord_1960293
  simp only [CollatzResearch.WordTrace]
  refine ⟨71497759487200727235405533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47665172991467151490270355 71497759487200727235405533)
  ·
    refine ⟨26811659807700272713277075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71497759487200727235405533 26811659807700272713277075)
    ·
      refine ⟨40217489711550409069915613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26811659807700272713277075 40217489711550409069915613)
      ·
        refine ⟨15081558641831403401218355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40217489711550409069915613 15081558641831403401218355)
        ·
          refine ⟨22622337962747105101827533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15081558641831403401218355 22622337962747105101827533)
          ·
            refine ⟨8483376736030164413185325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22622337962747105101827533 8483376736030164413185325)
            ·
              refine ⟨3181266276011311654944497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8483376736030164413185325 3181266276011311654944497)
              ·
                refine ⟨2385949707008483741208373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3181266276011311654944497 2385949707008483741208373)
                ·
                  refine ⟨223682785032045350738285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2385949707008483741208373 223682785032045350738285)
                  ·
                    rfl

theorem cell22_1960293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_1960293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960293 prefixEnd_1960293 := by exact prefixLift 1960293
  have htrace : WordTrace (prefixWord ++ tailWord_1960293) baseStart_1960293 baseEnd_1960293 := by
    simpa [prefixWord, tailWord_1960293, baseEnd_1960293] using wordTrace_append hprefix tailTrace_1960293
  have hstable : (prefixWord ++ tailWord_1960293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960293).length < 2 ^ (prefixWord ++ tailWord_1960293).sum := by decide
  have hdescent : baseEnd_1960293 < baseStart_1960293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960370 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_1960370 : Nat := 118140960795 + 1960370 * 2 ^ 59
def prefixEnd_1960370 : Nat := 4983230072969 + 3 ^ 40 * 1960370 * 2
def baseEnd_1960370 : Nat := 671074713769733518039619

theorem tailTrace_1960370 : CollatzResearch.WordTrace tailWord_1960370 prefixEnd_1960370 671074713769733518039619 := by
  unfold tailWord_1960370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17875141976980442346489641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47667045271947846257305709 17875141976980442346489641)
  ·
    refine ⟨13406356482735331759867231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17875141976980442346489641 13406356482735331759867231)
    ·
      refine ⟨20109534724102997639800847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13406356482735331759867231 20109534724102997639800847)
      ·
        refine ⟨30164302086154496459701271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20109534724102997639800847 30164302086154496459701271)
        ·
          refine ⟨45246453129231744689551907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30164302086154496459701271 45246453129231744689551907)
          ·
            refine ⟨67869679693847617034327861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45246453129231744689551907 67869679693847617034327861)
            ·
              refine ⟨6362782471298214096968237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67869679693847617034327861 6362782471298214096968237)
              ·
                refine ⟨2386043426736830286363089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6362782471298214096968237 2386043426736830286363089)
                ·
                  refine ⟨1789532570052622714772317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2386043426736830286363089 1789532570052622714772317)
                  ·
                    refine ⟨671074713769733518039619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789532570052622714772317 671074713769733518039619)
                    ·
                      rfl

theorem cell22_1960370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_1960370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960370 prefixEnd_1960370 := by exact prefixLift 1960370
  have htrace : WordTrace (prefixWord ++ tailWord_1960370) baseStart_1960370 baseEnd_1960370 := by
    simpa [prefixWord, tailWord_1960370, baseEnd_1960370] using wordTrace_append hprefix tailTrace_1960370
  have hstable : (prefixWord ++ tailWord_1960370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960370).length < 2 ^ (prefixWord ++ tailWord_1960370).sum := by decide
  have hdescent : baseEnd_1960370 < baseStart_1960370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960413 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1960413 : Nat := 118140960795 + 1960413 * 2 ^ 59
def prefixEnd_1960413 : Nat := 4983230072969 + 3 ^ 40 * 1960413 * 2
def baseEnd_1960413 : Nat := 671089433548495739214487

theorem tailTrace_1960413 : CollatzResearch.WordTrace tailWord_1960413 prefixEnd_1960413 671089433548495739214487 := by
  unfold tailWord_1960413
  simp only [CollatzResearch.WordTrace]
  refine ⟨71502136246765987729773893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47668090831177325153182595 71502136246765987729773893)
  ·
    refine ⟨13406650546268622699332605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71502136246765987729773893 13406650546268622699332605)
    ·
      refine ⟨5027493954850733512249727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13406650546268622699332605 5027493954850733512249727)
      ·
        refine ⟨7541240932276100268374591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5027493954850733512249727 7541240932276100268374591)
        ·
          refine ⟨11311861398414150402561887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541240932276100268374591 11311861398414150402561887)
          ·
            refine ⟨16967792097621225603842831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311861398414150402561887 16967792097621225603842831)
            ·
              refine ⟨25451688146431838405764247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16967792097621225603842831 25451688146431838405764247)
              ·
                refine ⟨38177532219647757608646371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25451688146431838405764247 38177532219647757608646371)
                ·
                  refine ⟨57266298329471636412969557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38177532219647757608646371 57266298329471636412969557)
                  ·
                    refine ⟨671089433548495739214487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57266298329471636412969557 671089433548495739214487)
                    ·
                      rfl

theorem cell22_1960413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1960413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960413 prefixEnd_1960413 := by exact prefixLift 1960413
  have htrace : WordTrace (prefixWord ++ tailWord_1960413) baseStart_1960413 baseEnd_1960413 := by
    simpa [prefixWord, tailWord_1960413, baseEnd_1960413] using wordTrace_append hprefix tailTrace_1960413
  have hstable : (prefixWord ++ tailWord_1960413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960413).length < 2 ^ (prefixWord ++ tailWord_1960413).sum := by decide
  have hdescent : baseEnd_1960413 < baseStart_1960413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960428 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 5]
def baseStart_1960428 : Nat := 118140960795 + 1960428 * 2 ^ 59
def prefixEnd_1960428 : Nat := 4983230072969 + 3 ^ 40 * 1960428 * 2
def baseEnd_1960428 : Nat := 223698189451680233363147

theorem tailTrace_1960428 : CollatzResearch.WordTrace tailWord_1960428 prefixEnd_1960428 223698189451680233363147 := by
  unfold tailWord_1960428
  simp only [CollatzResearch.WordTrace]
  refine ⟨35751341670855822645784969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47668455561141096861046625 35751341670855822645784969)
  ·
    refine ⟨26813506253141866984338727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35751341670855822645784969 26813506253141866984338727)
    ·
      refine ⟨40220259379712800476508091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26813506253141866984338727 40220259379712800476508091)
      ·
        refine ⟨60330389069569200714762137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40220259379712800476508091 60330389069569200714762137)
        ·
          refine ⟨45247791802176900536071603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60330389069569200714762137 45247791802176900536071603)
          ·
            refine ⟨67871687703265350804107405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45247791802176900536071603 67871687703265350804107405)
            ·
              refine ⟨25451882888724506551540277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67871687703265350804107405 25451882888724506551540277)
              ·
                refine ⟨2386114020817922489206901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25451882888724506551540277 2386114020817922489206901)
                ·
                  refine ⟨223698189451680233363147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2386114020817922489206901 223698189451680233363147)
                  ·
                    rfl

theorem cell22_1960428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_1960428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960428 prefixEnd_1960428 := by exact prefixLift 1960428
  have htrace : WordTrace (prefixWord ++ tailWord_1960428) baseStart_1960428 baseEnd_1960428 := by
    simpa [prefixWord, tailWord_1960428, baseEnd_1960428] using wordTrace_append hprefix tailTrace_1960428
  have hstable : (prefixWord ++ tailWord_1960428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960428).length < 2 ^ (prefixWord ++ tailWord_1960428).sum := by decide
  have hdescent : baseEnd_1960428 < baseStart_1960428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960449 : List Nat := [1, 2, 4, 1, 3, 2, 2, 3, 1, 3]
def baseStart_1960449 : Nat := 118140960795 + 1960449 * 2 ^ 59
def prefixEnd_1960449 : Nat := 4983230072969 + 3 ^ 40 * 1960449 * 2
def baseEnd_1960449 : Nat := 671101757084203645314377

theorem tailTrace_1960449 : CollatzResearch.WordTrace tailWord_1960449 prefixEnd_1960449 671101757084203645314377 := by
  unfold tailWord_1960449
  simp only [CollatzResearch.WordTrace]
  refine ⟨71503449274635565878084401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47668966183090377252056267 71503449274635565878084401)
  ·
    refine ⟨53627586955976674408563301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71503449274635565878084401 53627586955976674408563301)
    ·
      refine ⟨10055172554245626451605619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53627586955976674408563301 10055172554245626451605619)
      ·
        refine ⟨15082758831368439677408429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10055172554245626451605619 15082758831368439677408429)
        ·
          refine ⟨5656034561763164879028161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15082758831368439677408429 5656034561763164879028161)
          ·
            refine ⟨4242025921322373659271121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5656034561763164879028161 4242025921322373659271121)
            ·
              refine ⟨3181519440991780244453341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4242025921322373659271121 3181519440991780244453341)
              ·
                refine ⟨1193069790371917591670003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3181519440991780244453341 1193069790371917591670003)
                ·
                  refine ⟨1789604685557876387505005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193069790371917591670003 1789604685557876387505005)
                  ·
                    refine ⟨671101757084203645314377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789604685557876387505005 671101757084203645314377)
                    ·
                      rfl

theorem cell22_1960449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_1960449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960449 prefixEnd_1960449 := by exact prefixLift 1960449
  have htrace : WordTrace (prefixWord ++ tailWord_1960449) baseStart_1960449 baseEnd_1960449 := by
    simpa [prefixWord, tailWord_1960449, baseEnd_1960449] using wordTrace_append hprefix tailTrace_1960449
  have hstable : (prefixWord ++ tailWord_1960449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960449).length < 2 ^ (prefixWord ++ tailWord_1960449).sum := by decide
  have hdescent : baseEnd_1960449 < baseStart_1960449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960462 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_1960462 : Nat := 118140960795 + 1960462 * 2 ^ 59
def prefixEnd_1960462 : Nat := 4983230072969 + 3 ^ 40 * 1960462 * 2
def baseEnd_1960462 : Nat := 223702069083291981579779

theorem tailTrace_1960462 : CollatzResearch.WordTrace tailWord_1960462 prefixEnd_1960462 223702069083291981579779 := by
  unfold tailWord_1960462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8937990427948558637288455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47669282282392312732205093 8937990427948558637288455)
  ·
    refine ⟨13406985641922837955932683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8937990427948558637288455 13406985641922837955932683)
    ·
      refine ⟨20110478462884256933899025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13406985641922837955932683 20110478462884256933899025)
      ·
        refine ⟨15082858847163192700424269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20110478462884256933899025 15082858847163192700424269)
        ·
          refine ⟨5656072067686197262659101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15082858847163192700424269 5656072067686197262659101)
          ·
            refine ⟨2121027025382323973497163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5656072067686197262659101 2121027025382323973497163)
            ·
              refine ⟨3181540538073485960245745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121027025382323973497163 3181540538073485960245745)
              ·
                refine ⟨2386155403555114470184309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3181540538073485960245745 2386155403555114470184309)
                ·
                  refine ⟨223702069083291981579779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2386155403555114470184309 223702069083291981579779)
                  ·
                    rfl

theorem cell22_1960462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_1960462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960462 prefixEnd_1960462 := by exact prefixLift 1960462
  have htrace : WordTrace (prefixWord ++ tailWord_1960462) baseStart_1960462 baseEnd_1960462 := by
    simpa [prefixWord, tailWord_1960462, baseEnd_1960462] using wordTrace_append hprefix tailTrace_1960462
  have hstable : (prefixWord ++ tailWord_1960462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960462).length < 2 ^ (prefixWord ++ tailWord_1960462).sum := by decide
  have hdescent : baseEnd_1960462 < baseStart_1960462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960490 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_1960490 : Nat := 118140960795 + 1960490 * 2 ^ 59
def prefixEnd_1960490 : Nat := 4983230072969 + 3 ^ 40 * 1960490 * 2
def baseEnd_1960490 : Nat := 223705264074031068346417

theorem tailTrace_1960490 : CollatzResearch.WordTrace tailWord_1960490 prefixEnd_1960490 223705264074031068346417 := by
  unfold tailWord_1960490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17876236166871757470081731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47669963111658019920217949 17876236166871757470081731)
  ·
    refine ⟨26814354250307636205122597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17876236166871757470081731 26814354250307636205122597)
    ·
      refine ⟨5027691421932681788460487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26814354250307636205122597 5027691421932681788460487)
      ·
        refine ⟨7541537132899022682690731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5027691421932681788460487 7541537132899022682690731)
        ·
          refine ⟨11312305699348534024036097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541537132899022682690731 11312305699348534024036097)
          ·
            refine ⟨8484229274511400518027073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11312305699348534024036097 8484229274511400518027073)
            ·
              refine ⟨6363171955883550388520305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8484229274511400518027073 6363171955883550388520305)
              ·
                refine ⟨4772378966912662791390229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6363171955883550388520305 4772378966912662791390229)
                ·
                  refine ⟨223705264074031068346417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4772378966912662791390229 223705264074031068346417)
                  ·
                    rfl

theorem cell22_1960490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_1960490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960490 prefixEnd_1960490 := by exact prefixLift 1960490
  have htrace : WordTrace (prefixWord ++ tailWord_1960490) baseStart_1960490 baseEnd_1960490 := by
    simpa [prefixWord, tailWord_1960490, baseEnd_1960490] using wordTrace_append hprefix tailTrace_1960490
  have hstable : (prefixWord ++ tailWord_1960490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960490).length < 2 ^ (prefixWord ++ tailWord_1960490).sum := by decide
  have hdescent : baseEnd_1960490 < baseStart_1960490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
