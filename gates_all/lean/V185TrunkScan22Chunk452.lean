import V185TrunkScan22Chunk451

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4029730 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_4029730 : Nat := 118140960795 + 4029730 * 2 ^ 59
def prefixEnd_4029730 : Nat := 4983230072969 + 3 ^ 40 * 4029730 * 2
def baseEnd_4029730 : Nat := 1379458931895082597695077

theorem tailTrace_4029730 : CollatzResearch.WordTrace tailWord_4029730 prefixEnd_4029730 1379458931895082597695077 := by
  unfold tailWord_4029730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36744081922745976984217661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97984218460655938624580429 36744081922745976984217661)
  ·
    refine ⟨13779030721029741369081623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36744081922745976984217661 13779030721029741369081623)
    ·
      refine ⟨20668546081544612053622435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13779030721029741369081623 20668546081544612053622435)
      ·
        refine ⟨31002819122316918080433653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20668546081544612053622435 31002819122316918080433653)
        ·
          refine ⟨2906514292717211070040655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31002819122316918080433653 2906514292717211070040655)
          ·
            refine ⟨4359771439075816605060983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906514292717211070040655 4359771439075816605060983)
            ·
              refine ⟨6539657158613724907591475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359771439075816605060983 6539657158613724907591475)
              ·
                refine ⟨9809485737920587361387213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539657158613724907591475 9809485737920587361387213)
                ·
                  refine ⟨3678557151720220260520205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9809485737920587361387213 3678557151720220260520205)
                  ·
                    refine ⟨1379458931895082597695077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3678557151720220260520205 1379458931895082597695077)
                    ·
                      rfl

theorem cell22_4029730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_4029730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029730 prefixEnd_4029730 := by exact prefixLift 4029730
  have htrace : WordTrace (prefixWord ++ tailWord_4029730) baseStart_4029730 baseEnd_4029730 := by
    simpa [prefixWord, tailWord_4029730, baseEnd_4029730] using wordTrace_append hprefix tailTrace_4029730
  have hstable : (prefixWord ++ tailWord_4029730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029730).length < 2 ^ (prefixWord ++ tailWord_4029730).sum := by decide
  have hdescent : baseEnd_4029730 < baseStart_4029730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029756 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_4029756 : Nat := 118140960795 + 4029756 * 2 ^ 59
def prefixEnd_4029756 : Nat := 4983230072969 + 3 ^ 40 * 4029756 * 2
def baseEnd_4029756 : Nat := 1379467832226427196544997

theorem tailTrace_4029756 : CollatzResearch.WordTrace tailWord_4029756 prefixEnd_4029756 1379467832226427196544997 := by
  unfold tailWord_4029756
  simp only [CollatzResearch.WordTrace]
  refine ⟨73488637994444857188658561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97984850659259809584878081 73488637994444857188658561)
  ·
    refine ⟨55116478495833642891493921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73488637994444857188658561 55116478495833642891493921)
    ·
      refine ⟨41337358871875232168620441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55116478495833642891493921 41337358871875232168620441)
      ·
        refine ⟨31003019153906424126465331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41337358871875232168620441 31003019153906424126465331)
        ·
          refine ⟨46504528730859636189697997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31003019153906424126465331 46504528730859636189697997)
          ·
            refine ⟨17439198274072363571136749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46504528730859636189697997 17439198274072363571136749)
            ·
              refine ⟨6539699352777136339176281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17439198274072363571136749 6539699352777136339176281)
              ·
                refine ⟨4904774514582852254382211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6539699352777136339176281 4904774514582852254382211)
                ·
                  refine ⟨7357161771874278381573317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904774514582852254382211 7357161771874278381573317)
                  ·
                    refine ⟨1379467832226427196544997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357161771874278381573317 1379467832226427196544997)
                    ·
                      rfl

theorem cell22_4029756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_4029756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029756 prefixEnd_4029756 := by exact prefixLift 4029756
  have htrace : WordTrace (prefixWord ++ tailWord_4029756) baseStart_4029756 baseEnd_4029756 := by
    simpa [prefixWord, tailWord_4029756, baseEnd_4029756] using wordTrace_append hprefix tailTrace_4029756
  have hstable : (prefixWord ++ tailWord_4029756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029756).length < 2 ^ (prefixWord ++ tailWord_4029756).sum := by decide
  have hdescent : baseEnd_4029756 < baseStart_4029756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029769 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 6, 3]
def baseStart_4029769 : Nat := 118140960795 + 4029769 * 2 ^ 59
def prefixEnd_4029769 : Nat := 4983230072969 + 3 ^ 40 * 4029769 * 2
def baseEnd_4029769 : Nat := 1379472282392099495969957

theorem tailTrace_4029769 : CollatzResearch.WordTrace tailWord_4029769 prefixEnd_4029769 1379472282392099495969957 := by
  unfold tailWord_4029769
  simp only [CollatzResearch.WordTrace]
  refine ⟨146977750137842617597540361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97985166758561745065026907 146977750137842617597540361)
  ·
    refine ⟨110233312603381963198155271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146977750137842617597540361 110233312603381963198155271)
    ·
      refine ⟨165349968905072944797232907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110233312603381963198155271 165349968905072944797232907)
      ·
        refine ⟨248024953357609417195849361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165349968905072944797232907 248024953357609417195849361)
        ·
          refine ⟨186018715018207062896887021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248024953357609417195849361 186018715018207062896887021)
          ·
            refine ⟨69757018131827648586332633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186018715018207062896887021 69757018131827648586332633)
            ·
              refine ⟨52317763598870736439749475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69757018131827648586332633 52317763598870736439749475)
              ·
                refine ⟨78476645398306104659624213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52317763598870736439749475 78476645398306104659624213)
                ·
                  refine ⟨3678592753045598655919885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78476645398306104659624213 3678592753045598655919885)
                  ·
                    refine ⟨1379472282392099495969957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3678592753045598655919885 1379472282392099495969957)
                    ·
                      rfl

theorem cell22_4029769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 3].length) (baseStart_4029769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029769 prefixEnd_4029769 := by exact prefixLift 4029769
  have htrace : WordTrace (prefixWord ++ tailWord_4029769) baseStart_4029769 baseEnd_4029769 := by
    simpa [prefixWord, tailWord_4029769, baseEnd_4029769] using wordTrace_append hprefix tailTrace_4029769
  have hstable : (prefixWord ++ tailWord_4029769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029769).length < 2 ^ (prefixWord ++ tailWord_4029769).sum := by decide
  have hdescent : baseEnd_4029769 < baseStart_4029769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029784 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_4029784 : Nat := 118140960795 + 4029784 * 2 ^ 59
def prefixEnd_4029784 : Nat := 4983230072969 + 3 ^ 40 * 4029784 * 2
def baseEnd_4029784 : Nat := 1379477417198644456844911

theorem tailTrace_4029784 : CollatzResearch.WordTrace tailWord_4029784 prefixEnd_4029784 1379477417198644456844911 := by
  unfold tailWord_4029784
  simp only [CollatzResearch.WordTrace]
  refine ⟨73489148616394137579668203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97985531488525516772890937 73489148616394137579668203)
  ·
    refine ⟨110233722924591206369502305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73489148616394137579668203 110233722924591206369502305)
    ·
      refine ⟨82675292193443404777126729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110233722924591206369502305 82675292193443404777126729)
      ·
        refine ⟨62006469145082553582845047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82675292193443404777126729 62006469145082553582845047)
        ·
          refine ⟨93009703717623830374267571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62006469145082553582845047 93009703717623830374267571)
          ·
            refine ⟨139514555576435745561401357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93009703717623830374267571 139514555576435745561401357)
            ·
              refine ⟨52317958341163404585525509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139514555576435745561401357 52317958341163404585525509)
              ·
                refine ⟨9809617188968138359786033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52317958341163404585525509 9809617188968138359786033)
                ·
                  refine ⟨7357212891726103769839525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9809617188968138359786033 7357212891726103769839525)
                  ·
                    refine ⟨1379477417198644456844911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357212891726103769839525 1379477417198644456844911)
                    ·
                      rfl

theorem cell22_4029784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_4029784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029784 prefixEnd_4029784 := by exact prefixLift 4029784
  have htrace : WordTrace (prefixWord ++ tailWord_4029784) baseStart_4029784 baseEnd_4029784 := by
    simpa [prefixWord, tailWord_4029784, baseEnd_4029784] using wordTrace_append hprefix tailTrace_4029784
  have hstable : (prefixWord ++ tailWord_4029784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029784).length < 2 ^ (prefixWord ++ tailWord_4029784).sum := by decide
  have hdescent : baseEnd_4029784 < baseStart_4029784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029786 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 2, 3]
def baseStart_4029786 : Nat := 118140960795 + 4029786 * 2 ^ 59
def prefixEnd_4029786 : Nat := 4983230072969 + 3 ^ 40 * 4029786 * 2
def baseEnd_4029786 : Nat := 1379478101839517118294905

theorem tailTrace_4029786 : CollatzResearch.WordTrace tailWord_4029786 prefixEnd_4029786 1379478101839517118294905 := by
  unfold tailWord_4029786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36744592544695257375227303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97985580119187353000606141 36744592544695257375227303)
  ·
    refine ⟨55116888817042886062840955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36744592544695257375227303 55116888817042886062840955)
    ·
      refine ⟨82675333225564329094261433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55116888817042886062840955 82675333225564329094261433)
      ·
        refine ⟨62006499919173246820696075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82675333225564329094261433 62006499919173246820696075)
        ·
          refine ⟨93009749878759870231044113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62006499919173246820696075 93009749878759870231044113)
          ·
            refine ⟨69757312409069902673283085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93009749878759870231044113 69757312409069902673283085)
            ·
              refine ⟨26158992153401213502481157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69757312409069902673283085 26158992153401213502481157)
              ·
                refine ⟨4904811028762727531715217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26158992153401213502481157 4904811028762727531715217)
                ·
                  refine ⟨3678608271572045648786413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4904811028762727531715217 3678608271572045648786413)
                  ·
                    refine ⟨1379478101839517118294905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3678608271572045648786413 1379478101839517118294905)
                    ·
                      rfl

theorem cell22_4029786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_4029786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029786 prefixEnd_4029786 := by exact prefixLift 4029786
  have htrace : WordTrace (prefixWord ++ tailWord_4029786) baseStart_4029786 baseEnd_4029786 := by
    simpa [prefixWord, tailWord_4029786, baseEnd_4029786] using wordTrace_append hprefix tailTrace_4029786
  have hstable : (prefixWord ++ tailWord_4029786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029786).length < 2 ^ (prefixWord ++ tailWord_4029786).sum := by decide
  have hdescent : baseEnd_4029786 < baseStart_4029786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029822 : List Nat := [4, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_4029822 : Nat := 118140960795 + 4029822 * 2 ^ 59
def prefixEnd_4029822 : Nat := 4983230072969 + 3 ^ 40 * 4029822 * 2
def baseEnd_4029822 : Nat := 459830141791741674798265

theorem tailTrace_4029822 : CollatzResearch.WordTrace tailWord_4029822 prefixEnd_4029822 459830141791741674798265 := by
  unfold tailWord_4029822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18372460400831325956152465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97986455471100405099479813 18372460400831325956152465)
  ·
    refine ⟨13779345300623494467114349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18372460400831325956152465 13779345300623494467114349)
    ·
      refine ⟨5167254487733810425167881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13779345300623494467114349 5167254487733810425167881)
      ·
        refine ⟨3875440865800357818875911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5167254487733810425167881 3875440865800357818875911)
        ·
          refine ⟨5813161298700536728313867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3875440865800357818875911 5813161298700536728313867)
          ·
            refine ⟨8719741948050805092470801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5813161298700536728313867 8719741948050805092470801)
            ·
              refine ⟨6539806461038103819353101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8719741948050805092470801 6539806461038103819353101)
              ·
                refine ⟨2452427422889288932257413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6539806461038103819353101 2452427422889288932257413)
                ·
                  refine ⟨459830141791741674798265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452427422889288932257413 459830141791741674798265)
                  ·
                    rfl

theorem cell22_4029822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_4029822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029822 prefixEnd_4029822 := by exact prefixLift 4029822
  have htrace : WordTrace (prefixWord ++ tailWord_4029822) baseStart_4029822 baseEnd_4029822 := by
    simpa [prefixWord, tailWord_4029822, baseEnd_4029822] using wordTrace_append hprefix tailTrace_4029822
  have hstable : (prefixWord ++ tailWord_4029822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029822).length < 2 ^ (prefixWord ++ tailWord_4029822).sum := by decide
  have hdescent : baseEnd_4029822 < baseStart_4029822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029859 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 2, 5]
def baseStart_4029859 : Nat := 118140960795 + 4029859 * 2 ^ 59
def prefixEnd_4029859 : Nat := 4983230072969 + 3 ^ 40 * 4029859 * 2
def baseEnd_4029859 : Nat := 1379503091231369261219681

theorem tailTrace_4029859 : CollatzResearch.WordTrace tailWord_4029859 prefixEnd_4029859 1379503091231369261219681 := by
  unfold tailWord_4029859
  simp only [CollatzResearch.WordTrace]
  refine ⟨146981032707516562968316631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97987355138344375312211087 146981032707516562968316631)
  ·
    refine ⟨220471549061274844452474947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146981032707516562968316631 220471549061274844452474947)
    ·
      refine ⟨330707323591912266678712421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220471549061274844452474947 330707323591912266678712421)
      ·
        refine ⟨62007623173483550002258579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330707323591912266678712421 62007623173483550002258579)
        ·
          refine ⟨93011434760225325003387869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62007623173483550002258579 93011434760225325003387869)
          ·
            refine ⟨34879288035084496876270451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93011434760225325003387869 34879288035084496876270451)
            ·
              refine ⟨52318932052626745314405677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34879288035084496876270451 52318932052626745314405677)
              ·
                refine ⟨19619599519735029492902129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52318932052626745314405677 19619599519735029492902129)
                ·
                  refine ⟨14714699639801272119676597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19619599519735029492902129 14714699639801272119676597)
                  ·
                    refine ⟨1379503091231369261219681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14714699639801272119676597 1379503091231369261219681)
                    ·
                      rfl

theorem cell22_4029859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_4029859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029859 prefixEnd_4029859 := by exact prefixLift 4029859
  have htrace : WordTrace (prefixWord ++ tailWord_4029859) baseStart_4029859 baseEnd_4029859 := by
    simpa [prefixWord, tailWord_4029859, baseEnd_4029859] using wordTrace_append hprefix tailTrace_4029859
  have hstable : (prefixWord ++ tailWord_4029859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029859).length < 2 ^ (prefixWord ++ tailWord_4029859).sum := by decide
  have hdescent : baseEnd_4029859 < baseStart_4029859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029891 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 1, 4]
def baseStart_4029891 : Nat := 118140960795 + 4029891 * 2 ^ 59
def prefixEnd_4029891 : Nat := 4983230072969 + 3 ^ 40 * 4029891 * 2
def baseEnd_4029891 : Nat := 1379514045485331844419583

theorem tailTrace_4029891 : CollatzResearch.WordTrace tailWord_4029891 prefixEnd_4029891 1379514045485331844419583 := by
  unfold tailWord_4029891
  simp only [CollatzResearch.WordTrace]
  refine ⟨146982199843400632433481527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97988133228933754955654351 146982199843400632433481527)
  ·
    refine ⟨220473299765100948650222291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146982199843400632433481527 220473299765100948650222291)
    ·
      refine ⟨330709949647651422975333437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220473299765100948650222291 330709949647651422975333437)
      ·
        refine ⟨124016231117869283615750039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330709949647651422975333437 124016231117869283615750039)
        ·
          refine ⟨186024346676803925423625059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124016231117869283615750039 186024346676803925423625059)
          ·
            refine ⟨279036520015205888135437589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186024346676803925423625059 279036520015205888135437589)
            ·
              refine ⟨13079836875712776006348637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 279036520015205888135437589 13079836875712776006348637)
              ·
                refine ⟨4904938828392291002380739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13079836875712776006348637 4904938828392291002380739)
                ·
                  refine ⟨7357408242588436503571109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904938828392291002380739 7357408242588436503571109)
                  ·
                    refine ⟨1379514045485331844419583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357408242588436503571109 1379514045485331844419583)
                    ·
                      rfl

theorem cell22_4029891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 4].length) (baseStart_4029891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029891 prefixEnd_4029891 := by exact prefixLift 4029891
  have htrace : WordTrace (prefixWord ++ tailWord_4029891) baseStart_4029891 baseEnd_4029891 := by
    simpa [prefixWord, tailWord_4029891, baseEnd_4029891] using wordTrace_append hprefix tailTrace_4029891
  have hstable : (prefixWord ++ tailWord_4029891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029891).length < 2 ^ (prefixWord ++ tailWord_4029891).sum := by decide
  have hdescent : baseEnd_4029891 < baseStart_4029891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029904 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_4029904 : Nat := 118140960795 + 4029904 * 2 ^ 59
def prefixEnd_4029904 : Nat := 4983230072969 + 3 ^ 40 * 4029904 * 2
def baseEnd_4029904 : Nat := 1379518495651004143844543

theorem tailTrace_4029904 : CollatzResearch.WordTrace tailWord_4029904 prefixEnd_4029904 1379518495651004143844543 := by
  unfold tailWord_4029904
  simp only [CollatzResearch.WordTrace]
  refine ⟨73491336996176767826852383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97988449328235690435803177 73491336996176767826852383)
  ·
    refine ⟨110237005494265151740278575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73491336996176767826852383 110237005494265151740278575)
    ·
      refine ⟨165355508241397727610417863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110237005494265151740278575 165355508241397727610417863)
      ·
        refine ⟨248033262362096591415626795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165355508241397727610417863 248033262362096591415626795)
        ·
          refine ⟨372049893543144887123440193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248033262362096591415626795 372049893543144887123440193)
          ·
            refine ⟨279037420157358665342580145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372049893543144887123440193 279037420157358665342580145)
            ·
              refine ⟨209278065118018999006935109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279037420157358665342580145 209278065118018999006935109)
              ·
                refine ⟨39239637209628562313800333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209278065118018999006935109 39239637209628562313800333)
                ·
                  refine ⟨14714863953610710867675125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39239637209628562313800333 14714863953610710867675125)
                  ·
                    refine ⟨1379518495651004143844543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14714863953610710867675125 1379518495651004143844543)
                    ·
                      rfl

theorem cell22_4029904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_4029904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029904 prefixEnd_4029904 := by exact prefixLift 4029904
  have htrace : WordTrace (prefixWord ++ tailWord_4029904) baseStart_4029904 baseEnd_4029904 := by
    simpa [prefixWord, tailWord_4029904, baseEnd_4029904] using wordTrace_append hprefix tailTrace_4029904
  have hstable : (prefixWord ++ tailWord_4029904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029904).length < 2 ^ (prefixWord ++ tailWord_4029904).sum := by decide
  have hdescent : baseEnd_4029904 < baseStart_4029904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029925 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 1, 4]
def baseStart_4029925 : Nat := 118140960795 + 4029925 * 2 ^ 59
def prefixEnd_4029925 : Nat := 4983230072969 + 3 ^ 40 * 4029925 * 2
def baseEnd_4029925 : Nat := 1379525684380167089069479

theorem tailTrace_4029925 : CollatzResearch.WordTrace tailWord_4029925 prefixEnd_4029925 1379525684380167089069479 := by
  unfold tailWord_4029925
  simp only [CollatzResearch.WordTrace]
  refine ⟨146983439925277456240219229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97988959950184970826812819 146983439925277456240219229)
  ·
    refine ⟨55118789971979046090082211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146983439925277456240219229 55118789971979046090082211)
    ·
      refine ⟨82678184957968569135123317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55118789971979046090082211 82678184957968569135123317)
      ·
        refine ⟨7751079839809553356417811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82678184957968569135123317 7751079839809553356417811)
        ·
          refine ⟨11626619759714330034626717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7751079839809553356417811 11626619759714330034626717)
          ·
            refine ⟨4359982409892873762985019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11626619759714330034626717 4359982409892873762985019)
            ·
              refine ⟨6539973614839310644477529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359982409892873762985019 6539973614839310644477529)
              ·
                refine ⟨4904980211129482983358147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6539973614839310644477529 4904980211129482983358147)
                ·
                  refine ⟨7357470316694224475037221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904980211129482983358147 7357470316694224475037221)
                  ·
                    refine ⟨1379525684380167089069479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357470316694224475037221 1379525684380167089069479)
                    ·
                      rfl

theorem cell22_4029925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_4029925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029925 prefixEnd_4029925 := by exact prefixLift 4029925
  have htrace : WordTrace (prefixWord ++ tailWord_4029925) baseStart_4029925 baseEnd_4029925 := by
    simpa [prefixWord, tailWord_4029925, baseEnd_4029925] using wordTrace_append hprefix tailTrace_4029925
  have hstable : (prefixWord ++ tailWord_4029925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029925).length < 2 ^ (prefixWord ++ tailWord_4029925).sum := by decide
  have hdescent : baseEnd_4029925 < baseStart_4029925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029936 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_4029936 : Nat := 118140960795 + 4029936 * 2 ^ 59
def prefixEnd_4029936 : Nat := 4983230072969 + 3 ^ 40 * 4029936 * 2
def baseEnd_4029936 : Nat := 1379529449904966727044445

theorem tailTrace_4029936 : CollatzResearch.WordTrace tailWord_4029936 prefixEnd_4029936 1379529449904966727044445 := by
  unfold tailWord_4029936
  simp only [CollatzResearch.WordTrace]
  refine ⟨73491920564118802559434831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97989227418825070079246441 73491920564118802559434831)
  ·
    refine ⟨110237880846178203839152247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73491920564118802559434831 110237880846178203839152247)
    ·
      refine ⟨165356821269267305758728371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110237880846178203839152247 165356821269267305758728371)
      ·
        refine ⟨248035231903900958638092557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165356821269267305758728371 248035231903900958638092557)
        ·
          refine ⟨93013211963962859489284709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248035231903900958638092557 93013211963962859489284709)
          ·
            refine ⟨17439977243243036154240883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93013211963962859489284709 17439977243243036154240883)
            ·
              refine ⟨26159965864864554231361325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17439977243243036154240883 26159965864864554231361325)
              ·
                refine ⟨9809987199324207836760497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26159965864864554231361325 9809987199324207836760497)
                ·
                  refine ⟨7357490399493155877570373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9809987199324207836760497 7357490399493155877570373)
                  ·
                    refine ⟨1379529449904966727044445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357490399493155877570373 1379529449904966727044445)
                    ·
                      rfl

theorem cell22_4029936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_4029936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029936 prefixEnd_4029936 := by exact prefixLift 4029936
  have htrace : WordTrace (prefixWord ++ tailWord_4029936) baseStart_4029936 baseEnd_4029936 := by
    simpa [prefixWord, tailWord_4029936, baseEnd_4029936] using wordTrace_append hprefix tailTrace_4029936
  have hstable : (prefixWord ++ tailWord_4029936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029936).length < 2 ^ (prefixWord ++ tailWord_4029936).sum := by decide
  have hdescent : baseEnd_4029936 < baseStart_4029936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029938 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_4029938 : Nat := 118140960795 + 4029938 * 2 ^ 59
def prefixEnd_4029938 : Nat := 4983230072969 + 3 ^ 40 * 4029938 * 2
def baseEnd_4029938 : Nat := 1379530134545839388494439

theorem tailTrace_4029938 : CollatzResearch.WordTrace tailWord_4029938 prefixEnd_4029938 1379530134545839388494439 := by
  unfold tailWord_4029938
  simp only [CollatzResearch.WordTrace]
  refine ⟨36745978518557589865110617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97989276049486906306961645 36745978518557589865110617)
  ·
    refine ⟨27559483888918192398832963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36745978518557589865110617 27559483888918192398832963)
    ·
      refine ⟨41339225833377288598249445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27559483888918192398832963 41339225833377288598249445)
      ·
        refine ⟨7751104843758241612171771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41339225833377288598249445 7751104843758241612171771)
        ·
          refine ⟨11626657265637362418257657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7751104843758241612171771 11626657265637362418257657)
          ·
            refine ⟨8719992949228021813693243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11626657265637362418257657 8719992949228021813693243)
            ·
              refine ⟨13079989423842032720539865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8719992949228021813693243 13079989423842032720539865)
              ·
                refine ⟨9809992067881524540404899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13079989423842032720539865 9809992067881524540404899)
                ·
                  refine ⟨14714988101822286810607349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9809992067881524540404899 14714988101822286810607349)
                  ·
                    refine ⟨1379530134545839388494439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14714988101822286810607349 1379530134545839388494439)
                    ·
                      rfl

theorem cell22_4029938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_4029938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029938 prefixEnd_4029938 := by exact prefixLift 4029938
  have htrace : WordTrace (prefixWord ++ tailWord_4029938) baseStart_4029938 baseEnd_4029938 := by
    simpa [prefixWord, tailWord_4029938, baseEnd_4029938] using wordTrace_append hprefix tailTrace_4029938
  have hstable : (prefixWord ++ tailWord_4029938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029938).length < 2 ^ (prefixWord ++ tailWord_4029938).sum := by decide
  have hdescent : baseEnd_4029938 < baseStart_4029938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029981 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4029981 : Nat := 118140960795 + 4029981 * 2 ^ 59
def prefixEnd_4029981 : Nat := 4983230072969 + 3 ^ 40 * 4029981 * 2
def baseEnd_4029981 : Nat := 1379544854324601609669307

theorem tailTrace_4029981 : CollatzResearch.WordTrace tailWord_4029981 prefixEnd_4029981 1379544854324601609669307 := by
  unfold tailWord_4029981
  simp only [CollatzResearch.WordTrace]
  refine ⟨146985482413074577804257797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97990321608716385202838531 146985482413074577804257797)
  ·
    refine ⟨27559777952451483338298337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146985482413074577804257797 27559777952451483338298337)
    ·
      refine ⟨20669833464338612503723753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27559777952451483338298337 20669833464338612503723753)
      ·
        refine ⟨15502375098253959377792815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20669833464338612503723753 15502375098253959377792815)
        ·
          refine ⟨23253562647380939066689223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15502375098253959377792815 23253562647380939066689223)
          ·
            refine ⟨34880343971071408600033835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23253562647380939066689223 34880343971071408600033835)
            ·
              refine ⟨52320515956607112900050753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34880343971071408600033835 52320515956607112900050753)
              ·
                refine ⟨39240386967455334675038065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52320515956607112900050753 39240386967455334675038065)
                ·
                  refine ⟨29430290225591501006278549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39240386967455334675038065 29430290225591501006278549)
                  ·
                    refine ⟨1379544854324601609669307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29430290225591501006278549 1379544854324601609669307)
                    ·
                      rfl

theorem cell22_4029981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4029981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4029981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4029981 prefixEnd_4029981 := by exact prefixLift 4029981
  have htrace : WordTrace (prefixWord ++ tailWord_4029981) baseStart_4029981 baseEnd_4029981 := by
    simpa [prefixWord, tailWord_4029981, baseEnd_4029981] using wordTrace_append hprefix tailTrace_4029981
  have hstable : (prefixWord ++ tailWord_4029981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029981).length < 2 ^ (prefixWord ++ tailWord_4029981).sum := by decide
  have hdescent : baseEnd_4029981 < baseStart_4029981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030013 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 7]
def baseStart_4030013 : Nat := 118140960795 + 4030013 * 2 ^ 59
def prefixEnd_4030013 : Nat := 4983230072969 + 3 ^ 40 * 4030013 * 2
def baseEnd_4030013 : Nat := 459851936192854730956403

theorem tailTrace_4030013 : CollatzResearch.WordTrace tailWord_4030013 prefixEnd_4030013 459851936192854730956403 := by
  unfold tailWord_4030013
  simp only [CollatzResearch.WordTrace]
  refine ⟨146986649548958647269422693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97991099699305764846281795 146986649548958647269422693)
  ·
    refine ⟨27559996790429746363016755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146986649548958647269422693 27559996790429746363016755)
    ·
      refine ⟨41339995185644619544525133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27559996790429746363016755 41339995185644619544525133)
      ·
        refine ⟨15502498194616732329196925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41339995185644619544525133 15502498194616732329196925)
        ·
          refine ⟨5813436822981274623448847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15502498194616732329196925 5813436822981274623448847)
          ·
            refine ⟨8720155234471911935173271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5813436822981274623448847 8720155234471911935173271)
            ·
              refine ⟨13080232851707867902759907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8720155234471911935173271 13080232851707867902759907)
              ·
                refine ⟨19620349277561801854139861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13080232851707867902759907 19620349277561801854139861)
                ·
                  refine ⟨459851936192854730956403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19620349277561801854139861 459851936192854730956403)
                  ·
                    rfl

theorem cell22_4030013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_4030013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030013 prefixEnd_4030013 := by exact prefixLift 4030013
  have htrace : WordTrace (prefixWord ++ tailWord_4030013) baseStart_4030013 baseEnd_4030013 := by
    simpa [prefixWord, tailWord_4030013, baseEnd_4030013] using wordTrace_append hprefix tailTrace_4030013
  have hstable : (prefixWord ++ tailWord_4030013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030013).length < 2 ^ (prefixWord ++ tailWord_4030013).sum := by decide
  have hdescent : baseEnd_4030013 < baseStart_4030013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030073 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 4, 3]
def baseStart_4030073 : Nat := 118140960795 + 4030073 * 2 ^ 59
def prefixEnd_4030073 : Nat := 4983230072969 + 3 ^ 40 * 4030073 * 2
def baseEnd_4030073 : Nat := 1379576347804744036369025

theorem tailTrace_4030073 : CollatzResearch.WordTrace tailWord_4030073 prefixEnd_4030073 1379576347804744036369025 := by
  unfold tailWord_4030073
  simp only [CollatzResearch.WordTrace]
  refine ⟨146988837928741277516606873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97992558619160851677737915 146988837928741277516606873)
  ·
    refine ⟨110241628446555958137455155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146988837928741277516606873 110241628446555958137455155)
    ·
      refine ⟨165362442669833937206182733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110241628446555958137455155 165362442669833937206182733)
      ·
        refine ⟨62010916001187726452318525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165362442669833937206182733 62010916001187726452318525)
        ·
          refine ⟨23254093500445397419619447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62010916001187726452318525 23254093500445397419619447)
          ·
            refine ⟨34881140250668096129429171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23254093500445397419619447 34881140250668096129429171)
            ·
              refine ⟨52321710376002144194143757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34881140250668096129429171 52321710376002144194143757)
              ·
                refine ⟨19620641391000804072803909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52321710376002144194143757 19620641391000804072803909)
                ·
                  refine ⟨3678870260812650763650733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19620641391000804072803909 3678870260812650763650733)
                  ·
                    refine ⟨1379576347804744036369025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3678870260812650763650733 1379576347804744036369025)
                    ·
                      rfl

theorem cell22_4030073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 3].length) (baseStart_4030073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030073 prefixEnd_4030073 := by exact prefixLift 4030073
  have htrace : WordTrace (prefixWord ++ tailWord_4030073) baseStart_4030073 baseEnd_4030073 := by
    simpa [prefixWord, tailWord_4030073, baseEnd_4030073] using wordTrace_append hprefix tailTrace_4030073
  have hstable : (prefixWord ++ tailWord_4030073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030073).length < 2 ^ (prefixWord ++ tailWord_4030073).sum := by decide
  have hdescent : baseEnd_4030073 < baseStart_4030073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030075 : List Nat := [1, 1, 1, 1, 1, 4, 7, 2, 4]
def baseStart_4030075 : Nat := 118140960795 + 4030075 * 2 ^ 59
def prefixEnd_4030075 : Nat := 4983230072969 + 3 ^ 40 * 4030075 * 2
def baseEnd_4030075 : Nat := 459859010815205565939673

theorem tailTrace_4030075 : CollatzResearch.WordTrace tailWord_4030075 prefixEnd_4030075 459859010815205565939673 := by
  unfold tailWord_4030075
  simp only [CollatzResearch.WordTrace]
  refine ⟨146988910874734031858179679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97992607249822687905453119 146988910874734031858179679)
  ·
    refine ⟨220483366312101047787269519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146988910874734031858179679 220483366312101047787269519)
    ·
      refine ⟨330725049468151571680904279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220483366312101047787269519 330725049468151571680904279)
      ·
        refine ⟨496087574202227357521356419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330725049468151571680904279 496087574202227357521356419)
        ·
          refine ⟨744131361303341036282034629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496087574202227357521356419 744131361303341036282034629)
          ·
            refine ⟨139524630244376444302881493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 744131361303341036282034629 139524630244376444302881493)
            ·
              refine ⟨3270108521352572913348785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 139524630244376444302881493 3270108521352572913348785)
              ·
                refine ⟨2452581391014429685011589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270108521352572913348785 2452581391014429685011589)
                ·
                  refine ⟨459859010815205565939673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452581391014429685011589 459859010815205565939673)
                  ·
                    rfl

theorem cell22_4030075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 4].length) (baseStart_4030075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030075 prefixEnd_4030075 := by exact prefixLift 4030075
  have htrace : WordTrace (prefixWord ++ tailWord_4030075) baseStart_4030075 baseEnd_4030075 := by
    simpa [prefixWord, tailWord_4030075, baseEnd_4030075] using wordTrace_append hprefix tailTrace_4030075
  have hstable : (prefixWord ++ tailWord_4030075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030075).length < 2 ^ (prefixWord ++ tailWord_4030075).sum := by decide
  have hdescent : baseEnd_4030075 < baseStart_4030075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030101 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_4030101 : Nat := 118140960795 + 4030101 * 2 ^ 59
def prefixEnd_4030101 : Nat := 4983230072969 + 3 ^ 40 * 4030101 * 2
def baseEnd_4030101 : Nat := 1379585932776961296668939

theorem tailTrace_4030101 : CollatzResearch.WordTrace tailWord_4030101 prefixEnd_4030101 1379585932776961296668939 := by
  unfold tailWord_4030101
  simp only [CollatzResearch.WordTrace]
  refine ⟨146989859172639838298626157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97993239448426558865750771 146989859172639838298626157)
  ·
    refine ⟨55121197189739939361984809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146989859172639838298626157 55121197189739939361984809)
    ·
      refine ⟨41340897892304954521488607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55121197189739939361984809 41340897892304954521488607)
      ·
        refine ⟨62011346838457431782232911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41340897892304954521488607 62011346838457431782232911)
        ·
          refine ⟨93017020257686147673349367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62011346838457431782232911 93017020257686147673349367)
          ·
            refine ⟨139525530386529221510024051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93017020257686147673349367 139525530386529221510024051)
            ·
              refine ⟨209288295579793832265036077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139525530386529221510024051 209288295579793832265036077)
              ·
                refine ⟨78483110842422687099388529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209288295579793832265036077 78483110842422687099388529)
                ·
                  refine ⟨58862333131817015324541397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78483110842422687099388529 58862333131817015324541397)
                  ·
                    refine ⟨1379585932776961296668939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58862333131817015324541397 1379585932776961296668939)
                    ·
                      rfl

theorem cell22_4030101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_4030101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030101 prefixEnd_4030101 := by exact prefixLift 4030101
  have htrace : WordTrace (prefixWord ++ tailWord_4030101) baseStart_4030101 baseEnd_4030101 := by
    simpa [prefixWord, tailWord_4030101, baseEnd_4030101] using wordTrace_append hprefix tailTrace_4030101
  have hstable : (prefixWord ++ tailWord_4030101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030101).length < 2 ^ (prefixWord ++ tailWord_4030101).sum := by decide
  have hdescent : baseEnd_4030101 < baseStart_4030101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030120 : List Nat := [2, 1, 7, 1, 11]
def baseStart_4030120 : Nat := 118140960795 + 4030120 * 2 ^ 59
def prefixEnd_4030120 : Nat := 4983230072969 + 3 ^ 40 * 4030120 * 2
def baseEnd_4030120 : Nat := 5677335131132722553267

theorem tailTrace_4030120 : CollatzResearch.WordTrace tailWord_4030120 prefixEnd_4030120 5677335131132722553267 := by
  unfold tailWord_4030120
  simp only [CollatzResearch.WordTrace]
  refine ⟨73495276079785502271783907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97993701439714003029045209 73495276079785502271783907)
  ·
    refine ⟨110242914119678253407675861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73495276079785502271783907 110242914119678253407675861)
    ·
      refine ⟨2583818299679959064242403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 110242914119678253407675861 2583818299679959064242403)
      ·
        refine ⟨3875727449519938596363605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2583818299679959064242403 3875727449519938596363605)
        ·
          refine ⟨5677335131132722553267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3875727449519938596363605 5677335131132722553267)
          ·
            rfl

theorem cell22_4030120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 11].length) (baseStart_4030120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030120 prefixEnd_4030120 := by exact prefixLift 4030120
  have htrace : WordTrace (prefixWord ++ tailWord_4030120) baseStart_4030120 baseEnd_4030120 := by
    simpa [prefixWord, tailWord_4030120, baseEnd_4030120] using wordTrace_append hprefix tailTrace_4030120
  have hstable : (prefixWord ++ tailWord_4030120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030120).length < 2 ^ (prefixWord ++ tailWord_4030120).sum := by decide
  have hdescent : baseEnd_4030120 < baseStart_4030120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030126 : List Nat := [4, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_4030126 : Nat := 118140960795 + 4030126 * 2 ^ 59
def prefixEnd_4030126 : Nat := 4983230072969 + 3 ^ 40 * 4030126 * 2
def baseEnd_4030126 : Nat := 459864830262623188264621

theorem tailTrace_4030126 : CollatzResearch.WordTrace tailWord_4030126 prefixEnd_4030126 459864830262623188264621 := by
  unfold tailWord_4030126
  simp only [CollatzResearch.WordTrace]
  refine ⟨18373846374693658446035779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97993847331699511712190821 18373846374693658446035779)
  ·
    refine ⟨27560769562040487669053669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18373846374693658446035779 27560769562040487669053669)
    ·
      refine ⟨5167644292882591437947563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27560769562040487669053669 5167644292882591437947563)
      ·
        refine ⟨7751466439323887156921345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5167644292882591437947563 7751466439323887156921345)
        ·
          refine ⟨5813599829492915367691009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7751466439323887156921345 5813599829492915367691009)
          ·
            refine ⟨4360199872119686525768257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5813599829492915367691009 4360199872119686525768257)
            ·
              refine ⟨3270149904089764894326193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4360199872119686525768257 3270149904089764894326193)
              ·
                refine ⟨2452612428067323670744645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270149904089764894326193 2452612428067323670744645)
                ·
                  refine ⟨459864830262623188264621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452612428067323670744645 459864830262623188264621)
                  ·
                    rfl

theorem cell22_4030126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_4030126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030126 prefixEnd_4030126 := by exact prefixLift 4030126
  have htrace : WordTrace (prefixWord ++ tailWord_4030126) baseStart_4030126 baseEnd_4030126 := by
    simpa [prefixWord, tailWord_4030126, baseEnd_4030126] using wordTrace_append hprefix tailTrace_4030126
  have hstable : (prefixWord ++ tailWord_4030126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030126).length < 2 ^ (prefixWord ++ tailWord_4030126).sum := by decide
  have hdescent : baseEnd_4030126 < baseStart_4030126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030193 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 6]
def baseStart_4030193 : Nat := 118140960795 + 4030193 * 2 ^ 59
def prefixEnd_4030193 : Nat := 4983230072969 + 3 ^ 40 * 4030193 * 2
def baseEnd_4030193 : Nat := 459872475419034574456219

theorem tailTrace_4030193 : CollatzResearch.WordTrace tailWord_4030193 prefixEnd_4030193 459872475419034574456219 := by
  unfold tailWord_4030193
  simp only [CollatzResearch.WordTrace]
  refine ⟨146993214688306538010975233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97995476458871025340650155 146993214688306538010975233)
  ·
    refine ⟨110244911016229903508231425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146993214688306538010975233 110244911016229903508231425)
    ·
      refine ⟨82683683262172427631173569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110244911016229903508231425 82683683262172427631173569)
      ·
        refine ⟨62012762446629320723380177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82683683262172427631173569 62012762446629320723380177)
        ·
          refine ⟨46509571834971990542535133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62012762446629320723380177 46509571834971990542535133)
          ·
            refine ⟨17441089438114496453450675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46509571834971990542535133 17441089438114496453450675)
            ·
              refine ⟨26161634157171744680176013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17441089438114496453450675 26161634157171744680176013)
              ·
                refine ⟨9810612808939404255066005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26161634157171744680176013 9810612808939404255066005)
                ·
                  refine ⟨459872475419034574456219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9810612808939404255066005 459872475419034574456219)
                  ·
                    rfl

theorem cell22_4030193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_4030193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030193 prefixEnd_4030193 := by exact prefixLift 4030193
  have htrace : WordTrace (prefixWord ++ tailWord_4030193) baseStart_4030193 baseEnd_4030193 := by
    simpa [prefixWord, tailWord_4030193, baseEnd_4030193] using wordTrace_append hprefix tailTrace_4030193
  have hstable : (prefixWord ++ tailWord_4030193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030193).length < 2 ^ (prefixWord ++ tailWord_4030193).sum := by decide
  have hdescent : baseEnd_4030193 < baseStart_4030193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030210 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4030210 : Nat := 118140960795 + 4030210 * 2 ^ 59
def prefixEnd_4030210 : Nat := 4983230072969 + 3 ^ 40 * 4030210 * 2
def baseEnd_4030210 : Nat := 459874415234840448564535

theorem tailTrace_4030210 : CollatzResearch.WordTrace tailWord_4030210 prefixEnd_4030210 459874415234840448564535 := by
  unfold tailWord_4030210
  simp only [CollatzResearch.WordTrace]
  refine ⟨36748458682311237478586021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97995889819496633276229389 36748458682311237478586021)
  ·
    refine ⟨6890336002933357027234879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36748458682311237478586021 6890336002933357027234879)
    ·
      refine ⟨10335504004400035540852319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6890336002933357027234879 10335504004400035540852319)
      ·
        refine ⟨15503256006600053311278479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335504004400035540852319 15503256006600053311278479)
        ·
          refine ⟨23254884009900079966917719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15503256006600053311278479 23254884009900079966917719)
          ·
            refine ⟨34882326014850119950376579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23254884009900079966917719 34882326014850119950376579)
            ·
              refine ⟨52323489022275179925564869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34882326014850119950376579 52323489022275179925564869)
              ·
                refine ⟨9810654191676596236043413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52323489022275179925564869 9810654191676596236043413)
                ·
                  refine ⟨459874415234840448564535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9810654191676596236043413 459874415234840448564535)
                  ·
                    rfl

theorem cell22_4030210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4030210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030210 prefixEnd_4030210 := by exact prefixLift 4030210
  have htrace : WordTrace (prefixWord ++ tailWord_4030210) baseStart_4030210 baseEnd_4030210 := by
    simpa [prefixWord, tailWord_4030210, baseEnd_4030210] using wordTrace_append hprefix tailTrace_4030210
  have hstable : (prefixWord ++ tailWord_4030210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030210).length < 2 ^ (prefixWord ++ tailWord_4030210).sum := by decide
  have hdescent : baseEnd_4030210 < baseStart_4030210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030212 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_4030212 : Nat := 118140960795 + 4030212 * 2 ^ 59
def prefixEnd_4030212 : Nat := 4983230072969 + 3 ^ 40 * 4030212 * 2
def baseEnd_4030212 : Nat := 1379623930345394007143599

theorem tailTrace_4030212 : CollatzResearch.WordTrace tailWord_4030212 prefixEnd_4030212 1379623930345394007143599 := by
  unfold tailWord_4030212
  simp only [CollatzResearch.WordTrace]
  refine ⟨73496953837618852127958445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97995938450158469503944593 73496953837618852127958445)
  ·
    refine ⟨27561357689107069547984417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73496953837618852127958445 27561357689107069547984417)
    ·
      refine ⟨20671018266830302160988313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27561357689107069547984417 20671018266830302160988313)
      ·
        refine ⟨15503263700122726620741235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20671018266830302160988313 15503263700122726620741235)
        ·
          refine ⟨23254895550184089931111853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15503263700122726620741235 23254895550184089931111853)
          ·
            refine ⟨8720585831319033724166945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23254895550184089931111853 8720585831319033724166945)
            ·
              refine ⟨6540439373489275293125209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8720585831319033724166945 6540439373489275293125209)
              ·
                refine ⟨4905329530116956469843907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6540439373489275293125209 4905329530116956469843907)
                ·
                  refine ⟨7357994295175434704765861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905329530116956469843907 7357994295175434704765861)
                  ·
                    refine ⟨1379623930345394007143599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357994295175434704765861 1379623930345394007143599)
                    ·
                      rfl

theorem cell22_4030212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_4030212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030212 prefixEnd_4030212 := by exact prefixLift 4030212
  have htrace : WordTrace (prefixWord ++ tailWord_4030212) baseStart_4030212 baseEnd_4030212 := by
    simpa [prefixWord, tailWord_4030212, baseEnd_4030212] using wordTrace_append hprefix tailTrace_4030212
  have hstable : (prefixWord ++ tailWord_4030212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030212).length < 2 ^ (prefixWord ++ tailWord_4030212).sum := by decide
  have hdescent : baseEnd_4030212 < baseStart_4030212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030240 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_4030240 : Nat := 118140960795 + 4030240 * 2 ^ 59
def prefixEnd_4030240 : Nat := 4983230072969 + 3 ^ 40 * 4030240 * 2
def baseEnd_4030240 : Nat := 1379633515317611267443513

theorem tailTrace_4030240 : CollatzResearch.WordTrace tailWord_4030240 prefixEnd_4030240 1379633515317611267443513 := by
  unfold tailWord_4030240
  simp only [CollatzResearch.WordTrace]
  refine ⟨73497464459568132518968087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97996619279424176691957449 73497464459568132518968087)
  ·
    refine ⟨110246196689352198778452131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73497464459568132518968087 110246196689352198778452131)
    ·
      refine ⟨165369295034028298167678197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110246196689352198778452131 165369295034028298167678197)
      ·
        refine ⟨15503371409440152953219831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165369295034028298167678197 15503371409440152953219831)
        ·
          refine ⟨23255057114160229429829747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15503371409440152953219831 23255057114160229429829747)
          ·
            refine ⟨34882585671240344144744621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23255057114160229429829747 34882585671240344144744621)
            ·
              refine ⟨13080969626715129054279233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34882585671240344144744621 13080969626715129054279233)
              ·
                refine ⟨9810727220036346790709425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13080969626715129054279233 9810727220036346790709425)
                ·
                  refine ⟨7358045415027260093032069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9810727220036346790709425 7358045415027260093032069)
                  ·
                    refine ⟨1379633515317611267443513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7358045415027260093032069 1379633515317611267443513)
                    ·
                      rfl

theorem cell22_4030240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_4030240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030240 prefixEnd_4030240 := by exact prefixLift 4030240
  have htrace : WordTrace (prefixWord ++ tailWord_4030240) baseStart_4030240 baseEnd_4030240 := by
    simpa [prefixWord, tailWord_4030240, baseEnd_4030240] using wordTrace_append hprefix tailTrace_4030240
  have hstable : (prefixWord ++ tailWord_4030240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030240).length < 2 ^ (prefixWord ++ tailWord_4030240).sum := by decide
  have hdescent : baseEnd_4030240 < baseStart_4030240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030242 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_4030242 : Nat := 118140960795 + 4030242 * 2 ^ 59
def prefixEnd_4030242 : Nat := 4983230072969 + 3 ^ 40 * 4030242 * 2
def baseEnd_4030242 : Nat := 1379634199958483928893507

theorem tailTrace_4030242 : CollatzResearch.WordTrace tailWord_4030242 prefixEnd_4030242 1379634199958483928893507 := by
  unfold tailWord_4030242
  simp only [CollatzResearch.WordTrace]
  refine ⟨36748750466282254844877245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97996667910086012919672653 36748750466282254844877245)
  ·
    refine ⟨13780781424855845566828967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36748750466282254844877245 13780781424855845566828967)
    ·
      refine ⟨20671172137283768350243451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13780781424855845566828967 20671172137283768350243451)
      ·
        refine ⟨31006758205925652525365177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20671172137283768350243451 31006758205925652525365177)
        ·
          refine ⟨23255068654444239394023883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31006758205925652525365177 23255068654444239394023883)
          ·
            refine ⟨34882602981666359091035825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23255068654444239394023883 34882602981666359091035825)
            ·
              refine ⟨26161952236249769318276869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34882602981666359091035825 26161952236249769318276869)
              ·
                refine ⟨4905366044296831747176913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26161952236249769318276869 4905366044296831747176913)
                ·
                  refine ⟨3679024533222623810382685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4905366044296831747176913 3679024533222623810382685)
                  ·
                    refine ⟨1379634199958483928893507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679024533222623810382685 1379634199958483928893507)
                    ·
                      rfl

theorem cell22_4030242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_4030242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030242 prefixEnd_4030242 := by exact prefixLift 4030242
  have htrace : WordTrace (prefixWord ++ tailWord_4030242) baseStart_4030242 baseEnd_4030242 := by
    simpa [prefixWord, tailWord_4030242, baseEnd_4030242] using wordTrace_append hprefix tailTrace_4030242
  have hstable : (prefixWord ++ tailWord_4030242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030242).length < 2 ^ (prefixWord ++ tailWord_4030242).sum := by decide
  have hdescent : baseEnd_4030242 < baseStart_4030242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030244 : List Nat := [2, 3, 1, 3, 2, 2, 3, 2, 4]
def baseStart_4030244 : Nat := 118140960795 + 4030244 * 2 ^ 59
def prefixEnd_4030244 : Nat := 4983230072969 + 3 ^ 40 * 4030244 * 2
def baseEnd_4030244 : Nat := 459878294866452196781167

theorem tailTrace_4030244 : CollatzResearch.WordTrace tailWord_4030244 prefixEnd_4030244 459878294866452196781167 := by
  unfold tailWord_4030244
  simp only [CollatzResearch.WordTrace]
  refine ⟨73497537405560886860540893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97996716540747849147387857 73497537405560886860540893)
  ·
    refine ⟨27561576527085332572702835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73497537405560886860540893 27561576527085332572702835)
    ·
      refine ⟨41342364790627998859054253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27561576527085332572702835 41342364790627998859054253)
      ·
        refine ⟨15503386796485499572145345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41342364790627998859054253 15503386796485499572145345)
        ·
          refine ⟨11627540097364124679109009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15503386796485499572145345 11627540097364124679109009)
          ·
            refine ⟨8720655073023093509331757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11627540097364124679109009 8720655073023093509331757)
            ·
              refine ⟨3270245652383660065999409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8720655073023093509331757 3270245652383660065999409)
              ·
                refine ⟨2452684239287745049499557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270245652383660065999409 2452684239287745049499557)
                ·
                  refine ⟨459878294866452196781167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452684239287745049499557 459878294866452196781167)
                  ·
                    rfl

theorem cell22_4030244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_4030244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030244 prefixEnd_4030244 := by exact prefixLift 4030244
  have htrace : WordTrace (prefixWord ++ tailWord_4030244) baseStart_4030244 baseEnd_4030244 := by
    simpa [prefixWord, tailWord_4030244, baseEnd_4030244] using wordTrace_append hprefix tailTrace_4030244
  have hstable : (prefixWord ++ tailWord_4030244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030244).length < 2 ^ (prefixWord ++ tailWord_4030244).sum := by decide
  have hdescent : baseEnd_4030244 < baseStart_4030244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030304 : List Nat := [2, 1, 1, 3, 3, 3, 1, 4, 1, 3]
def baseStart_4030304 : Nat := 118140960795 + 4030304 * 2 ^ 59
def prefixEnd_4030304 : Nat := 4983230072969 + 3 ^ 40 * 4030304 * 2
def baseEnd_4030304 : Nat := 1379655423825536433843317

theorem tailTrace_4030304 : CollatzResearch.WordTrace tailWord_4030304 prefixEnd_4030304 1379655423825536433843317 := by
  unfold tailWord_4030304
  simp only [CollatzResearch.WordTrace]
  refine ⟨73498631595452201984132983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97998175460602935978843977 73498631595452201984132983)
  ·
    refine ⟨110247947393178302976199475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73498631595452201984132983 110247947393178302976199475)
    ·
      refine ⟨165371921089767454464299213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110247947393178302976199475 165371921089767454464299213)
      ·
        refine ⟨62014470408662795424112205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165371921089767454464299213 62014470408662795424112205)
        ·
          refine ⟨23255426403248548284042077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62014470408662795424112205 23255426403248548284042077)
          ·
            refine ⟨8720784901218205606515779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23255426403248548284042077 8720784901218205606515779)
            ·
              refine ⟨13081177351827308409773669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8720784901218205606515779 13081177351827308409773669)
              ·
                refine ⟨2452720753467620326832563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13081177351827308409773669 2452720753467620326832563)
                ·
                  refine ⟨3679081130201430490248845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452720753467620326832563 3679081130201430490248845)
                  ·
                    refine ⟨1379655423825536433843317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679081130201430490248845 1379655423825536433843317)
                    ·
                      rfl

theorem cell22_4030304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 1, 3].length) (baseStart_4030304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030304 prefixEnd_4030304 := by exact prefixLift 4030304
  have htrace : WordTrace (prefixWord ++ tailWord_4030304) baseStart_4030304 baseEnd_4030304 := by
    simpa [prefixWord, tailWord_4030304, baseEnd_4030304] using wordTrace_append hprefix tailTrace_4030304
  have hstable : (prefixWord ++ tailWord_4030304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030304).length < 2 ^ (prefixWord ++ tailWord_4030304).sum := by decide
  have hdescent : baseEnd_4030304 < baseStart_4030304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030330 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_4030330 : Nat := 118140960795 + 4030330 * 2 ^ 59
def prefixEnd_4030330 : Nat := 4983230072969 + 3 ^ 40 * 4030330 * 2
def baseEnd_4030330 : Nat := 1379664324156881032693237

theorem tailTrace_4030330 : CollatzResearch.WordTrace tailWord_4030330 prefixEnd_4030330 1379664324156881032693237 := by
  unfold tailWord_4030330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36749552872202552602178111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97998807659206806939141629 36749552872202552602178111)
  ·
    refine ⟨55124329308303828903267167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36749552872202552602178111 55124329308303828903267167)
    ·
      refine ⟨82686493962455743354900751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55124329308303828903267167 82686493962455743354900751)
      ·
        refine ⟨124029740943683615032351127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82686493962455743354900751 124029740943683615032351127)
        ·
          refine ⟨186044611415525422548526691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124029740943683615032351127 186044611415525422548526691)
          ·
            refine ⟨279066917123288133822790037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186044611415525422548526691 279066917123288133822790037)
            ·
              refine ⟨13081261740154131272943283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 279066917123288133822790037 13081261740154131272943283)
              ·
                refine ⟨19621892610231196909414925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13081261740154131272943283 19621892610231196909414925)
                ·
                  refine ⟨7358209728836698841030597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19621892610231196909414925 7358209728836698841030597)
                  ·
                    refine ⟨1379664324156881032693237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7358209728836698841030597 1379664324156881032693237)
                    ·
                      rfl

theorem cell22_4030330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_4030330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030330 prefixEnd_4030330 := by exact prefixLift 4030330
  have htrace : WordTrace (prefixWord ++ tailWord_4030330) baseStart_4030330 baseEnd_4030330 := by
    simpa [prefixWord, tailWord_4030330, baseEnd_4030330] using wordTrace_append hprefix tailTrace_4030330
  have hstable : (prefixWord ++ tailWord_4030330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030330).length < 2 ^ (prefixWord ++ tailWord_4030330).sum := by decide
  have hdescent : baseEnd_4030330 < baseStart_4030330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030362 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_4030362 : Nat := 118140960795 + 4030362 * 2 ^ 59
def prefixEnd_4030362 : Nat := 4983230072969 + 3 ^ 40 * 4030362 * 2
def baseEnd_4030362 : Nat := 459891759470281205297713

theorem tailTrace_4030362 : CollatzResearch.WordTrace tailWord_4030362 prefixEnd_4030362 459891759470281205297713 := by
  unfold tailWord_4030362
  simp only [CollatzResearch.WordTrace]
  refine ⟨36749844656173569968469335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97999585749796186582584893 36749844656173569968469335)
  ·
    refine ⟨55124766984260354952704003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36749844656173569968469335 55124766984260354952704003)
    ·
      refine ⟨82687150476390532429056005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55124766984260354952704003 82687150476390532429056005)
      ·
        refine ⟨15503840714323224830448001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82687150476390532429056005 15503840714323224830448001)
        ·
          refine ⟨11627880535742418622836001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15503840714323224830448001 11627880535742418622836001)
          ·
            refine ⟨8720910401806813967127001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11627880535742418622836001 8720910401806813967127001)
            ·
              refine ⟨6540682801355110475345251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8720910401806813967127001 6540682801355110475345251)
              ·
                refine ⟨9811024202032665713017877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540682801355110475345251 9811024202032665713017877)
                ·
                  refine ⟨459891759470281205297713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9811024202032665713017877 459891759470281205297713)
                  ·
                    rfl

theorem cell22_4030362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_4030362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030362 prefixEnd_4030362 := by exact prefixLift 4030362
  have htrace : WordTrace (prefixWord ++ tailWord_4030362) baseStart_4030362 baseEnd_4030362 := by
    simpa [prefixWord, tailWord_4030362, baseEnd_4030362] using wordTrace_append hprefix tailTrace_4030362
  have hstable : (prefixWord ++ tailWord_4030362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030362).length < 2 ^ (prefixWord ++ tailWord_4030362).sum := by decide
  have hdescent : baseEnd_4030362 < baseStart_4030362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030512 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_4030512 : Nat := 118140960795 + 4030512 * 2 ^ 59
def prefixEnd_4030512 : Nat := 4983230072969 + 3 ^ 40 * 4030512 * 2
def baseEnd_4030512 : Nat := 1379726626476293224642679

theorem tailTrace_4030512 : CollatzResearch.WordTrace tailWord_4030512 prefixEnd_4030512 1379726626476293224642679 := by
  unfold tailWord_4030512
  simp only [CollatzResearch.WordTrace]
  refine ⟨73502424787075427745918895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98003233049433903661225193 73502424787075427745918895)
  ·
    refine ⟨110253637180613141618878343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73502424787075427745918895 110253637180613141618878343)
    ·
      refine ⟨165380455770919712428317515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110253637180613141618878343 165380455770919712428317515)
      ·
        refine ⟨248070683656379568642476273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165380455770919712428317515 248070683656379568642476273)
        ·
          refine ⟨186053012742284676481857205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248070683656379568642476273 186053012742284676481857205)
          ·
            refine ⟨17442469944589188420174113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186053012742284676481857205 17442469944589188420174113)
            ·
              refine ⟨13081852458441891315130585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17442469944589188420174113 13081852458441891315130585)
              ·
                refine ⟨9811389343831418486347939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13081852458441891315130585 9811389343831418486347939)
                ·
                  refine ⟨14717084015747127729521909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9811389343831418486347939 14717084015747127729521909)
                  ·
                    refine ⟨1379726626476293224642679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14717084015747127729521909 1379726626476293224642679)
                    ·
                      rfl

theorem cell22_4030512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_4030512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030512 prefixEnd_4030512 := by exact prefixLift 4030512
  have htrace : WordTrace (prefixWord ++ tailWord_4030512) baseStart_4030512 baseEnd_4030512 := by
    simpa [prefixWord, tailWord_4030512, baseEnd_4030512] using wordTrace_append hprefix tailTrace_4030512
  have hstable : (prefixWord ++ tailWord_4030512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030512).length < 2 ^ (prefixWord ++ tailWord_4030512).sum := by decide
  have hdescent : baseEnd_4030512 < baseStart_4030512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030514 : List Nat := [3, 2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_4030514 : Nat := 118140960795 + 4030514 * 2 ^ 59
def prefixEnd_4030514 : Nat := 4983230072969 + 3 ^ 40 * 4030514 * 2
def baseEnd_4030514 : Nat := 459909103705721962030891

theorem tailTrace_4030514 : CollatzResearch.WordTrace tailWord_4030514 prefixEnd_4030514 459909103705721962030891 := by
  unfold tailWord_4030514
  simp only [CollatzResearch.WordTrace]
  refine ⟨36751230630035902458352649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98003281680095739888940397 36751230630035902458352649)
  ·
    refine ⟨27563422972526926843764487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36751230630035902458352649 27563422972526926843764487)
    ·
      refine ⟨41345134458790390265646731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27563422972526926843764487 41345134458790390265646731)
      ·
        refine ⟨62017701688185585398470097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41345134458790390265646731 62017701688185585398470097)
        ·
          refine ⟨46513276266139189048852573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62017701688185585398470097 46513276266139189048852573)
          ·
            refine ⟨17442478599802195893319715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46513276266139189048852573 17442478599802195893319715)
            ·
              refine ⟨26163717899703293839979573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17442478599802195893319715 26163717899703293839979573)
              ·
                refine ⟨2452848553097183797498085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26163717899703293839979573 2452848553097183797498085)
                ·
                  refine ⟨459909103705721962030891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452848553097183797498085 459909103705721962030891)
                  ·
                    rfl

theorem cell22_4030514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_4030514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030514 prefixEnd_4030514 := by exact prefixLift 4030514
  have htrace : WordTrace (prefixWord ++ tailWord_4030514) baseStart_4030514 baseEnd_4030514 := by
    simpa [prefixWord, tailWord_4030514, baseEnd_4030514] using wordTrace_append hprefix tailTrace_4030514
  have hstable : (prefixWord ++ tailWord_4030514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030514).length < 2 ^ (prefixWord ++ tailWord_4030514).sum := by decide
  have hdescent : baseEnd_4030514 < baseStart_4030514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030527 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 2, 4]
def baseStart_4030527 : Nat := 118140960795 + 4030527 * 2 ^ 59
def prefixEnd_4030527 : Nat := 4983230072969 + 3 ^ 40 * 4030527 * 2
def baseEnd_4030527 : Nat := 1379731761282838185517633

theorem tailTrace_4030527 : CollatzResearch.WordTrace tailWord_4030527 prefixEnd_4030527 1379731761282838185517633 := by
  unfold tailWord_4030527
  simp only [CollatzResearch.WordTrace]
  refine ⟨147005396669096513053633835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98003597779397675369089223 147005396669096513053633835)
  ·
    refine ⟨220508095003644769580450753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147005396669096513053633835 220508095003644769580450753)
    ·
      refine ⟨165381071252733577185338065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220508095003644769580450753 165381071252733577185338065)
      ·
        refine ⟨124035803439550182889003549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165381071252733577185338065 124035803439550182889003549)
        ·
          refine ⟨46513426289831318583376331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124035803439550182889003549 46513426289831318583376331)
          ·
            refine ⟨69770139434746977875064497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46513426289831318583376331 69770139434746977875064497)
            ·
              refine ⟨52327604576060233406298373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69770139434746977875064497 52327604576060233406298373)
              ·
                refine ⟨9811425858011293763680945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52327604576060233406298373 9811425858011293763680945)
                ·
                  refine ⟨7358569393508470322760709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9811425858011293763680945 7358569393508470322760709)
                  ·
                    refine ⟨1379731761282838185517633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7358569393508470322760709 1379731761282838185517633)
                    ·
                      rfl

theorem cell22_4030527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_4030527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030527 prefixEnd_4030527 := by exact prefixLift 4030527
  have htrace : WordTrace (prefixWord ++ tailWord_4030527) baseStart_4030527 baseEnd_4030527 := by
    simpa [prefixWord, tailWord_4030527, baseEnd_4030527] using wordTrace_append hprefix tailTrace_4030527
  have hstable : (prefixWord ++ tailWord_4030527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030527).length < 2 ^ (prefixWord ++ tailWord_4030527).sum := by decide
  have hdescent : baseEnd_4030527 < baseStart_4030527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030546 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_4030546 : Nat := 118140960795 + 4030546 * 2 ^ 59
def prefixEnd_4030546 : Nat := 4983230072969 + 3 ^ 40 * 4030546 * 2
def baseEnd_4030546 : Nat := 1379738265371128469292575

theorem tailTrace_4030546 : CollatzResearch.WordTrace tailWord_4030546 prefixEnd_4030546 1379738265371128469292575 := by
  unfold tailWord_4030546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36751522414006919824643873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98004059770685119532383661 36751522414006919824643873)
  ·
    refine ⟨27563641810505189868482905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36751522414006919824643873 27563641810505189868482905)
    ·
      refine ⟨20672731357878892401362179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27563641810505189868482905 20672731357878892401362179)
      ·
        refine ⟨31009097036818338602043269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20672731357878892401362179 31009097036818338602043269)
        ·
          refine ⟨5814205694403438487883113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31009097036818338602043269 5814205694403438487883113)
          ·
            refine ⟨4360654270802578865912335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5814205694403438487883113 4360654270802578865912335)
            ·
              refine ⟨6540981406203868298868503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360654270802578865912335 6540981406203868298868503)
              ·
                refine ⟨9811472109305802448302755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540981406203868298868503 9811472109305802448302755)
                ·
                  refine ⟨14717208163958703672454133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9811472109305802448302755 14717208163958703672454133)
                  ·
                    refine ⟨1379738265371128469292575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14717208163958703672454133 1379738265371128469292575)
                    ·
                      rfl

theorem cell22_4030546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_4030546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030546 prefixEnd_4030546 := by exact prefixLift 4030546
  have htrace : WordTrace (prefixWord ++ tailWord_4030546) baseStart_4030546 baseEnd_4030546 := by
    simpa [prefixWord, tailWord_4030546, baseEnd_4030546] using wordTrace_append hprefix tailTrace_4030546
  have hstable : (prefixWord ++ tailWord_4030546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030546).length < 2 ^ (prefixWord ++ tailWord_4030546).sum := by decide
  have hdescent : baseEnd_4030546 < baseStart_4030546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030664 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 6, 3]
def baseStart_4030664 : Nat := 118140960795 + 4030664 * 2 ^ 59
def prefixEnd_4030664 : Nat := 4983230072969 + 3 ^ 40 * 4030664 * 2
def baseEnd_4030664 : Nat := 1379778659182615494842213

theorem tailTrace_4030664 : CollatzResearch.WordTrace tailWord_4030664 prefixEnd_4030664 1379778659182615494842213 := by
  unfold tailWord_4030664
  simp only [CollatzResearch.WordTrace]
  refine ⟨73505196734800092725685523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98006928979733456967580697 73505196734800092725685523)
  ·
    refine ⟨110257795102200139088528285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73505196734800092725685523 110257795102200139088528285)
    ·
      refine ⟨41346673163325052158198107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110257795102200139088528285 41346673163325052158198107)
      ·
        refine ⟨62020009744987578237297161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41346673163325052158198107 62020009744987578237297161)
        ·
          refine ⟨46515007308740683677972871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62020009744987578237297161 46515007308740683677972871)
          ·
            refine ⟨69772510963111025516959307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46515007308740683677972871 69772510963111025516959307)
            ·
              refine ⟨104658766444666538275438961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69772510963111025516959307 104658766444666538275438961)
              ·
                refine ⟨78494074833499903706579221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104658766444666538275438961 78494074833499903706579221)
                ·
                  refine ⟨3679409757820307986245901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78494074833499903706579221 3679409757820307986245901)
                  ·
                    refine ⟨1379778659182615494842213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679409757820307986245901 1379778659182615494842213)
                    ·
                      rfl

theorem cell22_4030664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_4030664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030664 prefixEnd_4030664 := by exact prefixLift 4030664
  have htrace : WordTrace (prefixWord ++ tailWord_4030664) baseStart_4030664 baseEnd_4030664 := by
    simpa [prefixWord, tailWord_4030664, baseEnd_4030664] using wordTrace_append hprefix tailTrace_4030664
  have hstable : (prefixWord ++ tailWord_4030664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030664).length < 2 ^ (prefixWord ++ tailWord_4030664).sum := by decide
  have hdescent : baseEnd_4030664 < baseStart_4030664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030685 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_4030685 : Nat := 118140960795 + 4030685 * 2 ^ 59
def prefixEnd_4030685 : Nat := 4983230072969 + 3 ^ 40 * 4030685 * 2
def baseEnd_4030685 : Nat := 1379785847911778440067149

theorem tailTrace_4030685 : CollatzResearch.WordTrace tailWord_4030685 prefixEnd_4030685 1379785847911778440067149 := by
  unfold tailWord_4030685
  simp only [CollatzResearch.WordTrace]
  refine ⟨147011159402524106037885509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98007439601682737358590339 147011159402524106037885509)
  ·
    refine ⟨27564592387973269882103533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147011159402524106037885509 27564592387973269882103533)
    ·
      refine ⟨10336722145489976205788825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27564592387973269882103533 10336722145489976205788825)
      ·
        refine ⟨7752541609117482154341619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10336722145489976205788825 7752541609117482154341619)
        ·
          refine ⟨11628812413676223231512429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7752541609117482154341619 11628812413676223231512429)
          ·
            refine ⟨4360804655128583711817161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11628812413676223231512429 4360804655128583711817161)
            ·
              refine ⟨3270603491346437783862871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4360804655128583711817161 3270603491346437783862871)
              ·
                refine ⟨4905905237019656675794307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270603491346437783862871 4905905237019656675794307)
                ·
                  refine ⟨7358857855529485013691461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905905237019656675794307 7358857855529485013691461)
                  ·
                    refine ⟨1379785847911778440067149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7358857855529485013691461 1379785847911778440067149)
                    ·
                      rfl

theorem cell22_4030685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_4030685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030685 prefixEnd_4030685 := by exact prefixLift 4030685
  have htrace : WordTrace (prefixWord ++ tailWord_4030685) baseStart_4030685 baseEnd_4030685 := by
    simpa [prefixWord, tailWord_4030685, baseEnd_4030685] using wordTrace_append hprefix tailTrace_4030685
  have hstable : (prefixWord ++ tailWord_4030685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030685).length < 2 ^ (prefixWord ++ tailWord_4030685).sum := by decide
  have hdescent : baseEnd_4030685 < baseStart_4030685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030760 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 3, 3]
def baseStart_4030760 : Nat := 118140960795 + 4030760 * 2 ^ 59
def prefixEnd_4030760 : Nat := 4983230072969 + 3 ^ 40 * 4030760 * 2
def baseEnd_4030760 : Nat := 1379811521944503244441919

theorem tailTrace_4030760 : CollatzResearch.WordTrace tailWord_4030760 prefixEnd_4030760 1379811521944503244441919 := by
  unfold tailWord_4030760
  simp only [CollatzResearch.WordTrace]
  refine ⟨73506947438626196923432867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98009263251501595897910489 73506947438626196923432867)
  ·
    refine ⟨110260421157939295385149301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73506947438626196923432867 110260421157939295385149301)
    ·
      refine ⟨10336914483556808942357747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110260421157939295385149301 10336914483556808942357747)
      ·
        refine ⟨15505371725335213413536621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10336914483556808942357747 15505371725335213413536621)
        ·
          refine ⟨5814514397000705030076233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15505371725335213413536621 5814514397000705030076233)
          ·
            refine ⟨4360885797750528772557175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5814514397000705030076233 4360885797750528772557175)
            ·
              refine ⟨6541328696625793158835763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360885797750528772557175 6541328696625793158835763)
              ·
                refine ⟨9811993044938689738253645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6541328696625793158835763 9811993044938689738253645)
                ·
                  refine ⟨3679497391852008651845117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9811993044938689738253645 3679497391852008651845117)
                  ·
                    refine ⟨1379811521944503244441919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679497391852008651845117 1379811521944503244441919)
                    ·
                      rfl

theorem cell22_4030760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_4030760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030760 prefixEnd_4030760 := by exact prefixLift 4030760
  have htrace : WordTrace (prefixWord ++ tailWord_4030760) baseStart_4030760 baseEnd_4030760 := by
    simpa [prefixWord, tailWord_4030760, baseEnd_4030760] using wordTrace_append hprefix tailTrace_4030760
  have hstable : (prefixWord ++ tailWord_4030760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030760).length < 2 ^ (prefixWord ++ tailWord_4030760).sum := by decide
  have hdescent : baseEnd_4030760 < baseStart_4030760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030844 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_4030844 : Nat := 118140960795 + 4030844 * 2 ^ 59
def prefixEnd_4030844 : Nat := 4983230072969 + 3 ^ 40 * 4030844 * 2
def baseEnd_4030844 : Nat := 1379840276861155025341661

theorem tailTrace_4030844 : CollatzResearch.WordTrace tailWord_4030844 prefixEnd_4030844 1379840276861155025341661 := by
  unfold tailWord_4030844
  simp only [CollatzResearch.WordTrace]
  refine ⟨73508479304474038096461793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98011305739298717461949057 73508479304474038096461793)
  ·
    refine ⟨55131359478355528572346345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73508479304474038096461793 55131359478355528572346345)
    ·
      refine ⟨41348519608766646429259759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55131359478355528572346345 41348519608766646429259759)
      ·
        refine ⟨62022779413149969643889639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41348519608766646429259759 62022779413149969643889639)
        ·
          refine ⟨93034169119724954465834459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62022779413149969643889639 93034169119724954465834459)
          ·
            refine ⟨139551253679587431698751689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93034169119724954465834459 139551253679587431698751689)
            ·
              refine ⟨104663440259690573774063767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139551253679587431698751689 104663440259690573774063767)
              ·
                refine ⟨156995160389535860661095651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104663440259690573774063767 156995160389535860661095651)
                ·
                  refine ⟨235492740584303790991643477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156995160389535860661095651 235492740584303790991643477)
                  ·
                    refine ⟨1379840276861155025341661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 235492740584303790991643477 1379840276861155025341661)
                    ·
                      rfl

theorem cell22_4030844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_4030844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030844 prefixEnd_4030844 := by exact prefixLift 4030844
  have htrace : WordTrace (prefixWord ++ tailWord_4030844) baseStart_4030844 baseEnd_4030844 := by
    simpa [prefixWord, tailWord_4030844, baseEnd_4030844] using wordTrace_append hprefix tailTrace_4030844
  have hstable : (prefixWord ++ tailWord_4030844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030844).length < 2 ^ (prefixWord ++ tailWord_4030844).sum := by decide
  have hdescent : baseEnd_4030844 < baseStart_4030844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030987 : List Nat := [1, 1, 1, 1, 7, 3, 2, 2, 4]
def baseStart_4030987 : Nat := 118140960795 + 4030987 * 2 ^ 59
def prefixEnd_4030987 : Nat := 4983230072969 + 3 ^ 40 * 4030987 * 2
def baseEnd_4030987 : Nat := 459963076227850106338741

theorem tailTrace_4030987 : CollatzResearch.WordTrace tailWord_4030987 prefixEnd_4030987 459963076227850106338741 := by
  unfold tailWord_4030987
  simp only [CollatzResearch.WordTrace]
  refine ⟨147022174247430011615379215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98014782831620007743586143 147022174247430011615379215)
  ·
    refine ⟨220533261371145017423068823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147022174247430011615379215 220533261371145017423068823)
    ·
      refine ⟨330799892056717526134603235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220533261371145017423068823 330799892056717526134603235)
      ·
        refine ⟨496199838085076289201904853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330799892056717526134603235 496199838085076289201904853)
        ·
          refine ⟨11629683705118975528169645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 496199838085076289201904853 11629683705118975528169645)
          ·
            refine ⟨4361131389419615823063617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11629683705118975528169645 4361131389419615823063617)
            ·
              refine ⟨3270848542064711867297713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4361131389419615823063617 3270848542064711867297713)
              ·
                refine ⟨2453136406548533900473285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270848542064711867297713 2453136406548533900473285)
                ·
                  refine ⟨459963076227850106338741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2453136406548533900473285 459963076227850106338741)
                  ·
                    rfl

theorem cell22_4030987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 4].length) (baseStart_4030987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4030987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4030987 prefixEnd_4030987 := by exact prefixLift 4030987
  have htrace : WordTrace (prefixWord ++ tailWord_4030987) baseStart_4030987 baseEnd_4030987 := by
    simpa [prefixWord, tailWord_4030987, baseEnd_4030987] using wordTrace_append hprefix tailTrace_4030987
  have hstable : (prefixWord ++ tailWord_4030987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030987).length < 2 ^ (prefixWord ++ tailWord_4030987).sum := by decide
  have hdescent : baseEnd_4030987 < baseStart_4030987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031013 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 5, 3]
def baseStart_4031013 : Nat := 118140960795 + 4031013 * 2 ^ 59
def prefixEnd_4031013 : Nat := 4983230072969 + 3 ^ 40 * 4031013 * 2
def baseEnd_4031013 : Nat := 1379898129014894917866143

theorem tailTrace_4031013 : CollatzResearch.WordTrace tailWord_4031013 prefixEnd_4031013 1379898129014894917866143 := by
  unfold tailWord_4031013
  simp only [CollatzResearch.WordTrace]
  refine ⟨147023122545335818055825693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98015415030223878703883795 147023122545335818055825693)
  ·
    refine ⟨55133670954500931770934635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147023122545335818055825693 55133670954500931770934635)
    ·
      refine ⟨82700506431751397656401953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55133670954500931770934635 82700506431751397656401953)
      ·
        refine ⟨62025379823813548242301465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82700506431751397656401953 62025379823813548242301465)
        ·
          refine ⟨46519034867860161181726099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62025379823813548242301465 46519034867860161181726099)
          ·
            refine ⟨69778552301790241772589149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46519034867860161181726099 69778552301790241772589149)
            ·
              refine ⟨26166957113171340664720931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69778552301790241772589149 26166957113171340664720931)
              ·
                refine ⟨39250435669757010997081397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26166957113171340664720931 39250435669757010997081397)
                ·
                  refine ⟨3679728344039719780976381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39250435669757010997081397 3679728344039719780976381)
                  ·
                    refine ⟨1379898129014894917866143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679728344039719780976381 1379898129014894917866143)
                    ·
                      rfl

theorem cell22_4031013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_4031013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031013 prefixEnd_4031013 := by exact prefixLift 4031013
  have htrace : WordTrace (prefixWord ++ tailWord_4031013) baseStart_4031013 baseEnd_4031013 := by
    simpa [prefixWord, tailWord_4031013, baseEnd_4031013] using wordTrace_append hprefix tailTrace_4031013
  have hstable : (prefixWord ++ tailWord_4031013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031013).length < 2 ^ (prefixWord ++ tailWord_4031013).sum := by decide
  have hdescent : baseEnd_4031013 < baseStart_4031013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031021 : List Nat := [1, 5, 4, 1, 1, 1, 2, 3, 4]
def baseStart_4031021 : Nat := 118140960795 + 4031021 * 2 ^ 59
def prefixEnd_4031021 : Nat := 4983230072969 + 3 ^ 40 * 4031021 * 2
def baseEnd_4031021 : Nat := 459966955859461854555373

theorem tailTrace_4031021 : CollatzResearch.WordTrace tailWord_4031021 prefixEnd_4031021 459966955859461854555373 := by
  unfold tailWord_4031021
  simp only [CollatzResearch.WordTrace]
  refine ⟨147023414329306835422116917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98015609552871223614744611 147023414329306835422116917)
  ·
    refine ⟨13783445093372515820823461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147023414329306835422116917 13783445093372515820823461)
    ·
      refine ⟨2584395955007346716404399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13783445093372515820823461 2584395955007346716404399)
      ·
        refine ⟨3876593932511020074606599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584395955007346716404399 3876593932511020074606599)
        ·
          refine ⟨5814890898766530111909899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3876593932511020074606599 5814890898766530111909899)
          ·
            refine ⟨8722336348149795167864849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5814890898766530111909899 8722336348149795167864849)
            ·
              refine ⟨6541752261112346375898637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8722336348149795167864849 6541752261112346375898637)
              ·
                refine ⟨2453157097917129890961989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6541752261112346375898637 2453157097917129890961989)
                ·
                  refine ⟨459966955859461854555373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2453157097917129890961989 459966955859461854555373)
                  ·
                    rfl

theorem cell22_4031021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_4031021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031021 prefixEnd_4031021 := by exact prefixLift 4031021
  have htrace : WordTrace (prefixWord ++ tailWord_4031021) baseStart_4031021 baseEnd_4031021 := by
    simpa [prefixWord, tailWord_4031021, baseEnd_4031021] using wordTrace_append hprefix tailTrace_4031021
  have hstable : (prefixWord ++ tailWord_4031021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031021).length < 2 ^ (prefixWord ++ tailWord_4031021).sum := by decide
  have hdescent : baseEnd_4031021 < baseStart_4031021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031047 : List Nat := [1, 1, 4, 1, 4, 1, 2, 4, 1, 3]
def baseStart_4031047 : Nat := 118140960795 + 4031047 * 2 ^ 59
def prefixEnd_4031047 : Nat := 4983230072969 + 3 ^ 40 * 4031047 * 2
def baseEnd_4031047 : Nat := 1379909767909730162516039

theorem tailTrace_4031047 : CollatzResearch.WordTrace tailWord_4031047 prefixEnd_4031047 1379909767909730162516039 := by
  unfold tailWord_4031047
  simp only [CollatzResearch.WordTrace]
  refine ⟨147024362627212641862563395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98016241751475094575042263 147024362627212641862563395)
  ·
    refine ⟨220536543940818962793845093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147024362627212641862563395 220536543940818962793845093)
    ·
      refine ⟨41350601988903555523845955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220536543940818962793845093 41350601988903555523845955)
      ·
        refine ⟨62025902983355333285768933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41350601988903555523845955 62025902983355333285768933)
        ·
          refine ⟨11629856809379124991081675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62025902983355333285768933 11629856809379124991081675)
          ·
            refine ⟨17444785214068687486622513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11629856809379124991081675 17444785214068687486622513)
            ·
              refine ⟨13083588910551515614966885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17444785214068687486622513 13083588910551515614966885)
              ·
                refine ⟨2453172920728409177806291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13083588910551515614966885 2453172920728409177806291)
                ·
                  refine ⟨3679759381092613766709437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453172920728409177806291 3679759381092613766709437)
                  ·
                    refine ⟨1379909767909730162516039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679759381092613766709437 1379909767909730162516039)
                    ·
                      rfl

theorem cell22_4031047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_4031047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031047 prefixEnd_4031047 := by exact prefixLift 4031047
  have htrace : WordTrace (prefixWord ++ tailWord_4031047) baseStart_4031047 baseEnd_4031047 := by
    simpa [prefixWord, tailWord_4031047, baseEnd_4031047] using wordTrace_append hprefix tailTrace_4031047
  have hstable : (prefixWord ++ tailWord_4031047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031047).length < 2 ^ (prefixWord ++ tailWord_4031047).sum := by decide
  have hdescent : baseEnd_4031047 < baseStart_4031047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031056 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_4031056 : Nat := 118140960795 + 4031056 * 2 ^ 59
def prefixEnd_4031056 : Nat := 4983230072969 + 3 ^ 40 * 4031056 * 2
def baseEnd_4031056 : Nat := 1379912848793657139041011

theorem tailTrace_4031056 : CollatzResearch.WordTrace tailWord_4031056 prefixEnd_4031056 1379912848793657139041011 := by
  unfold tailWord_4031056
  simp only [CollatzResearch.WordTrace]
  refine ⟨73512345442090018199820511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98016460589453357599760681 73512345442090018199820511)
  ·
    refine ⟨110268518163135027299730767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73512345442090018199820511 110268518163135027299730767)
    ·
      refine ⟨165402777244702540949596151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110268518163135027299730767 165402777244702540949596151)
      ·
        refine ⟨248104165867053811424394227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165402777244702540949596151 248104165867053811424394227)
        ·
          refine ⟨372156248800580717136591341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248104165867053811424394227 372156248800580717136591341)
          ·
            refine ⟨139558593300217768926221753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372156248800580717136591341 139558593300217768926221753)
            ·
              refine ⟨104668944975163326694666315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139558593300217768926221753 104668944975163326694666315)
              ·
                refine ⟨157003417462744990041999473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104668944975163326694666315 157003417462744990041999473)
                ·
                  refine ⟨117752563097058742531499605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157003417462744990041999473 117752563097058742531499605)
                  ·
                    refine ⟨1379912848793657139041011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117752563097058742531499605 1379912848793657139041011)
                    ·
                      rfl

theorem cell22_4031056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_4031056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031056 prefixEnd_4031056 := by exact prefixLift 4031056
  have htrace : WordTrace (prefixWord ++ tailWord_4031056) baseStart_4031056 baseEnd_4031056 := by
    simpa [prefixWord, tailWord_4031056, baseEnd_4031056] using wordTrace_append hprefix tailTrace_4031056
  have hstable : (prefixWord ++ tailWord_4031056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031056).length < 2 ^ (prefixWord ++ tailWord_4031056).sum := by decide
  have hdescent : baseEnd_4031056 < baseStart_4031056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031058 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_4031058 : Nat := 118140960795 + 4031058 * 2 ^ 59
def prefixEnd_4031058 : Nat := 4983230072969 + 3 ^ 40 * 4031058 * 2
def baseEnd_4031058 : Nat := 1379913533434529800491005

theorem tailTrace_4031058 : CollatzResearch.WordTrace tailWord_4031058 prefixEnd_4031058 1379913533434529800491005 := by
  unfold tailWord_4031058
  simp only [CollatzResearch.WordTrace]
  refine ⟨36756190957543197685303457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98016509220115193827475885 36756190957543197685303457)
  ·
    refine ⟨27567143218157398263977593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36756190957543197685303457 27567143218157398263977593)
    ·
      refine ⟨20675357413618048697983195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27567143218157398263977593 20675357413618048697983195)
      ·
        refine ⟨31013036120427073046974793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20675357413618048697983195 31013036120427073046974793)
        ·
          refine ⟨23259777090320304785231095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31013036120427073046974793 23259777090320304785231095)
          ·
            refine ⟨34889665635480457177846643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23259777090320304785231095 34889665635480457177846643)
            ·
              refine ⟨52334498453220685766769965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34889665635480457177846643 52334498453220685766769965)
              ·
                refine ⟨19625436919957757162538737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52334498453220685766769965 19625436919957757162538737)
                ·
                  refine ⟨14719077689968317871904053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19625436919957757162538737 14719077689968317871904053)
                  ·
                    refine ⟨1379913533434529800491005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14719077689968317871904053 1379913533434529800491005)
                    ·
                      rfl

theorem cell22_4031058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_4031058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031058 prefixEnd_4031058 := by exact prefixLift 4031058
  have htrace : WordTrace (prefixWord ++ tailWord_4031058) baseStart_4031058 baseEnd_4031058 := by
    simpa [prefixWord, tailWord_4031058, baseEnd_4031058] using wordTrace_append hprefix tailTrace_4031058
  have hstable : (prefixWord ++ tailWord_4031058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031058).length < 2 ^ (prefixWord ++ tailWord_4031058).sum := by decide
  have hdescent : baseEnd_4031058 < baseStart_4031058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031124 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_4031124 : Nat := 118140960795 + 4031124 * 2 ^ 59
def prefixEnd_4031124 : Nat := 4983230072969 + 3 ^ 40 * 4031124 * 2
def baseEnd_4031124 : Nat := 1379936126583327628340803

theorem tailTrace_4031124 : CollatzResearch.WordTrace tailWord_4031124 prefixEnd_4031124 1379936126583327628340803 := by
  unfold tailWord_4031124
  simp only [CollatzResearch.WordTrace]
  refine ⟨73513585523966842006558213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98018114031955789342077617 73513585523966842006558213)
  ·
    refine ⟨13783797285743782876229665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73513585523966842006558213 13783797285743782876229665)
    ·
      refine ⟨10337847964307837157172249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13783797285743782876229665 10337847964307837157172249)
      ·
        refine ⟨7753385973230877867879187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10337847964307837157172249 7753385973230877867879187)
        ·
          refine ⟨11630078959846316801818781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7753385973230877867879187 11630078959846316801818781)
          ·
            refine ⟨4361279609942368800682043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11630078959846316801818781 4361279609942368800682043)
            ·
              refine ⟨6541919414913553201023065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4361279609942368800682043 6541919414913553201023065)
              ·
                refine ⟨4906439561185164900767299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6541919414913553201023065 4906439561185164900767299)
                ·
                  refine ⟨7359659341777747351150949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906439561185164900767299 7359659341777747351150949)
                  ·
                    refine ⟨1379936126583327628340803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7359659341777747351150949 1379936126583327628340803)
                    ·
                      rfl

theorem cell22_4031124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_4031124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031124 prefixEnd_4031124 := by exact prefixLift 4031124
  have htrace : WordTrace (prefixWord ++ tailWord_4031124) baseStart_4031124 baseEnd_4031124 := by
    simpa [prefixWord, tailWord_4031124, baseEnd_4031124] using wordTrace_append hprefix tailTrace_4031124
  have hstable : (prefixWord ++ tailWord_4031124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031124).length < 2 ^ (prefixWord ++ tailWord_4031124).sum := by decide
  have hdescent : baseEnd_4031124 < baseStart_4031124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031133 : List Nat := [1, 4, 2, 1, 1, 1, 4, 8]
def baseStart_4031133 : Nat := 118140960795 + 4031133 * 2 ^ 59
def prefixEnd_4031133 : Nat := 4983230072969 + 3 ^ 40 * 4031133 * 2
def baseEnd_4031133 : Nat := 153326578607472733873975

theorem tailTrace_4031133 : CollatzResearch.WordTrace tailWord_4031133 prefixEnd_4031133 153326578607472733873975 := by
  unfold tailWord_4031133
  simp only [CollatzResearch.WordTrace]
  refine ⟨147027499304901078550194053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98018332869934052366796035 147027499304901078550194053)
  ·
    refine ⟨27567656119668952228161385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147027499304901078550194053 27567656119668952228161385)
    ·
      refine ⟨20675742089751714171121039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27567656119668952228161385 20675742089751714171121039)
      ·
        refine ⟨31013613134627571256681559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20675742089751714171121039 31013613134627571256681559)
        ·
          refine ⟨46520419701941356885022339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31013613134627571256681559 46520419701941356885022339)
          ·
            refine ⟨69780629552912035327533509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46520419701941356885022339 69780629552912035327533509)
            ·
              refine ⟨13083868041171006623912533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69780629552912035327533509 13083868041171006623912533)
              ·
                refine ⟨153326578607472733873975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13083868041171006623912533 153326578607472733873975)
                ·
                  rfl

theorem cell22_4031133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 8].length) (baseStart_4031133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031133 prefixEnd_4031133 := by exact prefixLift 4031133
  have htrace : WordTrace (prefixWord ++ tailWord_4031133) baseStart_4031133 baseEnd_4031133 := by
    simpa [prefixWord, tailWord_4031133, baseEnd_4031133] using wordTrace_append hprefix tailTrace_4031133
  have hstable : (prefixWord ++ tailWord_4031133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031133).length < 2 ^ (prefixWord ++ tailWord_4031133).sum := by decide
  have hdescent : baseEnd_4031133 < baseStart_4031133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031150 : List Nat := [4, 1, 4, 1, 1, 11]
def baseStart_4031150 : Nat := 118140960795 + 4031150 * 2 ^ 59
def prefixEnd_4031150 : Nat := 4983230072969 + 3 ^ 40 * 4031150 * 2
def baseEnd_4031150 : Nat := 17036358356971262064083

theorem tailTrace_4031150 : CollatzResearch.WordTrace tailWord_4031150 prefixEnd_4031150 17036358356971262064083 := by
  unfold tailWord_4031150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18378514918229936306695363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98018746230559660302375269 18378514918229936306695363)
  ·
    refine ⟨27567772377344904460043045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18378514918229936306695363 27567772377344904460043045)
    ·
      refine ⟨5168957320752169586258071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27567772377344904460043045 5168957320752169586258071)
      ·
        refine ⟨7753435981128254379387107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168957320752169586258071 7753435981128254379387107)
        ·
          refine ⟨11630153971692381569080661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7753435981128254379387107 11630153971692381569080661)
          ·
            refine ⟨17036358356971262064083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11630153971692381569080661 17036358356971262064083)
            ·
              rfl

theorem cell22_4031150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 11].length) (baseStart_4031150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031150 prefixEnd_4031150 := by exact prefixLift 4031150
  have htrace : WordTrace (prefixWord ++ tailWord_4031150) baseStart_4031150 baseEnd_4031150 := by
    simpa [prefixWord, tailWord_4031150, baseEnd_4031150] using wordTrace_append hprefix tailTrace_4031150
  have hstable : (prefixWord ++ tailWord_4031150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031150).length < 2 ^ (prefixWord ++ tailWord_4031150).sum := by decide
  have hdescent : baseEnd_4031150 < baseStart_4031150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031182 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_4031182 : Nat := 118140960795 + 4031182 * 2 ^ 59
def prefixEnd_4031182 : Nat := 4983230072969 + 3 ^ 40 * 4031182 * 2
def baseEnd_4031182 : Nat := 1379955981168634810390625

theorem tailTrace_4031182 : CollatzResearch.WordTrace tailWord_4031182 prefixEnd_4031182 1379955981168634810390625 := by
  unfold tailWord_4031182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18378660810215444989840975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98019524321149039945818533 18378660810215444989840975)
  ·
    refine ⟨27567991215323167484761463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18378660810215444989840975 27567991215323167484761463)
    ·
      refine ⟨41351986822984751227142195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27567991215323167484761463 41351986822984751227142195)
      ·
        refine ⟨62027980234477126840713293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41351986822984751227142195 62027980234477126840713293)
        ·
          refine ⟨23260492587928922565267485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62027980234477126840713293 23260492587928922565267485)
          ·
            refine ⟨8722684720473345961975307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23260492587928922565267485 8722684720473345961975307)
            ·
              refine ⟨13084027080710018942962961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8722684720473345961975307 13084027080710018942962961)
              ·
                refine ⟨9813020310532514207222221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13084027080710018942962961 9813020310532514207222221)
                ·
                  refine ⟨3679882616449692827708333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9813020310532514207222221 3679882616449692827708333)
                  ·
                    refine ⟨1379955981168634810390625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679882616449692827708333 1379955981168634810390625)
                    ·
                      rfl

theorem cell22_4031182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_4031182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031182 prefixEnd_4031182 := by exact prefixLift 4031182
  have htrace : WordTrace (prefixWord ++ tailWord_4031182) baseStart_4031182 baseEnd_4031182 := by
    simpa [prefixWord, tailWord_4031182, baseEnd_4031182] using wordTrace_append hprefix tailTrace_4031182
  have hstable : (prefixWord ++ tailWord_4031182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031182).length < 2 ^ (prefixWord ++ tailWord_4031182).sum := by decide
  have hdescent : baseEnd_4031182 < baseStart_4031182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031193 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_4031193 : Nat := 118140960795 + 4031193 * 2 ^ 59
def prefixEnd_4031193 : Nat := 4983230072969 + 3 ^ 40 * 4031193 * 2
def baseEnd_4031193 : Nat := 1379959746693434448365591

theorem tailTrace_4031193 : CollatzResearch.WordTrace tailWord_4031193 prefixEnd_4031193 1379959746693434448365591 := by
  unfold tailWord_4031193
  simp only [CollatzResearch.WordTrace]
  refine ⟨147029687684683708797378233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98019791789789139198252155 147029687684683708797378233)
  ·
    refine ⟨110272265763512781598033675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147029687684683708797378233 110272265763512781598033675)
    ·
      refine ⟨165408398645269172397050513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110272265763512781598033675 165408398645269172397050513)
      ·
        refine ⟨124056298983951879297787885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165408398645269172397050513 124056298983951879297787885)
        ·
          refine ⟨46521112118981954736670457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124056298983951879297787885 46521112118981954736670457)
          ·
            refine ⟨34890834089236466052502843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46521112118981954736670457 34890834089236466052502843)
            ·
              refine ⟨52336251133854699078754265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34890834089236466052502843 52336251133854699078754265)
              ·
                refine ⟨39252188350391024309065699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52336251133854699078754265 39252188350391024309065699)
                ·
                  refine ⟨58878282525586536463598549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39252188350391024309065699 58878282525586536463598549)
                  ·
                    refine ⟨1379959746693434448365591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58878282525586536463598549 1379959746693434448365591)
                    ·
                      rfl

theorem cell22_4031193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_4031193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031193 prefixEnd_4031193 := by exact prefixLift 4031193
  have htrace : WordTrace (prefixWord ++ tailWord_4031193) baseStart_4031193 baseEnd_4031193 := by
    simpa [prefixWord, tailWord_4031193, baseEnd_4031193] using wordTrace_append hprefix tailTrace_4031193
  have hstable : (prefixWord ++ tailWord_4031193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031193).length < 2 ^ (prefixWord ++ tailWord_4031193).sum := by decide
  have hdescent : baseEnd_4031193 < baseStart_4031193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031199 : List Nat := [1, 1, 2, 3, 2, 4, 2, 3, 1, 3]
def baseStart_4031199 : Nat := 118140960795 + 4031199 * 2 ^ 59
def prefixEnd_4031199 : Nat := 4983230072969 + 3 ^ 40 * 4031199 * 2
def baseEnd_4031199 : Nat := 1379961800616052432715573

theorem tailTrace_4031199 : CollatzResearch.WordTrace tailWord_4031199 prefixEnd_4031199 1379961800616052432715573 := by
  unfold tailWord_4031199
  simp only [CollatzResearch.WordTrace]
  refine ⟨147029906522661971822096651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98019937681774647881397767 147029906522661971822096651)
  ·
    refine ⟨220544859783992957733144977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147029906522661971822096651 220544859783992957733144977)
    ·
      refine ⟨165408644837994718299858733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220544859783992957733144977 165408644837994718299858733)
      ·
        refine ⟨62028241814248019362447025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165408644837994718299858733 62028241814248019362447025)
        ·
          refine ⟨46521181360686014521835269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62028241814248019362447025 46521181360686014521835269)
          ·
            refine ⟨8722721505128627722844113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46521181360686014521835269 8722721505128627722844113)
            ·
              refine ⟨6542041128846470792133085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8722721505128627722844113 6542041128846470792133085)
              ·
                refine ⟨2453265423317426547049907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6542041128846470792133085 2453265423317426547049907)
                ·
                  refine ⟨3679898134976139820574861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453265423317426547049907 3679898134976139820574861)
                  ·
                    refine ⟨1379961800616052432715573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679898134976139820574861 1379961800616052432715573)
                    ·
                      rfl

theorem cell22_4031199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 1, 3].length) (baseStart_4031199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031199 prefixEnd_4031199 := by exact prefixLift 4031199
  have htrace : WordTrace (prefixWord ++ tailWord_4031199) baseStart_4031199 baseEnd_4031199 := by
    simpa [prefixWord, tailWord_4031199, baseEnd_4031199] using wordTrace_append hprefix tailTrace_4031199
  have hstable : (prefixWord ++ tailWord_4031199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031199).length < 2 ^ (prefixWord ++ tailWord_4031199).sum := by decide
  have hdescent : baseEnd_4031199 < baseStart_4031199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031240 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 6]
def baseStart_4031240 : Nat := 118140960795 + 4031240 * 2 ^ 59
def prefixEnd_4031240 : Nat := 4983230072969 + 3 ^ 40 * 4031240 * 2
def baseEnd_4031240 : Nat := 459991945251313997480149

theorem tailTrace_4031240 : CollatzResearch.WordTrace tailWord_4031240 prefixEnd_4031240 459991945251313997480149 := by
  unfold tailWord_4031240
  simp only [CollatzResearch.WordTrace]
  refine ⟨73515700957756717912169587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98020934610342290549559449 73515700957756717912169587)
  ·
    refine ⟨110273551436635076868254381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73515700957756717912169587 110273551436635076868254381)
    ·
      refine ⟨41352581788738153825595393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110273551436635076868254381 41352581788738153825595393)
      ·
        refine ⟨31014436341553615369196545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41352581788738153825595393 31014436341553615369196545)
        ·
          refine ⟨23260827256165211526897409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31014436341553615369196545 23260827256165211526897409)
          ·
            refine ⟨17445620442123908645173057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23260827256165211526897409 17445620442123908645173057)
            ·
              refine ⟨13084215331592931483879793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17445620442123908645173057 13084215331592931483879793)
              ·
                refine ⟨9813161498694698612909845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13084215331592931483879793 9813161498694698612909845)
                ·
                  refine ⟨459991945251313997480149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9813161498694698612909845 459991945251313997480149)
                  ·
                    rfl

theorem cell22_4031240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_4031240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031240 prefixEnd_4031240 := by exact prefixLift 4031240
  have htrace : WordTrace (prefixWord ++ tailWord_4031240) baseStart_4031240 baseEnd_4031240 := by
    simpa [prefixWord, tailWord_4031240, baseEnd_4031240] using wordTrace_append hprefix tailTrace_4031240
  have hstable : (prefixWord ++ tailWord_4031240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031240).length < 2 ^ (prefixWord ++ tailWord_4031240).sum := by decide
  have hdescent : baseEnd_4031240 < baseStart_4031240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031242 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_4031242 : Nat := 118140960795 + 4031242 * 2 ^ 59
def prefixEnd_4031242 : Nat := 4983230072969 + 3 ^ 40 * 4031242 * 2
def baseEnd_4031242 : Nat := 1379976520394814653890441

theorem tailTrace_4031242 : CollatzResearch.WordTrace tailWord_4031242 prefixEnd_4031242 1379976520394814653890441 := by
  unfold tailWord_4031242
  simp only [CollatzResearch.WordTrace]
  refine ⟨36757868715376547541477995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98020983241004126777274653 36757868715376547541477995)
  ·
    refine ⟨55136803073064821312216993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36757868715376547541477995 55136803073064821312216993)
    ·
      refine ⟨41352602304798615984162745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55136803073064821312216993 41352602304798615984162745)
      ·
        refine ⟨31014451728598961988122059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41352602304798615984162745 31014451728598961988122059)
        ·
          refine ⟨46521677592898442982183089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31014451728598961988122059 46521677592898442982183089)
          ·
            refine ⟨34891258194673832236637317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46521677592898442982183089 34891258194673832236637317)
            ·
              refine ⟨6542110911501343544369497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34891258194673832236637317 6542110911501343544369497)
              ·
                refine ⟨4906583183626007658277123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6542110911501343544369497 4906583183626007658277123)
                ·
                  refine ⟨7359874775439011487415685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906583183626007658277123 7359874775439011487415685)
                  ·
                    refine ⟨1379976520394814653890441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7359874775439011487415685 1379976520394814653890441)
                    ·
                      rfl

theorem cell22_4031242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_4031242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031242 prefixEnd_4031242 := by exact prefixLift 4031242
  have htrace : WordTrace (prefixWord ++ tailWord_4031242) baseStart_4031242 baseEnd_4031242 := by
    simpa [prefixWord, tailWord_4031242, baseEnd_4031242] using wordTrace_append hprefix tailTrace_4031242
  have hstable : (prefixWord ++ tailWord_4031242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031242).length < 2 ^ (prefixWord ++ tailWord_4031242).sum := by decide
  have hdescent : baseEnd_4031242 < baseStart_4031242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031250 : List Nat := [3, 2, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4031250 : Nat := 118140960795 + 4031250 * 2 ^ 59
def prefixEnd_4031250 : Nat := 4983230072969 + 3 ^ 40 * 4031250 * 2
def baseEnd_4031250 : Nat := 1379979258958305299690417

theorem tailTrace_4031250 : CollatzResearch.WordTrace tailWord_4031250 prefixEnd_4031250 1379979258958305299690417 := by
  unfold tailWord_4031250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36757941661369301883050801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98021177763651471688135469 36757941661369301883050801)
  ·
    refine ⟨27568456246026976412288101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36757941661369301883050801 27568456246026976412288101)
    ·
      refine ⟨5169085546130058077304019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27568456246026976412288101 5169085546130058077304019)
      ·
        refine ⟨7753628319195087115956029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5169085546130058077304019 7753628319195087115956029)
        ·
          refine ⟨2907610619698157668483511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7753628319195087115956029 2907610619698157668483511)
          ·
            refine ⟨4361415929547236502725267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907610619698157668483511 4361415929547236502725267)
            ·
              refine ⟨6542123894320854754087901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4361415929547236502725267 6542123894320854754087901)
              ·
                refine ⟨2453296460370320532782963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6542123894320854754087901 2453296460370320532782963)
                ·
                  refine ⟨3679944690555480799174445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453296460370320532782963 3679944690555480799174445)
                  ·
                    refine ⟨1379979258958305299690417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679944690555480799174445 1379979258958305299690417)
                    ·
                      rfl

theorem cell22_4031250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4031250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031250 prefixEnd_4031250 := by exact prefixLift 4031250
  have htrace : WordTrace (prefixWord ++ tailWord_4031250) baseStart_4031250 baseEnd_4031250 := by
    simpa [prefixWord, tailWord_4031250, baseEnd_4031250] using wordTrace_append hprefix tailTrace_4031250
  have hstable : (prefixWord ++ tailWord_4031250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031250).length < 2 ^ (prefixWord ++ tailWord_4031250).sum := by decide
  have hdescent : baseEnd_4031250 < baseStart_4031250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031272 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 4, 3]
def baseStart_4031272 : Nat := 118140960795 + 4031272 * 2 ^ 59
def prefixEnd_4031272 : Nat := 4983230072969 + 3 ^ 40 * 4031272 * 2
def baseEnd_4031272 : Nat := 1379986790007904575640349

theorem tailTrace_4031272 : CollatzResearch.WordTrace tailWord_4031272 prefixEnd_4031272 1379986790007904575640349 := by
  unfold tailWord_4031272
  simp only [CollatzResearch.WordTrace]
  refine ⟨73516284525698752644752035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98021712700931670193002713 73516284525698752644752035)
  ·
    refine ⟨110274426788548128967128053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73516284525698752644752035 110274426788548128967128053)
    ·
      refine ⟨10338227511426387090668255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110274426788548128967128053 10338227511426387090668255)
      ·
        refine ⟨15507341267139580636002383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10338227511426387090668255 15507341267139580636002383)
        ·
          refine ⟨23261011900709370954003575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15507341267139580636002383 23261011900709370954003575)
          ·
            refine ⟨34891517851064056431005363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23261011900709370954003575 34891517851064056431005363)
            ·
              refine ⟨52337276776596084646508045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34891517851064056431005363 52337276776596084646508045)
              ·
                refine ⟨19626478791223531742440517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52337276776596084646508045 19626478791223531742440517)
                ·
                  refine ⟨3679964773354412201707597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19626478791223531742440517 3679964773354412201707597)
                  ·
                    refine ⟨1379986790007904575640349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679964773354412201707597 1379986790007904575640349)
                    ·
                      rfl

theorem cell22_4031272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_4031272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031272 prefixEnd_4031272 := by exact prefixLift 4031272
  have htrace : WordTrace (prefixWord ++ tailWord_4031272) baseStart_4031272 baseEnd_4031272 := by
    simpa [prefixWord, tailWord_4031272, baseEnd_4031272] using wordTrace_append hprefix tailTrace_4031272
  have hstable : (prefixWord ++ tailWord_4031272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031272).length < 2 ^ (prefixWord ++ tailWord_4031272).sum := by decide
  have hdescent : baseEnd_4031272 < baseStart_4031272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031285 : List Nat := [1, 3, 3, 1, 3, 1, 1, 9]
def baseStart_4031285 : Nat := 118140960795 + 4031285 * 2 ^ 59
def prefixEnd_4031285 : Nat := 4983230072969 + 3 ^ 40 * 4031285 * 2
def baseEnd_4031285 : Nat := 153332360019286319451701

theorem tailTrace_4031285 : CollatzResearch.WordTrace tailWord_4031285 prefixEnd_4031285 153332360019286319451701 := by
  unfold tailWord_4031285
  simp only [CollatzResearch.WordTrace]
  refine ⟨147033043200350408509727309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98022028800233605673151539 147033043200350408509727309)
  ·
    refine ⟨55137391200131403191147741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147033043200350408509727309 55137391200131403191147741)
    ·
      refine ⟨20676521700049276196680403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55137391200131403191147741 20676521700049276196680403)
      ·
        refine ⟨31014782550073914295020605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20676521700049276196680403 31014782550073914295020605)
        ·
          refine ⟨11630543456277717860632727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31014782550073914295020605 11630543456277717860632727)
          ·
            refine ⟨17445815184416576790949091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11630543456277717860632727 17445815184416576790949091)
            ·
              refine ⟨26168722776624865186423637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17445815184416576790949091 26168722776624865186423637)
              ·
                refine ⟨153332360019286319451701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26168722776624865186423637 153332360019286319451701)
                ·
                  rfl

theorem cell22_4031285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 9].length) (baseStart_4031285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031285 prefixEnd_4031285 := by exact prefixLift 4031285
  have htrace : WordTrace (prefixWord ++ tailWord_4031285) baseStart_4031285 baseEnd_4031285 := by
    simpa [prefixWord, tailWord_4031285, baseEnd_4031285] using wordTrace_append hprefix tailTrace_4031285
  have hstable : (prefixWord ++ tailWord_4031285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031285).length < 2 ^ (prefixWord ++ tailWord_4031285).sum := by decide
  have hdescent : baseEnd_4031285 < baseStart_4031285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031345 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_4031345 : Nat := 118140960795 + 4031345 * 2 ^ 59
def prefixEnd_4031345 : Nat := 4983230072969 + 3 ^ 40 * 4031345 * 2
def baseEnd_4031345 : Nat := 1380011779399756718565125

theorem tailTrace_4031345 : CollatzResearch.WordTrace tailWord_4031345 prefixEnd_4031345 1380011779399756718565125 := by
  unfold tailWord_4031345
  simp only [CollatzResearch.WordTrace]
  refine ⟨147035231580133038756911489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98023487720088692504607659 147035231580133038756911489)
  ·
    refine ⟨110276423685099779067683617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147035231580133038756911489 110276423685099779067683617)
    ·
      refine ⟨82707317763824834300762713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110276423685099779067683617 82707317763824834300762713)
      ·
        refine ⟨62030488322868625725572035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82707317763824834300762713 62030488322868625725572035)
        ·
          refine ⟨93045732484302938588358053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62030488322868625725572035 93045732484302938588358053)
          ·
            refine ⟨17446074840806800985317135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93045732484302938588358053 17446074840806800985317135)
            ·
              refine ⟨26169112261210201477975703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17446074840806800985317135 26169112261210201477975703)
              ·
                refine ⟨39253668391815302216963555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26169112261210201477975703 39253668391815302216963555)
                ·
                  refine ⟨58880502587722953325445333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39253668391815302216963555 58880502587722953325445333)
                  ·
                    refine ⟨1380011779399756718565125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58880502587722953325445333 1380011779399756718565125)
                    ·
                      rfl

theorem cell22_4031345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_4031345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031345 prefixEnd_4031345 := by exact prefixLift 4031345
  have htrace : WordTrace (prefixWord ++ tailWord_4031345) baseStart_4031345 baseEnd_4031345 := by
    simpa [prefixWord, tailWord_4031345, baseEnd_4031345] using wordTrace_append hprefix tailTrace_4031345
  have hstable : (prefixWord ++ tailWord_4031345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031345).length < 2 ^ (prefixWord ++ tailWord_4031345).sum := by decide
  have hdescent : baseEnd_4031345 < baseStart_4031345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031422 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4031422 : Nat := 118140960795 + 4031422 * 2 ^ 59
def prefixEnd_4031422 : Nat := 4983230072969 + 3 ^ 40 * 4031422 * 2
def baseEnd_4031422 : Nat := 1380038138073354184389889

theorem tailTrace_4031422 : CollatzResearch.WordTrace tailWord_4031422 prefixEnd_4031422 1380038138073354184389889 := by
  unfold tailWord_4031422
  simp only [CollatzResearch.WordTrace]
  refine ⟨18379755000106760113433065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98025360000569387271643013 18379755000106760113433065)
  ·
    refine ⟨13784816250080070085074799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18379755000106760113433065 13784816250080070085074799)
    ·
      refine ⟨20677224375120105127612199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13784816250080070085074799 20677224375120105127612199)
      ·
        refine ⟨31015836562680157691418299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20677224375120105127612199 31015836562680157691418299)
        ·
          refine ⟨46523754844020236537127449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31015836562680157691418299 46523754844020236537127449)
          ·
            refine ⟨34892816133015177402845587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46523754844020236537127449 34892816133015177402845587)
            ·
              refine ⟨52339224199522766104268381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34892816133015177402845587 52339224199522766104268381)
              ·
                refine ⟨19627209074821037289100643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52339224199522766104268381 19627209074821037289100643)
                ·
                  refine ⟨29440813612231555933650965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19627209074821037289100643 29440813612231555933650965)
                  ·
                    refine ⟨1380038138073354184389889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29440813612231555933650965 1380038138073354184389889)
                    ·
                      rfl

theorem cell22_4031422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4031422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031422 prefixEnd_4031422 := by exact prefixLift 4031422
  have htrace : WordTrace (prefixWord ++ tailWord_4031422) baseStart_4031422 baseEnd_4031422 := by
    simpa [prefixWord, tailWord_4031422, baseEnd_4031422] using wordTrace_append hprefix tailTrace_4031422
  have hstable : (prefixWord ++ tailWord_4031422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031422).length < 2 ^ (prefixWord ++ tailWord_4031422).sum := by decide
  have hdescent : baseEnd_4031422 < baseStart_4031422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031458 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_4031458 : Nat := 118140960795 + 4031458 * 2 ^ 59
def prefixEnd_4031458 : Nat := 4983230072969 + 3 ^ 40 * 4031458 * 2
def baseEnd_4031458 : Nat := 1380050461609062090489779

theorem tailTrace_4031458 : CollatzResearch.WordTrace tailWord_4031458 prefixEnd_4031458 1380050461609062090489779 := by
  unfold tailWord_4031458
  simp only [CollatzResearch.WordTrace]
  refine ⟨36759838257180914763943757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98026235352482439370516685 36759838257180914763943757)
  ·
    refine ⟨13784939346442843036478909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36759838257180914763943757 13784939346442843036478909)
    ·
      refine ⟨5169352254916066138679591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13784939346442843036478909 5169352254916066138679591)
      ·
        refine ⟨7754028382374099208019387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5169352254916066138679591 7754028382374099208019387)
        ·
          refine ⟨11631042573561148812029081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7754028382374099208019387 11631042573561148812029081)
          ·
            refine ⟨8723281930170861609021811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11631042573561148812029081 8723281930170861609021811)
            ·
              refine ⟨13084922895256292413532717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8723281930170861609021811 13084922895256292413532717)
              ·
                refine ⟨4906846085721109655074769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13084922895256292413532717 4906846085721109655074769)
                ·
                  refine ⟨3680134564290832241306077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4906846085721109655074769 3680134564290832241306077)
                  ·
                    refine ⟨1380050461609062090489779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3680134564290832241306077 1380050461609062090489779)
                    ·
                      rfl

theorem cell22_4031458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_4031458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031458 prefixEnd_4031458 := by exact prefixLift 4031458
  have htrace : WordTrace (prefixWord ++ tailWord_4031458) baseStart_4031458 baseEnd_4031458 := by
    simpa [prefixWord, tailWord_4031458, baseEnd_4031458] using wordTrace_append hprefix tailTrace_4031458
  have hstable : (prefixWord ++ tailWord_4031458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031458).length < 2 ^ (prefixWord ++ tailWord_4031458).sum := by decide
  have hdescent : baseEnd_4031458 < baseStart_4031458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031499 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 5]
def baseStart_4031499 : Nat := 118140960795 + 4031499 * 2 ^ 59
def prefixEnd_4031499 : Nat := 4983230072969 + 3 ^ 40 * 4031499 * 2
def baseEnd_4031499 : Nat := 460021498915650550071551

theorem tailTrace_4031499 : CollatzResearch.WordTrace tailWord_4031499 prefixEnd_4031499 460021498915650550071551 := by
  unfold tailWord_4031499
  simp only [CollatzResearch.WordTrace]
  refine ⟨147040848421575123058017551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98027232281050082038678367 147040848421575123058017551)
  ·
    refine ⟨220561272632362684587026327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147040848421575123058017551 220561272632362684587026327)
    ·
      refine ⟨330841908948544026880539491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220561272632362684587026327 330841908948544026880539491)
      ·
        refine ⟨496262863422816040320809237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330841908948544026880539491 496262863422816040320809237)
        ·
          refine ⟨23262321722944501890037933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 496262863422816040320809237 23262321722944501890037933)
          ·
            refine ⟨8723370646104188208764225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23262321722944501890037933 8723370646104188208764225)
            ·
              refine ⟨6542527984578141156573169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8723370646104188208764225 6542527984578141156573169)
              ·
                refine ⟨4906895988433605867429877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6542527984578141156573169 4906895988433605867429877)
                ·
                  refine ⟨460021498915650550071551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4906895988433605867429877 460021498915650550071551)
                  ·
                    rfl

theorem cell22_4031499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 5].length) (baseStart_4031499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031499 prefixEnd_4031499 := by exact prefixLift 4031499
  have htrace : WordTrace (prefixWord ++ tailWord_4031499) baseStart_4031499 baseEnd_4031499 := by
    simpa [prefixWord, tailWord_4031499, baseEnd_4031499] using wordTrace_append hprefix tailTrace_4031499
  have hstable : (prefixWord ++ tailWord_4031499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031499).length < 2 ^ (prefixWord ++ tailWord_4031499).sum := by decide
  have hdescent : baseEnd_4031499 < baseStart_4031499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031546 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 1, 4]
def baseStart_4031546 : Nat := 118140960795 + 4031546 * 2 ^ 59
def prefixEnd_4031546 : Nat := 4983230072969 + 3 ^ 40 * 4031546 * 2
def baseEnd_4031546 : Nat := 1380080585807459194289509

theorem tailTrace_4031546 : CollatzResearch.WordTrace tailWord_4031546 prefixEnd_4031546 1380080585807459194289509 := by
  unfold tailWord_4031546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36760640663101212521244623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98028375101603233389985661 36760640663101212521244623)
  ·
    refine ⟨55140960994651818781866935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36760640663101212521244623 55140960994651818781866935)
    ·
      refine ⟨82711441491977728172800403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55140960994651818781866935 82711441491977728172800403)
      ·
        refine ⟨124067162237966592259200605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82711441491977728172800403 124067162237966592259200605)
        ·
          refine ⟨46525185839237472097200227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124067162237966592259200605 46525185839237472097200227)
          ·
            refine ⟨69787778758856208145800341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46525185839237472097200227 69787778758856208145800341)
            ·
              refine ⟨3271302129321384756834391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69787778758856208145800341 3271302129321384756834391)
              ·
                refine ⟨4906953193982077135251587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271302129321384756834391 4906953193982077135251587)
                ·
                  refine ⟨7360429790973115702877381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906953193982077135251587 7360429790973115702877381)
                  ·
                    refine ⟨1380080585807459194289509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7360429790973115702877381 1380080585807459194289509)
                    ·
                      rfl

theorem cell22_4031546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_4031546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031546 prefixEnd_4031546 := by exact prefixLift 4031546
  have htrace : WordTrace (prefixWord ++ tailWord_4031546) baseStart_4031546 baseEnd_4031546 := by
    simpa [prefixWord, tailWord_4031546, baseEnd_4031546] using wordTrace_append hprefix tailTrace_4031546
  have hstable : (prefixWord ++ tailWord_4031546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031546).length < 2 ^ (prefixWord ++ tailWord_4031546).sum := by decide
  have hdescent : baseEnd_4031546 < baseStart_4031546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031587 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 1, 9]
def baseStart_4031587 : Nat := 118140960795 + 4031587 * 2 ^ 59
def prefixEnd_4031587 : Nat := 4983230072969 + 3 ^ 40 * 4031587 * 2
def baseEnd_4031587 : Nat := 1380094620945348754014383

theorem tailTrace_4031587 : CollatzResearch.WordTrace tailWord_4031587 prefixEnd_4031587 1380094620945348754014383 := by
  unfold tailWord_4031587
  simp only [CollatzResearch.WordTrace]
  refine ⟨147044058045256314087221015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98029372030170876058147343 147044058045256314087221015)
  ·
    refine ⟨220566087067884471130831523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147044058045256314087221015 220566087067884471130831523)
    ·
      refine ⟨330849130601826706696247285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220566087067884471130831523 330849130601826706696247285)
      ·
        refine ⟨31017105993921253752773183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 330849130601826706696247285 31017105993921253752773183)
        ·
          refine ⟨46525658990881880629159775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31017105993921253752773183 46525658990881880629159775)
          ·
            refine ⟨69788488486322820943739663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46525658990881880629159775 69788488486322820943739663)
            ·
              refine ⟨104682732729484231415609495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69788488486322820943739663 104682732729484231415609495)
              ·
                refine ⟨157024099094226347123414243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104682732729484231415609495 157024099094226347123414243)
                ·
                  refine ⟨235536148641339520685121365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157024099094226347123414243 235536148641339520685121365)
                  ·
                    refine ⟨1380094620945348754014383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 235536148641339520685121365 1380094620945348754014383)
                    ·
                      rfl

theorem cell22_4031587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_4031587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031587 prefixEnd_4031587 := by exact prefixLift 4031587
  have htrace : WordTrace (prefixWord ++ tailWord_4031587) baseStart_4031587 baseEnd_4031587 := by
    simpa [prefixWord, tailWord_4031587, baseEnd_4031587] using wordTrace_append hprefix tailTrace_4031587
  have hstable : (prefixWord ++ tailWord_4031587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031587).length < 2 ^ (prefixWord ++ tailWord_4031587).sum := by decide
  have hdescent : baseEnd_4031587 < baseStart_4031587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031713 : List Nat := [1, 2, 3, 1, 3, 3, 2, 3, 4]
def baseStart_4031713 : Nat := 118140960795 + 4031713 * 2 ^ 59
def prefixEnd_4031713 : Nat := 4983230072969 + 3 ^ 40 * 4031713 * 2
def baseEnd_4031713 : Nat := 460045917773442141787999

theorem tailTrace_4031713 : CollatzResearch.WordTrace tailWord_4031713 prefixEnd_4031713 460045917773442141787999 := by
  unfold tailWord_4031713
  simp only [CollatzResearch.WordTrace]
  refine ⟨147048653642799837606307793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98032435761866558404205195 147048653642799837606307793)
  ·
    refine ⟨110286490232099878204730845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147048653642799837606307793 110286490232099878204730845)
    ·
      refine ⟨41357433837037454326774067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110286490232099878204730845 41357433837037454326774067)
      ·
        refine ⟨62036150755556181490161101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41357433837037454326774067 62036150755556181490161101)
        ·
          refine ⟨23263556533333568058810413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62036150755556181490161101 23263556533333568058810413)
          ·
            refine ⟨8723833700000088022053905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23263556533333568058810413 8723833700000088022053905)
            ·
              refine ⟨6542875275000066016540429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8723833700000088022053905 6542875275000066016540429)
              ·
                refine ⟨2453578228125024756202661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6542875275000066016540429 2453578228125024756202661)
                ·
                  refine ⟨460045917773442141787999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2453578228125024756202661 460045917773442141787999)
                  ·
                    rfl

theorem cell22_4031713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 4].length) (baseStart_4031713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031713 prefixEnd_4031713 := by exact prefixLift 4031713
  have htrace : WordTrace (prefixWord ++ tailWord_4031713) baseStart_4031713 baseEnd_4031713 := by
    simpa [prefixWord, tailWord_4031713, baseEnd_4031713] using wordTrace_append hprefix tailTrace_4031713
  have hstable : (prefixWord ++ tailWord_4031713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031713).length < 2 ^ (prefixWord ++ tailWord_4031713).sum := by decide
  have hdescent : baseEnd_4031713 < baseStart_4031713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031724 : List Nat := [2, 2, 1, 1, 2, 5, 9]
def baseStart_4031724 : Nat := 118140960795 + 4031724 * 2 ^ 59
def prefixEnd_4031724 : Nat := 4983230072969 + 3 ^ 40 * 4031724 * 2
def baseEnd_4031724 : Nat := 51116352549819483827369

theorem tailTrace_4031724 : CollatzResearch.WordTrace tailWord_4031724 prefixEnd_4031724 51116352549819483827369 := by
  unfold tailWord_4031724
  simp only [CollatzResearch.WordTrace]
  refine ⟨73524527422879993242479113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98032703230506657656638817 73524527422879993242479113)
  ·
    refine ⟨55143395567159994931859335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73524527422879993242479113 55143395567159994931859335)
    ·
      refine ⟨82715093350739992397789003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55143395567159994931859335 82715093350739992397789003)
      ·
        refine ⟨124072640026109988596683505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82715093350739992397789003 124072640026109988596683505)
        ·
          refine ⟨93054480019582491447512629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124072640026109988596683505 93054480019582491447512629)
          ·
            refine ⟨8723857501835858573204309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93054480019582491447512629 8723857501835858573204309)
            ·
              refine ⟨51116352549819483827369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8723857501835858573204309 51116352549819483827369)
              ·
                rfl

theorem cell22_4031724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 9].length) (baseStart_4031724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031724 prefixEnd_4031724 := by exact prefixLift 4031724
  have htrace : WordTrace (prefixWord ++ tailWord_4031724) baseStart_4031724 baseEnd_4031724 := by
    simpa [prefixWord, tailWord_4031724, baseEnd_4031724] using wordTrace_append hprefix tailTrace_4031724
  have hstable : (prefixWord ++ tailWord_4031724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031724).length < 2 ^ (prefixWord ++ tailWord_4031724).sum := by decide
  have hdescent : baseEnd_4031724 < baseStart_4031724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031726 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_4031726 : Nat := 118140960795 + 4031726 * 2 ^ 59
def prefixEnd_4031726 : Nat := 4983230072969 + 3 ^ 40 * 4031726 * 2
def baseEnd_4031726 : Nat := 1380142203485998724788957

theorem tailTrace_4031726 : CollatzResearch.WordTrace tailWord_4031726 prefixEnd_4031726 1380142203485998724788957 := by
  unfold tailWord_4031726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18381140973969092603316379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98032751861168493884354021 18381140973969092603316379)
  ·
    refine ⟨27571711460953638904974569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18381140973969092603316379 27571711460953638904974569)
    ·
      refine ⟨20678783595715229178730927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27571711460953638904974569 20678783595715229178730927)
      ·
        refine ⟨31018175393572843768096391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20678783595715229178730927 31018175393572843768096391)
        ·
          refine ⟨46527263090359265652144587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31018175393572843768096391 46527263090359265652144587)
          ·
            refine ⟨69790894635538898478216881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46527263090359265652144587 69790894635538898478216881)
            ·
              refine ⟨52343170976654173858662661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69790894635538898478216881 52343170976654173858662661)
              ·
                refine ⟨9814344558122657598499249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52343170976654173858662661 9814344558122657598499249)
                ·
                  refine ⟨7360758418591993198874437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9814344558122657598499249 7360758418591993198874437)
                  ·
                    refine ⟨1380142203485998724788957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7360758418591993198874437 1380142203485998724788957)
                    ·
                      rfl

theorem cell22_4031726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_4031726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031726 prefixEnd_4031726 := by exact prefixLift 4031726
  have htrace : WordTrace (prefixWord ++ tailWord_4031726) baseStart_4031726 baseEnd_4031726 := by
    simpa [prefixWord, tailWord_4031726, baseEnd_4031726] using wordTrace_append hprefix tailTrace_4031726
  have hstable : (prefixWord ++ tailWord_4031726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031726).length < 2 ^ (prefixWord ++ tailWord_4031726).sum := by decide
  have hdescent : baseEnd_4031726 < baseStart_4031726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031745 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 2, 3]
def baseStart_4031745 : Nat := 118140960795 + 4031745 * 2 ^ 59
def prefixEnd_4031745 : Nat := 4983230072969 + 3 ^ 40 * 4031745 * 2
def baseEnd_4031745 : Nat := 1380148707574289008563899

theorem tailTrace_4031745 : CollatzResearch.WordTrace tailWord_4031745 prefixEnd_4031745 1380148707574289008563899 := by
  unfold tailWord_4031745
  simp only [CollatzResearch.WordTrace]
  refine ⟨147049820778683907071472689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98033213852455938047648459 147049820778683907071472689)
  ·
    refine ⟨110287365584012930303604517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147049820778683907071472689 110287365584012930303604517)
    ·
      refine ⟨20678881047002424431925847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110287365584012930303604517 20678881047002424431925847)
      ·
        refine ⟨31018321570503636647888771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20678881047002424431925847 31018321570503636647888771)
        ·
          refine ⟨46527482355755454971833157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31018321570503636647888771 46527482355755454971833157)
          ·
            refine ⟨8723902941704147807218717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46527482355755454971833157 8723902941704147807218717)
            ·
              refine ⟨3271463603139055427707019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8723902941704147807218717 3271463603139055427707019)
              ·
                refine ⟨4907195404708583141560529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271463603139055427707019 4907195404708583141560529)
                ·
                  refine ⟨3680396553531437356170397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4907195404708583141560529 3680396553531437356170397)
                  ·
                    refine ⟨1380148707574289008563899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3680396553531437356170397 1380148707574289008563899)
                    ·
                      rfl

theorem cell22_4031745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_4031745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031745 prefixEnd_4031745 := by exact prefixLift 4031745
  have htrace : WordTrace (prefixWord ++ tailWord_4031745) baseStart_4031745 baseEnd_4031745 := by
    simpa [prefixWord, tailWord_4031745, baseEnd_4031745] using wordTrace_append hprefix tailTrace_4031745
  have hstable : (prefixWord ++ tailWord_4031745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031745).length < 2 ^ (prefixWord ++ tailWord_4031745).sum := by decide
  have hdescent : baseEnd_4031745 < baseStart_4031745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031758 : List Nat := [4, 1, 1, 2, 1, 5, 2, 6]
def baseStart_4031758 : Nat := 118140960795 + 4031758 * 2 ^ 59
def prefixEnd_4031758 : Nat := 4983230072969 + 3 ^ 40 * 4031758 * 2
def baseEnd_4031758 : Nat := 153350350859995700887651

theorem tailTrace_4031758 : CollatzResearch.WordTrace tailWord_4031758 prefixEnd_4031758 153350350859995700887651 := by
  unfold tailWord_4031758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18381286865954601286461991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98033529951757873527797285 18381286865954601286461991)
  ·
    refine ⟨27571930298931901929692987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18381286865954601286461991 27571930298931901929692987)
    ·
      refine ⟨41357895448397852894539481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27571930298931901929692987 41357895448397852894539481)
      ·
        refine ⟨31018421586298389670904611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41357895448397852894539481 31018421586298389670904611)
        ·
          refine ⟨46527632379447584506356917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31018421586298389670904611 46527632379447584506356917)
          ·
            refine ⟨4361965535573211047470961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46527632379447584506356917 4361965535573211047470961)
            ·
              refine ⟨3271474151679908285603221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4361965535573211047470961 3271474151679908285603221)
              ·
                refine ⟨153350350859995700887651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3271474151679908285603221 153350350859995700887651)
                ·
                  rfl

theorem cell22_4031758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_4031758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031758 prefixEnd_4031758 := by exact prefixLift 4031758
  have htrace : WordTrace (prefixWord ++ tailWord_4031758) baseStart_4031758 baseEnd_4031758 := by
    simpa [prefixWord, tailWord_4031758, baseEnd_4031758] using wordTrace_append hprefix tailTrace_4031758
  have hstable : (prefixWord ++ tailWord_4031758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031758).length < 2 ^ (prefixWord ++ tailWord_4031758).sum := by decide
  have hdescent : baseEnd_4031758 < baseStart_4031758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031799 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 1, 10]
def baseStart_4031799 : Nat := 118140960795 + 4031799 * 2 ^ 59
def prefixEnd_4031799 : Nat := 4983230072969 + 3 ^ 40 * 4031799 * 2
def baseEnd_4031799 : Nat := 1380167192877850867713733

theorem tailTrace_4031799 : CollatzResearch.WordTrace tailWord_4031799 prefixEnd_4031799 1380167192877850867713733 := by
  unfold tailWord_4031799
  simp only [CollatzResearch.WordTrace]
  refine ⟨147051790320488274293938451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98034526880325516195958967 147051790320488274293938451)
  ·
    refine ⟨220577685480732411440907677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147051790320488274293938451 220577685480732411440907677)
    ·
      refine ⟨82716632055274654290340379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220577685480732411440907677 82716632055274654290340379)
      ·
        refine ⟨124074948082911981435510569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82716632055274654290340379 124074948082911981435510569)
        ·
          refine ⟨93056211062183986076632927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124074948082911981435510569 93056211062183986076632927)
          ·
            refine ⟨139584316593275979114949391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93056211062183986076632927 139584316593275979114949391)
            ·
              refine ⟨209376474889913968672424087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139584316593275979114949391 209376474889913968672424087)
              ·
                refine ⟨314064712334870953008636131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209376474889913968672424087 314064712334870953008636131)
                ·
                  refine ⟨471097068502306429512954197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314064712334870953008636131 471097068502306429512954197)
                  ·
                    refine ⟨1380167192877850867713733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 471097068502306429512954197 1380167192877850867713733)
                    ·
                      rfl

theorem cell22_4031799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_4031799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031799 prefixEnd_4031799 := by exact prefixLift 4031799
  have htrace : WordTrace (prefixWord ++ tailWord_4031799) baseStart_4031799 baseEnd_4031799 := by
    simpa [prefixWord, tailWord_4031799, baseEnd_4031799] using wordTrace_append hprefix tailTrace_4031799
  have hstable : (prefixWord ++ tailWord_4031799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031799).length < 2 ^ (prefixWord ++ tailWord_4031799).sum := by decide
  have hdescent : baseEnd_4031799 < baseStart_4031799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031863 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 2, 3]
def baseStart_4031863 : Nat := 118140960795 + 4031863 * 2 ^ 59
def prefixEnd_4031863 : Nat := 4983230072969 + 3 ^ 40 * 4031863 * 2
def baseEnd_4031863 : Nat := 1380189101385776034113537

theorem tailTrace_4031863 : CollatzResearch.WordTrace tailWord_4031863 prefixEnd_4031863 1380189101385776034113537 := by
  unfold tailWord_4031863
  simp only [CollatzResearch.WordTrace]
  refine ⟨147054124592256413224268243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98036083061504275482845495 147054124592256413224268243)
  ·
    refine ⟨220581186888384619836402365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147054124592256413224268243 220581186888384619836402365)
    ·
      refine ⟨82717945083144232438650887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220581186888384619836402365 82717945083144232438650887)
      ·
        refine ⟨124076917624716348657976331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82717945083144232438650887 124076917624716348657976331)
        ·
          refine ⟨186115376437074522986964497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124076917624716348657976331 186115376437074522986964497)
          ·
            refine ⟨139586532327805892240223373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186115376437074522986964497 139586532327805892240223373)
            ·
              refine ⟨52344949622927209590083765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139586532327805892240223373 52344949622927209590083765)
              ·
                refine ⟨4907339027149425899070353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52344949622927209590083765 4907339027149425899070353)
                ·
                  refine ⟨3680504270362069424302765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4907339027149425899070353 3680504270362069424302765)
                  ·
                    refine ⟨1380189101385776034113537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3680504270362069424302765 1380189101385776034113537)
                    ·
                      rfl

theorem cell22_4031863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_4031863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031863 prefixEnd_4031863 := by exact prefixLift 4031863
  have htrace : WordTrace (prefixWord ++ tailWord_4031863) baseStart_4031863 baseEnd_4031863 := by
    simpa [prefixWord, tailWord_4031863, baseEnd_4031863] using wordTrace_append hprefix tailTrace_4031863
  have hstable : (prefixWord ++ tailWord_4031863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031863).length < 2 ^ (prefixWord ++ tailWord_4031863).sum := by decide
  have hdescent : baseEnd_4031863 < baseStart_4031863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031925 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 3, 3]
def baseStart_4031925 : Nat := 118140960795 + 4031925 * 2 ^ 59
def prefixEnd_4031925 : Nat := 4983230072969 + 3 ^ 40 * 4031925 * 2
def baseEnd_4031925 : Nat := 1380210325252828539063347

theorem tailTrace_4031925 : CollatzResearch.WordTrace tailWord_4031925 prefixEnd_4031925 1380210325252828539063347 := by
  unfold tailWord_4031925
  simp only [CollatzResearch.WordTrace]
  refine ⟨147056385918031797813025229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98037590612021198542016819 147056385918031797813025229)
  ·
    refine ⟨55146144719261924179884461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147056385918031797813025229 55146144719261924179884461)
    ·
      refine ⟨20679804269723221567456673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55146144719261924179884461 20679804269723221567456673)
      ·
        refine ⟨15509853202292416175592505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20679804269723221567456673 15509853202292416175592505)
        ·
          refine ⟨11632389901719312131694379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15509853202292416175592505 11632389901719312131694379)
          ·
            refine ⟨17448584852578968197541569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11632389901719312131694379 17448584852578968197541569)
            ·
              refine ⟨13086438639434226148156177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17448584852578968197541569 13086438639434226148156177)
              ·
                refine ⟨9814828979575669611117133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13086438639434226148156177 9814828979575669611117133)
                ·
                  refine ⟨3680560867340876104168925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9814828979575669611117133 3680560867340876104168925)
                  ·
                    refine ⟨1380210325252828539063347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3680560867340876104168925 1380210325252828539063347)
                    ·
                      rfl

theorem cell22_4031925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_4031925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031925 prefixEnd_4031925 := by exact prefixLift 4031925
  have htrace : WordTrace (prefixWord ++ tailWord_4031925) baseStart_4031925 baseEnd_4031925 := by
    simpa [prefixWord, tailWord_4031925, baseEnd_4031925] using wordTrace_append hprefix tailTrace_4031925
  have hstable : (prefixWord ++ tailWord_4031925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031925).length < 2 ^ (prefixWord ++ tailWord_4031925).sum := by decide
  have hdescent : baseEnd_4031925 < baseStart_4031925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031936 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_4031936 : Nat := 118140960795 + 4031936 * 2 ^ 59
def prefixEnd_4031936 : Nat := 4983230072969 + 3 ^ 40 * 4031936 * 2
def baseEnd_4031936 : Nat := 1380214090777628177038313

theorem tailTrace_4031936 : CollatzResearch.WordTrace tailWord_4031936 prefixEnd_4031936 1380214090777628177038313 := by
  unfold tailWord_4031936
  simp only [CollatzResearch.WordTrace]
  refine ⟨73528393560495973345837831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98037858080661297794450441 73528393560495973345837831)
  ·
    refine ⟨110292590340743960018756747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73528393560495973345837831 110292590340743960018756747)
    ·
      refine ⟨165438885511115940028135121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110292590340743960018756747 165438885511115940028135121)
      ·
        refine ⟨124079164133336955021101341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165438885511115940028135121 124079164133336955021101341)
        ·
          refine ⟨46529686550001358132913003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124079164133336955021101341 46529686550001358132913003)
          ·
            refine ⟨69794529825002037199369505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46529686550001358132913003 69794529825002037199369505)
            ·
              refine ⟨52345897368751527899527129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69794529825002037199369505 52345897368751527899527129)
              ·
                refine ⟨39259423026563645924645347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52345897368751527899527129 39259423026563645924645347)
                ·
                  refine ⟨58889134539845468886968021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39259423026563645924645347 58889134539845468886968021)
                  ·
                    refine ⟨1380214090777628177038313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58889134539845468886968021 1380214090777628177038313)
                    ·
                      rfl

theorem cell22_4031936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_4031936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031936 prefixEnd_4031936 := by exact prefixLift 4031936
  have htrace : WordTrace (prefixWord ++ tailWord_4031936) baseStart_4031936 baseEnd_4031936 := by
    simpa [prefixWord, tailWord_4031936, baseEnd_4031936] using wordTrace_append hprefix tailTrace_4031936
  have hstable : (prefixWord ++ tailWord_4031936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031936).length < 2 ^ (prefixWord ++ tailWord_4031936).sum := by decide
  have hdescent : baseEnd_4031936 < baseStart_4031936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031985 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 1, 4]
def baseStart_4031985 : Nat := 118140960795 + 4031985 * 2 ^ 59
def prefixEnd_4031985 : Nat := 4983230072969 + 3 ^ 40 * 4031985 * 2
def baseEnd_4031985 : Nat := 1380230864479008382563163

theorem tailTrace_4031985 : CollatzResearch.WordTrace tailWord_4031985 prefixEnd_4031985 1380230864479008382563163 := by
  unfold tailWord_4031985
  simp only [CollatzResearch.WordTrace]
  refine ⟨147058574297814428060209409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98039049531876285373472939 147058574297814428060209409)
  ·
    refine ⟨110293930723360821045157057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147058574297814428060209409 110293930723360821045157057)
    ·
      refine ⟨82720448042520615783867793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110293930723360821045157057 82720448042520615783867793)
      ·
        refine ⟨62040336031890461837900845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82720448042520615783867793 62040336031890461837900845)
        ·
          refine ⟨23265126011958923189212817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62040336031890461837900845 23265126011958923189212817)
          ·
            refine ⟨17448844508969192391909613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23265126011958923189212817 17448844508969192391909613)
            ·
              refine ⟨6543316690863447146966105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17448844508969192391909613 6543316690863447146966105)
              ·
                refine ⟨4907487518147585360224579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6543316690863447146966105 4907487518147585360224579)
                ·
                  refine ⟨7361231277221378040336869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4907487518147585360224579 7361231277221378040336869)
                  ·
                    refine ⟨1380230864479008382563163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7361231277221378040336869 1380230864479008382563163)
                    ·
                      rfl

theorem cell22_4031985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_4031985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031985 prefixEnd_4031985 := by exact prefixLift 4031985
  have htrace : WordTrace (prefixWord ++ tailWord_4031985) baseStart_4031985 baseEnd_4031985 := by
    simpa [prefixWord, tailWord_4031985, baseEnd_4031985] using wordTrace_append hprefix tailTrace_4031985
  have hstable : (prefixWord ++ tailWord_4031985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031985).length < 2 ^ (prefixWord ++ tailWord_4031985).sum := by decide
  have hdescent : baseEnd_4031985 < baseStart_4031985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032006 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4032006 : Nat := 118140960795 + 4032006 * 2 ^ 59
def prefixEnd_4032006 : Nat := 4983230072969 + 3 ^ 40 * 4032006 * 2
def baseEnd_4032006 : Nat := 460079351069390442596033

theorem tailTrace_4032006 : CollatzResearch.WordTrace tailWord_4032006 prefixEnd_4032006 460079351069390442596033 := by
  unfold tailWord_4032006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4595604382210573395210121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98039560153825565764482581 4595604382210573395210121)
  ·
    refine ⟨3446703286657930046407591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4595604382210573395210121 3446703286657930046407591)
    ·
      refine ⟨5170054929986895069611387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3446703286657930046407591 5170054929986895069611387)
      ·
        refine ⟨7755082394980342604417081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170054929986895069611387 7755082394980342604417081)
        ·
          refine ⟨5816311796235256953312811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7755082394980342604417081 5816311796235256953312811)
          ·
            refine ⟨8724467694352885429969217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816311796235256953312811 8724467694352885429969217)
            ·
              refine ⟨6543350770764664072476913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8724467694352885429969217 6543350770764664072476913)
              ·
                refine ⟨4907513078073498054357685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6543350770764664072476913 4907513078073498054357685)
                ·
                  refine ⟨460079351069390442596033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4907513078073498054357685 460079351069390442596033)
                  ·
                    rfl

theorem cell22_4032006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4032006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032006 prefixEnd_4032006 := by exact prefixLift 4032006
  have htrace : WordTrace (prefixWord ++ tailWord_4032006) baseStart_4032006 baseEnd_4032006 := by
    simpa [prefixWord, tailWord_4032006, baseEnd_4032006] using wordTrace_append hprefix tailTrace_4032006
  have hstable : (prefixWord ++ tailWord_4032006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032006).length < 2 ^ (prefixWord ++ tailWord_4032006).sum := by decide
  have hdescent : baseEnd_4032006 < baseStart_4032006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032011 : List Nat := [1, 1, 1, 1, 18]
def baseStart_4032011 : Nat := 118140960795 + 4032011 * 2 ^ 59
def prefixEnd_4032011 : Nat := 4983230072969 + 3 ^ 40 * 4032011 * 2
def baseEnd_4032011 : Nat := 5679999032141370293881

theorem tailTrace_4032011 : CollatzResearch.WordTrace tailWord_4032011 prefixEnd_4032011 5679999032141370293881 := by
  unfold tailWord_4032011
  simp only [CollatzResearch.WordTrace]
  refine ⟨147059522595720234500655887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98039681730480156333770591 147059522595720234500655887)
  ·
    refine ⟨220589283893580351750983831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147059522595720234500655887 220589283893580351750983831)
    ·
      refine ⟨330883925840370527626475747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220589283893580351750983831 330883925840370527626475747)
      ·
        refine ⟨496325888760555791439713621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330883925840370527626475747 496325888760555791439713621)
        ·
          refine ⟨5679999032141370293881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 18 496325888760555791439713621 5679999032141370293881)
          ·
            rfl

theorem cell22_4032011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 18].length) (baseStart_4032011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032011 prefixEnd_4032011 := by exact prefixLift 4032011
  have htrace : WordTrace (prefixWord ++ tailWord_4032011) baseStart_4032011 baseEnd_4032011 := by
    simpa [prefixWord, tailWord_4032011, baseEnd_4032011] using wordTrace_append hprefix tailTrace_4032011
  have hstable : (prefixWord ++ tailWord_4032011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032011).length < 2 ^ (prefixWord ++ tailWord_4032011).sum := by decide
  have hdescent : baseEnd_4032011 < baseStart_4032011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032032 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 2, 3]
def baseStart_4032032 : Nat := 118140960795 + 4032032 * 2 ^ 59
def prefixEnd_4032032 : Nat := 4983230072969 + 3 ^ 40 * 4032032 * 2
def baseEnd_4032032 : Nat := 1380246953539515926638019

theorem tailTrace_4032032 : CollatzResearch.WordTrace tailWord_4032032 prefixEnd_4032032 1380246953539515926638019 := by
  unfold tailWord_4032032
  simp only [CollatzResearch.WordTrace]
  refine ⟨73530144264322077543585175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98040192352429436724780233 73530144264322077543585175)
  ·
    refine ⟨110295216396483116315377763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73530144264322077543585175 110295216396483116315377763)
    ·
      refine ⟨165442824594724674473066645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110295216396483116315377763 165442824594724674473066645)
      ·
        refine ⟨7755132402877719115924999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165442824594724674473066645 7755132402877719115924999)
        ·
          refine ⟨11632698604316578673887499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7755132402877719115924999 11632698604316578673887499)
          ·
            refine ⟨17449047906474868010831249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11632698604316578673887499 17449047906474868010831249)
            ·
              refine ⟨13086785929856151008123437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17449047906474868010831249 13086785929856151008123437)
              ·
                refine ⟨4907544723696056628046289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13086785929856151008123437 4907544723696056628046289)
                ·
                  refine ⟨3680658542772042471034717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4907544723696056628046289 3680658542772042471034717)
                  ·
                    refine ⟨1380246953539515926638019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3680658542772042471034717 1380246953539515926638019)
                    ·
                      rfl

theorem cell22_4032032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2, 3].length) (baseStart_4032032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032032 prefixEnd_4032032 := by exact prefixLift 4032032
  have htrace : WordTrace (prefixWord ++ tailWord_4032032) baseStart_4032032 baseEnd_4032032 := by
    simpa [prefixWord, tailWord_4032032, baseEnd_4032032] using wordTrace_append hprefix tailTrace_4032032
  have hstable : (prefixWord ++ tailWord_4032032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032032).length < 2 ^ (prefixWord ++ tailWord_4032032).sum := by decide
  have hdescent : baseEnd_4032032 < baseStart_4032032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032135 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 6]
def baseStart_4032135 : Nat := 118140960795 + 4032135 * 2 ^ 59
def prefixEnd_4032135 : Nat := 4983230072969 + 3 ^ 40 * 4032135 * 2
def baseEnd_4032135 : Nat := 460094070848152663770901

theorem tailTrace_4032135 : CollatzResearch.WordTrace tailWord_4032135 prefixEnd_4032135 460094070848152663770901 := by
  unfold tailWord_4032135
  simp only [CollatzResearch.WordTrace]
  refine ⟨147064045247271003678169859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98042696831514002452113239 147064045247271003678169859)
  ·
    refine ⟨220596067870906505517254789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147064045247271003678169859 220596067870906505517254789)
    ·
      refine ⟨41361762725794969784485273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220596067870906505517254789 41361762725794969784485273)
      ·
        refine ⟨31021322044346227338363955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41361762725794969784485273 31021322044346227338363955)
        ·
          refine ⟨46531983066519341007545933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31021322044346227338363955 46531983066519341007545933)
          ·
            refine ⟨17449493649944752877829725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46531983066519341007545933 17449493649944752877829725)
            ·
              refine ⟨6543560118729282329186147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17449493649944752877829725 6543560118729282329186147)
              ·
                refine ⟨9815340178093923493779221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543560118729282329186147 9815340178093923493779221)
                ·
                  refine ⟨460094070848152663770901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9815340178093923493779221 460094070848152663770901)
                  ·
                    rfl

theorem cell22_4032135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 6].length) (baseStart_4032135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032135 prefixEnd_4032135 := by exact prefixLift 4032135
  have htrace : WordTrace (prefixWord ++ tailWord_4032135) baseStart_4032135 baseEnd_4032135 := by
    simpa [prefixWord, tailWord_4032135, baseEnd_4032135] using wordTrace_append hprefix tailTrace_4032135
  have hstable : (prefixWord ++ tailWord_4032135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032135).length < 2 ^ (prefixWord ++ tailWord_4032135).sum := by decide
  have hdescent : baseEnd_4032135 < baseStart_4032135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032163 : List Nat := [1, 1, 1, 4, 1, 1, 3, 10]
def baseStart_4032163 : Nat := 118140960795 + 4032163 * 2 ^ 59
def prefixEnd_4032163 : Nat := 4983230072969 + 3 ^ 40 * 4032163 * 2
def baseEnd_4032163 : Nat := 153365755279630583512513

theorem tailTrace_4032163 : CollatzResearch.WordTrace tailWord_4032163 prefixEnd_4032163 153365755279630583512513 := by
  unfold tailWord_4032163
  simp only [CollatzResearch.WordTrace]
  refine ⟨147065066491169564460189143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98043377660779709640126095 147065066491169564460189143)
  ·
    refine ⟨220597599736754346690283715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147065066491169564460189143 220597599736754346690283715)
    ·
      refine ⟨330896399605131520035425573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220597599736754346690283715 330896399605131520035425573)
      ·
        refine ⟨62043074925962160006642295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330896399605131520035425573 62043074925962160006642295)
        ·
          refine ⟨93064612388943240009963443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62043074925962160006642295 93064612388943240009963443)
          ·
            refine ⟨139596918583414860014945165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93064612388943240009963443 139596918583414860014945165)
            ·
              refine ⟨52348844468780572505604437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139596918583414860014945165 52348844468780572505604437)
              ·
                refine ⟨153365755279630583512513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52348844468780572505604437 153365755279630583512513)
                ·
                  rfl

theorem cell22_4032163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 10].length) (baseStart_4032163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032163 prefixEnd_4032163 := by exact prefixLift 4032163
  have htrace : WordTrace (prefixWord ++ tailWord_4032163) baseStart_4032163 baseEnd_4032163 := by
    simpa [prefixWord, tailWord_4032163, baseEnd_4032163] using wordTrace_append hprefix tailTrace_4032163
  have hstable : (prefixWord ++ tailWord_4032163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032163).length < 2 ^ (prefixWord ++ tailWord_4032163).sum := by decide
  have hdescent : baseEnd_4032163 < baseStart_4032163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032165 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_4032165 : Nat := 118140960795 + 4032165 * 2 ^ 59
def prefixEnd_4032165 : Nat := 4983230072969 + 3 ^ 40 * 4032165 * 2
def baseEnd_4032165 : Nat := 1380292482157547913062611

theorem tailTrace_4032165 : CollatzResearch.WordTrace tailWord_4032165 prefixEnd_4032165 1380292482157547913062611 := by
  unfold tailWord_4032165
  simp only [CollatzResearch.WordTrace]
  refine ⟨147065139437162318801761949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98043426291441545867841299 147065139437162318801761949)
  ·
    refine ⟨55149427288935869550660731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147065139437162318801761949 55149427288935869550660731)
    ·
      refine ⟨82724140933403804325991097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55149427288935869550660731 82724140933403804325991097)
      ·
        refine ⟨62043105700052853244493323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82724140933403804325991097 62043105700052853244493323)
        ·
          refine ⟨93064658550079279866739985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62043105700052853244493323 93064658550079279866739985)
          ·
            refine ⟨69798493912559459900054989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93064658550079279866739985 69798493912559459900054989)
            ·
              refine ⟨26174435217209797462520621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69798493912559459900054989 26174435217209797462520621)
              ·
                refine ⟨9815413206453674048445233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26174435217209797462520621 9815413206453674048445233)
                ·
                  refine ⟨7361559904840255536333925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9815413206453674048445233 7361559904840255536333925)
                  ·
                    refine ⟨1380292482157547913062611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7361559904840255536333925 1380292482157547913062611)
                    ·
                      rfl

theorem cell22_4032165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_4032165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032165 prefixEnd_4032165 := by exact prefixLift 4032165
  have htrace : WordTrace (prefixWord ++ tailWord_4032165) baseStart_4032165 baseEnd_4032165 := by
    simpa [prefixWord, tailWord_4032165, baseEnd_4032165] using wordTrace_append hprefix tailTrace_4032165
  have hstable : (prefixWord ++ tailWord_4032165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032165).length < 2 ^ (prefixWord ++ tailWord_4032165).sum := by decide
  have hdescent : baseEnd_4032165 < baseStart_4032165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032195 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 9, 3]
def baseStart_4032195 : Nat := 118140960795 + 4032195 * 2 ^ 59
def prefixEnd_4032195 : Nat := 4983230072969 + 3 ^ 40 * 4032195 * 2
def baseEnd_4032195 : Nat := 1380302751770637834812519

theorem tailTrace_4032195 : CollatzResearch.WordTrace tailWord_4032195 prefixEnd_4032195 1380302751770637834812519 := by
  unfold tailWord_4032195
  simp only [CollatzResearch.WordTrace]
  refine ⟨147066233627053633925354039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98044155751369089283569359 147066233627053633925354039)
  ·
    refine ⟨220599350440580450888031059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147066233627053633925354039 220599350440580450888031059)
    ·
      refine ⟨330899025660870676332046589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220599350440580450888031059 330899025660870676332046589)
      ·
        refine ⟨124087134622826503624517471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330899025660870676332046589 124087134622826503624517471)
        ·
          refine ⟨186130701934239755436776207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124087134622826503624517471 186130701934239755436776207)
          ·
            refine ⟨279196052901359633155164311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186130701934239755436776207 279196052901359633155164311)
            ·
              refine ⟨418794079352039449732746467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279196052901359633155164311 418794079352039449732746467)
              ·
                refine ⟨628191119028059174599119701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418794079352039449732746467 628191119028059174599119701)
                ·
                  refine ⟨3680807338055034226166717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 628191119028059174599119701 3680807338055034226166717)
                  ·
                    refine ⟨1380302751770637834812519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3680807338055034226166717 1380302751770637834812519)
                    ·
                      rfl

theorem cell22_4032195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 3].length) (baseStart_4032195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032195 prefixEnd_4032195 := by exact prefixLift 4032195
  have htrace : WordTrace (prefixWord ++ tailWord_4032195) baseStart_4032195 baseEnd_4032195 := by
    simpa [prefixWord, tailWord_4032195, baseEnd_4032195] using wordTrace_append hprefix tailTrace_4032195
  have hstable : (prefixWord ++ tailWord_4032195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032195).length < 2 ^ (prefixWord ++ tailWord_4032195).sum := by decide
  have hdescent : baseEnd_4032195 < baseStart_4032195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032246 : List Nat := [5, 1, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_4032246 : Nat := 118140960795 + 4032246 * 2 ^ 59
def prefixEnd_4032246 : Nat := 4983230072969 + 3 ^ 40 * 4032246 * 2
def baseEnd_4032246 : Nat := 1380320210112890701787363

theorem tailTrace_4032246 : CollatzResearch.WordTrace tailWord_4032246 prefixEnd_4032246 1380320210112890701787363 := by
  unfold tailWord_4032246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9191755859366804352216287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98045395833245913090307061 9191755859366804352216287)
  ·
    refine ⟨13787633789050206528324431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9191755859366804352216287 13787633789050206528324431)
    ·
      refine ⟨20681450683575309792486647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13787633789050206528324431 20681450683575309792486647)
      ·
        refine ⟨31022176025362964688729971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20681450683575309792486647 31022176025362964688729971)
        ·
          refine ⟨46533264038044447033094957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31022176025362964688729971 46533264038044447033094957)
          ·
            refine ⟨17449974014266667637410609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46533264038044447033094957 17449974014266667637410609)
            ·
              refine ⟨13087480510700000728057957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17449974014266667637410609 13087480510700000728057957)
              ·
                refine ⟨2453902595756250136510867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13087480510700000728057957 2453902595756250136510867)
                ·
                  refine ⟨3680853893634375204766301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453902595756250136510867 3680853893634375204766301)
                  ·
                    refine ⟨1380320210112890701787363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3680853893634375204766301 1380320210112890701787363)
                    ·
                      rfl

theorem cell22_4032246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_4032246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032246 prefixEnd_4032246 := by exact prefixLift 4032246
  have htrace : WordTrace (prefixWord ++ tailWord_4032246) baseStart_4032246 baseEnd_4032246 := by
    simpa [prefixWord, tailWord_4032246, baseEnd_4032246] using wordTrace_append hprefix tailTrace_4032246
  have hstable : (prefixWord ++ tailWord_4032246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032246).length < 2 ^ (prefixWord ++ tailWord_4032246).sum := by decide
  have hdescent : baseEnd_4032246 < baseStart_4032246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032255 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 5, 4]
def baseStart_4032255 : Nat := 118140960795 + 4032255 * 2 ^ 59
def prefixEnd_4032255 : Nat := 4983230072969 + 3 ^ 40 * 4032255 * 2
def baseEnd_4032255 : Nat := 1380323290996817678312335

theorem tailTrace_4032255 : CollatzResearch.WordTrace tailWord_4032255 prefixEnd_4032255 1380323290996817678312335 := by
  unfold tailWord_4032255
  simp only [CollatzResearch.WordTrace]
  refine ⟨147068422006836264172538219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98045614671224176115025479 147068422006836264172538219)
  ·
    refine ⟨220602633010254396258807329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147068422006836264172538219 220602633010254396258807329)
    ·
      refine ⟨165451974757690797194105497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220602633010254396258807329 165451974757690797194105497)
      ·
        refine ⟨124088981068268097895579123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165451974757690797194105497 124088981068268097895579123)
        ·
          refine ⟨186133471602402146843368685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124088981068268097895579123 186133471602402146843368685)
          ·
            refine ⟨69800051850900805066263257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186133471602402146843368685 69800051850900805066263257)
            ·
              refine ⟨52350038888175603799697443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69800051850900805066263257 52350038888175603799697443)
              ·
                refine ⟨78525058332263405699546165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52350038888175603799697443 78525058332263405699546165)
                ·
                  refine ⟨7361724218649694284332453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78525058332263405699546165 7361724218649694284332453)
                  ·
                    refine ⟨1380323290996817678312335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7361724218649694284332453 1380323290996817678312335)
                    ·
                      rfl

theorem cell22_4032255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_4032255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032255 prefixEnd_4032255 := by exact prefixLift 4032255
  have htrace : WordTrace (prefixWord ++ tailWord_4032255) baseStart_4032255 baseEnd_4032255 := by
    simpa [prefixWord, tailWord_4032255, baseEnd_4032255] using wordTrace_append hprefix tailTrace_4032255
  have hstable : (prefixWord ++ tailWord_4032255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032255).length < 2 ^ (prefixWord ++ tailWord_4032255).sum := by decide
  have hdescent : baseEnd_4032255 < baseStart_4032255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032377 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 5]
def baseStart_4032377 : Nat := 118140960795 + 4032377 * 2 ^ 59
def prefixEnd_4032377 : Nat := 4983230072969 + 3 ^ 40 * 4032377 * 2
def baseEnd_4032377 : Nat := 460121684696683342253987

theorem tailTrace_4032377 : CollatzResearch.WordTrace tailWord_4032377 prefixEnd_4032377 460121684696683342253987 := by
  unfold tailWord_4032377
  simp only [CollatzResearch.WordTrace]
  refine ⟨147072871712394279008479385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98048581141596186005652923 147072871712394279008479385)
  ·
    refine ⟨110304653784295709256359539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147072871712394279008479385 110304653784295709256359539)
    ·
      refine ⟨165456980676443563884539309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110304653784295709256359539 165456980676443563884539309)
      ·
        refine ⟨62046367753666336456702241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165456980676443563884539309 62046367753666336456702241)
        ·
          refine ⟨46534775815249752342526681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62046367753666336456702241 46534775815249752342526681)
          ·
            refine ⟨34901081861437314256895011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46534775815249752342526681 34901081861437314256895011)
            ·
              refine ⟨52351622792155971385342517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34901081861437314256895011 52351622792155971385342517)
              ·
                refine ⟨4907964636764622317375861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52351622792155971385342517 4907964636764622317375861)
                ·
                  refine ⟨460121684696683342253987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4907964636764622317375861 460121684696683342253987)
                  ·
                    rfl

theorem cell22_4032377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_4032377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032377 prefixEnd_4032377 := by exact prefixLift 4032377
  have htrace : WordTrace (prefixWord ++ tailWord_4032377) baseStart_4032377 baseEnd_4032377 := by
    simpa [prefixWord, tailWord_4032377, baseEnd_4032377] using wordTrace_append hprefix tailTrace_4032377
  have hstable : (prefixWord ++ tailWord_4032377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032377).length < 2 ^ (prefixWord ++ tailWord_4032377).sum := by decide
  have hdescent : baseEnd_4032377 < baseStart_4032377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032456 : List Nat := [2, 1, 3, 1, 4, 1, 3, 3, 4]
def baseStart_4032456 : Nat := 118140960795 + 4032456 * 2 ^ 59
def prefixEnd_4032456 : Nat := 4983230072969 + 3 ^ 40 * 4032456 * 2
def baseEnd_4032456 : Nat := 460130699134840051345573

theorem tailTrace_4032456 : CollatzResearch.WordTrace tailWord_4032456 prefixEnd_4032456 460130699134840051345573 := by
  unfold tailWord_4032456
  simp only [CollatzResearch.WordTrace]
  refine ⟨73537876539554037750302611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98050502052738717000403481 73537876539554037750302611)
  ·
    refine ⟨110306814809331056625453917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73537876539554037750302611 110306814809331056625453917)
    ·
      refine ⟨41365055553499146234545219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110306814809331056625453917 41365055553499146234545219)
      ·
        refine ⟨62047583330248719351817829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41365055553499146234545219 62047583330248719351817829)
        ·
          refine ⟨11633921874421634878465843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62047583330248719351817829 11633921874421634878465843)
          ·
            refine ⟨17450882811632452317698765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11633921874421634878465843 17450882811632452317698765)
            ·
              refine ⟨6544081054362169619137037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17450882811632452317698765 6544081054362169619137037)
              ·
                refine ⟨2454030395385813607176389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6544081054362169619137037 2454030395385813607176389)
                ·
                  refine ⟨460130699134840051345573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2454030395385813607176389 460130699134840051345573)
                  ·
                    rfl

theorem cell22_4032456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 4].length) (baseStart_4032456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032456 prefixEnd_4032456 := by exact prefixLift 4032456
  have htrace : WordTrace (prefixWord ++ tailWord_4032456) baseStart_4032456 baseEnd_4032456 := by
    simpa [prefixWord, tailWord_4032456, baseEnd_4032456] using wordTrace_append hprefix tailTrace_4032456
  have hstable : (prefixWord ++ tailWord_4032456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032456).length < 2 ^ (prefixWord ++ tailWord_4032456).sum := by decide
  have hdescent : baseEnd_4032456 < baseStart_4032456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032469 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_4032469 : Nat := 118140960795 + 4032469 * 2 ^ 59
def prefixEnd_4032469 : Nat := 4983230072969 + 3 ^ 40 * 4032469 * 2
def baseEnd_4032469 : Nat := 1380396547570192453461679

theorem tailTrace_4032469 : CollatzResearch.WordTrace tailWord_4032469 prefixEnd_4032469 1380396547570192453461679 := by
  unfold tailWord_4032469
  simp only [CollatzResearch.WordTrace]
  refine ⟨147076227228060978720828461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98050818152040652480552307 147076227228060978720828461)
  ·
    refine ⟨55153585210522867020310673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147076227228060978720828461 55153585210522867020310673)
    ·
      refine ⟨41365188907892150265233005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55153585210522867020310673 41365188907892150265233005)
      ·
        refine ⟨15511945840459556349462377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41365188907892150265233005 15511945840459556349462377)
        ·
          refine ⟨11633959380344667262096783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15511945840459556349462377 11633959380344667262096783)
          ·
            refine ⟨17450939070517000893145175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11633959380344667262096783 17450939070517000893145175)
            ·
              refine ⟨26176408605775501339717763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17450939070517000893145175 26176408605775501339717763)
              ·
                refine ⟨39264612908663252009576645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26176408605775501339717763 39264612908663252009576645)
                ·
                  refine ⟨7362114920374359751795621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39264612908663252009576645 7362114920374359751795621)
                  ·
                    refine ⟨1380396547570192453461679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7362114920374359751795621 1380396547570192453461679)
                    ·
                      rfl

theorem cell22_4032469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_4032469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032469 prefixEnd_4032469 := by exact prefixLift 4032469
  have htrace : WordTrace (prefixWord ++ tailWord_4032469) baseStart_4032469 baseEnd_4032469 := by
    simpa [prefixWord, tailWord_4032469, baseEnd_4032469] using wordTrace_append hprefix tailTrace_4032469
  have hstable : (prefixWord ++ tailWord_4032469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032469).length < 2 ^ (prefixWord ++ tailWord_4032469).sum := by decide
  have hdescent : baseEnd_4032469 < baseStart_4032469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032473 : List Nat := [1, 2, 1, 2, 6, 1, 3, 2, 4]
def baseStart_4032473 : Nat := 118140960795 + 4032473 * 2 ^ 59
def prefixEnd_4032473 : Nat := 4983230072969 + 3 ^ 40 * 4032473 * 2
def baseEnd_4032473 : Nat := 460132638950645925453889

theorem tailTrace_4032473 : CollatzResearch.WordTrace tailWord_4032473 prefixEnd_4032473 460132638950645925453889 := by
  unfold tailWord_4032473
  simp only [CollatzResearch.WordTrace]
  refine ⟨147076373120046487403974073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98050915413364324935982715 147076373120046487403974073)
  ·
    refine ⟨110307279840034865552980555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147076373120046487403974073 110307279840034865552980555)
    ·
      refine ⟨165460919760052298329470833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110307279840034865552980555 165460919760052298329470833)
      ·
        refine ⟨124095689820039223747103125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165460919760052298329470833 124095689820039223747103125)
        ·
          refine ⟨5816985460314338613145459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124095689820039223747103125 5816985460314338613145459)
          ·
            refine ⟨8725478190471507919718189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816985460314338613145459 8725478190471507919718189)
            ·
              refine ⟨3272054321426815469894321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8725478190471507919718189 3272054321426815469894321)
              ·
                refine ⟨2454040741070111602420741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3272054321426815469894321 2454040741070111602420741)
                ·
                  refine ⟨460132638950645925453889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2454040741070111602420741 460132638950645925453889)
                  ·
                    rfl

theorem cell22_4032473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 4].length) (baseStart_4032473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032473 prefixEnd_4032473 := by exact prefixLift 4032473
  have htrace : WordTrace (prefixWord ++ tailWord_4032473) baseStart_4032473 baseEnd_4032473 := by
    simpa [prefixWord, tailWord_4032473, baseEnd_4032473] using wordTrace_append hprefix tailTrace_4032473
  have hstable : (prefixWord ++ tailWord_4032473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032473).length < 2 ^ (prefixWord ++ tailWord_4032473).sum := by decide
  have hdescent : baseEnd_4032473 < baseStart_4032473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032499 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 3, 3]
def baseStart_4032499 : Nat := 118140960795 + 4032499 * 2 ^ 59
def prefixEnd_4032499 : Nat := 4983230072969 + 3 ^ 40 * 4032499 * 2
def baseEnd_4032499 : Nat := 1380406817183282375211587

theorem tailTrace_4032499 : CollatzResearch.WordTrace tailWord_4032499 prefixEnd_4032499 1380406817183282375211587 := by
  unfold tailWord_4032499
  simp only [CollatzResearch.WordTrace]
  refine ⟨147077321417952293844420551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98051547611968195896280367 147077321417952293844420551)
  ·
    refine ⟨220615982126928440766630827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147077321417952293844420551 220615982126928440766630827)
    ·
      refine ⟨330923973190392661149946241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220615982126928440766630827 330923973190392661149946241)
      ·
        refine ⟨248192979892794495862459681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330923973190392661149946241 248192979892794495862459681)
        ·
          refine ⟨186144734919595871896844761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248192979892794495862459681 186144734919595871896844761)
          ·
            refine ⟨139608551189696903922633571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186144734919595871896844761 139608551189696903922633571)
            ·
              refine ⟨209412826784545355883950357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139608551189696903922633571 209412826784545355883950357)
              ·
                refine ⟨9816226255525563557060173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209412826784545355883950357 9816226255525563557060173)
                ·
                  refine ⟨3681084845822086333897565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9816226255525563557060173 3681084845822086333897565)
                  ·
                    refine ⟨1380406817183282375211587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3681084845822086333897565 1380406817183282375211587)
                    ·
                      rfl

theorem cell22_4032499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 3].length) (baseStart_4032499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032499 prefixEnd_4032499 := by exact prefixLift 4032499
  have htrace : WordTrace (prefixWord ++ tailWord_4032499) baseStart_4032499 baseEnd_4032499 := by
    simpa [prefixWord, tailWord_4032499, baseEnd_4032499] using wordTrace_append hprefix tailTrace_4032499
  have hstable : (prefixWord ++ tailWord_4032499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032499).length < 2 ^ (prefixWord ++ tailWord_4032499).sum := by decide
  have hdescent : baseEnd_4032499 < baseStart_4032499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032512 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 7]
def baseStart_4032512 : Nat := 118140960795 + 4032512 * 2 ^ 59
def prefixEnd_4032512 : Nat := 4983230072969 + 3 ^ 40 * 4032512 * 2
def baseEnd_4032512 : Nat := 460137089116318224878849

theorem tailTrace_4032512 : CollatzResearch.WordTrace tailWord_4032512 prefixEnd_4032512 460137089116318224878849 := by
  unfold tailWord_4032512
  simp only [CollatzResearch.WordTrace]
  refine ⟨73538897783452598532321895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98051863711270131376429193 73538897783452598532321895)
  ·
    refine ⟨110308346675178897798482843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73538897783452598532321895 110308346675178897798482843)
    ·
      refine ⟨165462520012768346697724265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110308346675178897798482843 165462520012768346697724265)
      ·
        refine ⟨124096890009576260023293199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165462520012768346697724265 124096890009576260023293199)
        ·
          refine ⟨186145335014364390034939799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124096890009576260023293199 186145335014364390034939799)
          ·
            refine ⟨279218002521546585052409699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186145335014364390034939799 279218002521546585052409699)
            ·
              refine ⟨418827003782319877578614549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279218002521546585052409699 418827003782319877578614549)
              ·
                refine ⟨19632515802296244261497557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 418827003782319877578614549 19632515802296244261497557)
                ·
                  refine ⟨460137089116318224878849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19632515802296244261497557 460137089116318224878849)
                  ·
                    rfl

theorem cell22_4032512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_4032512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032512 prefixEnd_4032512 := by exact prefixLift 4032512
  have htrace : WordTrace (prefixWord ++ tailWord_4032512) baseStart_4032512 baseEnd_4032512 := by
    simpa [prefixWord, tailWord_4032512, baseEnd_4032512] using wordTrace_append hprefix tailTrace_4032512
  have hstable : (prefixWord ++ tailWord_4032512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032512).length < 2 ^ (prefixWord ++ tailWord_4032512).sum := by decide
  have hdescent : baseEnd_4032512 < baseStart_4032512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032518 : List Nat := [6, 2, 1, 2, 11]
def baseStart_4032518 : Nat := 118140960795 + 4032518 * 2 ^ 59
def prefixEnd_4032518 : Nat := 4983230072969 + 3 ^ 40 * 4032518 * 2
def baseEnd_4032518 : Nat := 5680713256261615880603

theorem tailTrace_4032518 : CollatzResearch.WordTrace tailWord_4032518 prefixEnd_4032518 5680713256261615880603 := by
  unfold tailWord_4032518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596187950152608127792569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98052009603255640059574805 4596187950152608127792569)
  ·
    refine ⟨3447140962614456095844427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4596187950152608127792569 3447140962614456095844427)
    ·
      refine ⟨5170711443921684143766641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447140962614456095844427 5170711443921684143766641)
      ·
        refine ⟨3878033582941263107824981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5170711443921684143766641 3878033582941263107824981)
        ·
          refine ⟨5680713256261615880603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3878033582941263107824981 5680713256261615880603)
          ·
            rfl

theorem cell22_4032518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 11].length) (baseStart_4032518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032518 prefixEnd_4032518 := by exact prefixLift 4032518
  have htrace : WordTrace (prefixWord ++ tailWord_4032518) baseStart_4032518 baseEnd_4032518 := by
    simpa [prefixWord, tailWord_4032518, baseEnd_4032518] using wordTrace_append hprefix tailTrace_4032518
  have hstable : (prefixWord ++ tailWord_4032518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032518).length < 2 ^ (prefixWord ++ tailWord_4032518).sum := by decide
  have hdescent : baseEnd_4032518 < baseStart_4032518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032576 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 1, 4]
def baseStart_4032576 : Nat := 118140960795 + 4032576 * 2 ^ 59
def prefixEnd_4032576 : Nat := 4983230072969 + 3 ^ 40 * 4032576 * 2
def baseEnd_4032576 : Nat := 1380433175856879841036351

theorem tailTrace_4032576 : CollatzResearch.WordTrace tailWord_4032576 prefixEnd_4032576 1380433175856879841036351 := by
  unfold tailWord_4032576
  simp only [CollatzResearch.WordTrace]
  refine ⟨73540064919336667997486791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98053419892448890663315721 73540064919336667997486791)
  ·
    refine ⟨110310097379005001996230187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73540064919336667997486791 110310097379005001996230187)
    ·
      refine ⟨165465146068507502994345281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110310097379005001996230187 165465146068507502994345281)
      ·
        refine ⟨124098859551380627245758961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165465146068507502994345281 124098859551380627245758961)
        ·
          refine ⟨93074144663535470434319221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124098859551380627245758961 93074144663535470434319221)
          ·
            refine ⟨8725701062206450353217427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93074144663535470434319221 8725701062206450353217427)
            ·
              refine ⟨13088551593309675529826141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8725701062206450353217427 13088551593309675529826141)
              ·
                refine ⟨4908206847491128323684803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13088551593309675529826141 4908206847491128323684803)
                ·
                  refine ⟨7362310271236692485527205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908206847491128323684803 7362310271236692485527205)
                  ·
                    refine ⟨1380433175856879841036351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7362310271236692485527205 1380433175856879841036351)
                    ·
                      rfl

theorem cell22_4032576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_4032576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032576 prefixEnd_4032576 := by exact prefixLift 4032576
  have htrace : WordTrace (prefixWord ++ tailWord_4032576) baseStart_4032576 baseEnd_4032576 := by
    simpa [prefixWord, tailWord_4032576, baseEnd_4032576] using wordTrace_append hprefix tailTrace_4032576
  have hstable : (prefixWord ++ tailWord_4032576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032576).length < 2 ^ (prefixWord ++ tailWord_4032576).sum := by decide
  have hdescent : baseEnd_4032576 < baseStart_4032576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032610 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4032610 : Nat := 118140960795 + 4032610 * 2 ^ 59
def prefixEnd_4032610 : Nat := 4983230072969 + 3 ^ 40 * 4032610 * 2
def baseEnd_4032610 : Nat := 1380444814751715085686247

theorem tailTrace_4032610 : CollatzResearch.WordTrace tailWord_4032610 prefixEnd_4032610 1380444814751715085686247 := by
  unfold tailWord_4032610
  simp only [CollatzResearch.WordTrace]
  refine ⟨36770342480137539950427821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98054246613700106534474189 36770342480137539950427821)
  ·
    refine ⟨13788878430051577481410433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36770342480137539950427821 13788878430051577481410433)
    ·
      refine ⟨10341658822538683111057825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13788878430051577481410433 10341658822538683111057825)
      ·
        refine ⟨7756244116904012333293369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10341658822538683111057825 7756244116904012333293369)
        ·
          refine ⟨5817183087678009249970027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7756244116904012333293369 5817183087678009249970027)
          ·
            refine ⟨8725774631517013874955041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5817183087678009249970027 8725774631517013874955041)
            ·
              refine ⟨6544330973637760406216281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8725774631517013874955041 6544330973637760406216281)
              ·
                refine ⟨4908248230228320304662211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544330973637760406216281 4908248230228320304662211)
                ·
                  refine ⟨7362372345342480456993317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908248230228320304662211 7362372345342480456993317)
                  ·
                    refine ⟨1380444814751715085686247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7362372345342480456993317 1380444814751715085686247)
                    ·
                      rfl

theorem cell22_4032610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4032610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032610 prefixEnd_4032610 := by exact prefixLift 4032610
  have htrace : WordTrace (prefixWord ++ tailWord_4032610) baseStart_4032610 baseEnd_4032610 := by
    simpa [prefixWord, tailWord_4032610, baseEnd_4032610] using wordTrace_append hprefix tailTrace_4032610
  have hstable : (prefixWord ++ tailWord_4032610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032610).length < 2 ^ (prefixWord ++ tailWord_4032610).sum := by decide
  have hdescent : baseEnd_4032610 < baseStart_4032610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032621 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_4032621 : Nat := 118140960795 + 4032621 * 2 ^ 59
def prefixEnd_4032621 : Nat := 4983230072969 + 3 ^ 40 * 4032621 * 2
def baseEnd_4032621 : Nat := 1380448580276514723661213

theorem tailTrace_4032621 : CollatzResearch.WordTrace tailWord_4032621 prefixEnd_4032621 1380448580276514723661213 := by
  unfold tailWord_4032621
  simp only [CollatzResearch.WordTrace]
  refine ⟨147081771123510308680361717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98054514082340205786907811 147081771123510308680361717)
  ·
    refine ⟨13788916042829091438783911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147081771123510308680361717 13788916042829091438783911)
    ·
      refine ⟨20683374064243637158175867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13788916042829091438783911 20683374064243637158175867)
      ·
        refine ⟨31025061096365455737263801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20683374064243637158175867 31025061096365455737263801)
        ·
          refine ⟨23268795822274091802947851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31025061096365455737263801 23268795822274091802947851)
          ·
            refine ⟨34903193733411137704421777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23268795822274091802947851 34903193733411137704421777)
            ·
              refine ⟨26177395300058353278316333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34903193733411137704421777 26177395300058353278316333)
              ·
                refine ⟨9816523237521882479368625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26177395300058353278316333 9816523237521882479368625)
                ·
                  refine ⟨7362392428141411859526469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9816523237521882479368625 7362392428141411859526469)
                  ·
                    refine ⟨1380448580276514723661213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7362392428141411859526469 1380448580276514723661213)
                    ·
                      rfl

theorem cell22_4032621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_4032621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032621 prefixEnd_4032621 := by exact prefixLift 4032621
  have htrace : WordTrace (prefixWord ++ tailWord_4032621) baseStart_4032621 baseEnd_4032621 := by
    simpa [prefixWord, tailWord_4032621, baseEnd_4032621] using wordTrace_append hprefix tailTrace_4032621
  have hstable : (prefixWord ++ tailWord_4032621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032621).length < 2 ^ (prefixWord ++ tailWord_4032621).sum := by decide
  have hdescent : baseEnd_4032621 < baseStart_4032621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032649 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_4032649 : Nat := 118140960795 + 4032649 * 2 ^ 59
def prefixEnd_4032649 : Nat := 4983230072969 + 3 ^ 40 * 4032649 * 2
def baseEnd_4032649 : Nat := 1380458165248731983961127

theorem tailTrace_4032649 : CollatzResearch.WordTrace tailWord_4032649 prefixEnd_4032649 1380458165248731983961127 := by
  unfold tailWord_4032649
  simp only [CollatzResearch.WordTrace]
  refine ⟨147082792367408869462381001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98055194911605912974920667 147082792367408869462381001)
  ·
    refine ⟨110312094275556652096785751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147082792367408869462381001 110312094275556652096785751)
    ·
      refine ⟨165468141413334978145178627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110312094275556652096785751 165468141413334978145178627)
      ·
        refine ⟨248202212120002467217767941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165468141413334978145178627 248202212120002467217767941)
        ·
          refine ⟨46537914772500462603331489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248202212120002467217767941 46537914772500462603331489)
          ·
            refine ⟨34903436079375346952498617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46537914772500462603331489 34903436079375346952498617)
            ·
              refine ⟨26177577059531510214373963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34903436079375346952498617 26177577059531510214373963)
              ·
                refine ⟨39266365589297265321560945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26177577059531510214373963 39266365589297265321560945)
                ·
                  refine ⟨29449774191972948991170709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39266365589297265321560945 29449774191972948991170709)
                  ·
                    refine ⟨1380458165248731983961127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29449774191972948991170709 1380458165248731983961127)
                    ·
                      rfl

theorem cell22_4032649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_4032649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032649 prefixEnd_4032649 := by exact prefixLift 4032649
  have htrace : WordTrace (prefixWord ++ tailWord_4032649) baseStart_4032649 baseEnd_4032649 := by
    simpa [prefixWord, tailWord_4032649, baseEnd_4032649] using wordTrace_append hprefix tailTrace_4032649
  have hstable : (prefixWord ++ tailWord_4032649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032649).length < 2 ^ (prefixWord ++ tailWord_4032649).sum := by decide
  have hdescent : baseEnd_4032649 < baseStart_4032649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032702 : List Nat := [4, 2, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_4032702 : Nat := 118140960795 + 4032702 * 2 ^ 59
def prefixEnd_4032702 : Nat := 4983230072969 + 3 ^ 40 * 4032702 * 2
def baseEnd_4032702 : Nat := 1380476308231857512385965

theorem tailTrace_4032702 : CollatzResearch.WordTrace tailWord_4032702 prefixEnd_4032702 1380476308231857512385965 := by
  unfold tailWord_4032702
  simp only [CollatzResearch.WordTrace]
  refine ⟨18385590679527107439257545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98056483624144573009373573 18385590679527107439257545)
  ·
    refine ⟨13789193009645330579443159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18385590679527107439257545 13789193009645330579443159)
    ·
      refine ⟨20683789514467995869164739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13789193009645330579443159 20683789514467995869164739)
      ·
        refine ⟨31025684271701993803747109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20683789514467995869164739 31025684271701993803747109)
        ·
          refine ⟨5817315800944123838202583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31025684271701993803747109 5817315800944123838202583)
          ·
            refine ⟨8725973701416185757303875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5817315800944123838202583 8725973701416185757303875)
            ·
              refine ⟨13088960552124278635955813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8725973701416185757303875 13088960552124278635955813)
              ·
                refine ⟨2454180103523302244241715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13088960552124278635955813 2454180103523302244241715)
                ·
                  refine ⟨3681270155284953366362573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454180103523302244241715 3681270155284953366362573)
                  ·
                    refine ⟨1380476308231857512385965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3681270155284953366362573 1380476308231857512385965)
                    ·
                      rfl

theorem cell22_4032702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_4032702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032702 prefixEnd_4032702 := by exact prefixLift 4032702
  have htrace : WordTrace (prefixWord ++ tailWord_4032702) baseStart_4032702 baseEnd_4032702 := by
    simpa [prefixWord, tailWord_4032702, baseEnd_4032702] using wordTrace_append hprefix tailTrace_4032702
  have hstable : (prefixWord ++ tailWord_4032702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032702).length < 2 ^ (prefixWord ++ tailWord_4032702).sum := by decide
  have hdescent : baseEnd_4032702 < baseStart_4032702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032831 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 1, 7]
def baseStart_4032831 : Nat := 118140960795 + 4032831 * 2 ^ 59
def prefixEnd_4032831 : Nat := 4983230072969 + 3 ^ 40 * 4032831 * 2
def baseEnd_4032831 : Nat := 1380520467568144175910569

theorem tailTrace_4032831 : CollatzResearch.WordTrace tailWord_4032831 prefixEnd_4032831 1380520467568144175910569 := by
  unfold tailWord_4032831
  simp only [CollatzResearch.WordTrace]
  refine ⟨147089430452749514545506347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98059620301833009697004231 147089430452749514545506347)
  ·
    refine ⟨220634145679124271818259521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147089430452749514545506347 220634145679124271818259521)
    ·
      refine ⟨165475609259343203863694641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220634145679124271818259521 165475609259343203863694641)
      ·
        refine ⟨124106706944507402897770981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165475609259343203863694641 124106706944507402897770981)
        ·
          refine ⟨23270007552095138043332059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124106706944507402897770981 23270007552095138043332059)
          ·
            refine ⟨34905011328142707064998089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23270007552095138043332059 34905011328142707064998089)
            ·
              refine ⟨26178758496107030298748567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34905011328142707064998089 26178758496107030298748567)
              ·
                refine ⟨39268137744160545448122851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26178758496107030298748567 39268137744160545448122851)
                ·
                  refine ⟨58902206616240818172184277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39268137744160545448122851 58902206616240818172184277)
                  ·
                    refine ⟨1380520467568144175910569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58902206616240818172184277 1380520467568144175910569)
                    ·
                      rfl

theorem cell22_4032831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_4032831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032831 prefixEnd_4032831 := by exact prefixLift 4032831
  have htrace : WordTrace (prefixWord ++ tailWord_4032831) baseStart_4032831 baseEnd_4032831 := by
    simpa [prefixWord, tailWord_4032831, baseEnd_4032831] using wordTrace_append hprefix tailTrace_4032831
  have hstable : (prefixWord ++ tailWord_4032831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032831).length < 2 ^ (prefixWord ++ tailWord_4032831).sum := by decide
  have hdescent : baseEnd_4032831 < baseStart_4032831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032863 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 1, 4]
def baseStart_4032863 : Nat := 118140960795 + 4032863 * 2 ^ 59
def prefixEnd_4032863 : Nat := 4983230072969 + 3 ^ 40 * 4032863 * 2
def baseEnd_4032863 : Nat := 1380531421822106759110471

theorem tailTrace_4032863 : CollatzResearch.WordTrace tailWord_4032863 prefixEnd_4032863 1380531421822106759110471 := by
  unfold tailWord_4032863
  simp only [CollatzResearch.WordTrace]
  refine ⟨147090597588633584010671243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98060398392422389340447495 147090597588633584010671243)
  ·
    refine ⟨220635896382950376016006865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147090597588633584010671243 220635896382950376016006865)
    ·
      refine ⟨165476922287212782012005149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220635896382950376016006865 165476922287212782012005149)
      ·
        refine ⟨62053845857704793254501931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165476922287212782012005149 62053845857704793254501931)
        ·
          refine ⟨93080768786557189881752897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62053845857704793254501931 93080768786557189881752897)
          ·
            refine ⟨69810576589917892411314673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93080768786557189881752897 69810576589917892411314673)
            ·
              refine ⟨52357932442438419308486005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69810576589917892411314673 52357932442438419308486005)
              ·
                refine ⟨4908556166478601810170563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52357932442438419308486005 4908556166478601810170563)
                ·
                  refine ⟨7362834249717902715255845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908556166478601810170563 7362834249717902715255845)
                  ·
                    refine ⟨1380531421822106759110471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7362834249717902715255845 1380531421822106759110471)
                    ·
                      rfl

theorem cell22_4032863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_4032863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032863 prefixEnd_4032863 := by exact prefixLift 4032863
  have htrace : WordTrace (prefixWord ++ tailWord_4032863) baseStart_4032863 baseEnd_4032863 := by
    simpa [prefixWord, tailWord_4032863, baseEnd_4032863] using wordTrace_append hprefix tailTrace_4032863
  have hstable : (prefixWord ++ tailWord_4032863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032863).length < 2 ^ (prefixWord ++ tailWord_4032863).sum := by decide
  have hdescent : baseEnd_4032863 < baseStart_4032863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032893 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_4032893 : Nat := 118140960795 + 4032893 * 2 ^ 59
def prefixEnd_4032893 : Nat := 4983230072969 + 3 ^ 40 * 4032893 * 2
def baseEnd_4032893 : Nat := 1380541691435196680860379

theorem tailTrace_4032893 : CollatzResearch.WordTrace tailWord_4032893 prefixEnd_4032893 1380541691435196680860379 := by
  unfold tailWord_4032893
  simp only [CollatzResearch.WordTrace]
  refine ⟨147091691778524899134263333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98061127852349932756175555 147091691778524899134263333)
  ·
    refine ⟨27579692208473418587674375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147091691778524899134263333 27579692208473418587674375)
    ·
      refine ⟨41369538312710127881511563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27579692208473418587674375 41369538312710127881511563)
      ·
        refine ⟨62054307469065191822267345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41369538312710127881511563 62054307469065191822267345)
        ·
          refine ⟨46540730601798893866700509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62054307469065191822267345 46540730601798893866700509)
          ·
            refine ⟨17452773975674585200012691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46540730601798893866700509 17452773975674585200012691)
            ·
              refine ⟨26179160963511877800019037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17452773975674585200012691 26179160963511877800019037)
              ·
                refine ⟨9817185361316954175007139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26179160963511877800019037 9817185361316954175007139)
                ·
                  refine ⟨14725778041975431262510709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817185361316954175007139 14725778041975431262510709)
                  ·
                    refine ⟨1380541691435196680860379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14725778041975431262510709 1380541691435196680860379)
                    ·
                      rfl

theorem cell22_4032893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_4032893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032893 prefixEnd_4032893 := by exact prefixLift 4032893
  have htrace : WordTrace (prefixWord ++ tailWord_4032893) baseStart_4032893 baseEnd_4032893 := by
    simpa [prefixWord, tailWord_4032893, baseEnd_4032893] using wordTrace_append hprefix tailTrace_4032893
  have hstable : (prefixWord ++ tailWord_4032893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032893).length < 2 ^ (prefixWord ++ tailWord_4032893).sum := by decide
  have hdescent : baseEnd_4032893 < baseStart_4032893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032908 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_4032908 : Nat := 118140960795 + 4032908 * 2 ^ 59
def prefixEnd_4032908 : Nat := 4983230072969 + 3 ^ 40 * 4032908 * 2
def baseEnd_4032908 : Nat := 1380546826241741641735333

theorem tailTrace_4032908 : CollatzResearch.WordTrace tailWord_4032908 prefixEnd_4032908 1380546826241741641735333 := by
  unfold tailWord_4032908
  simp only [CollatzResearch.WordTrace]
  refine ⟨73546119436735278348029689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98061492582313704464039585 73546119436735278348029689)
  ·
    refine ⟨55159589577551458761022267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73546119436735278348029689 55159589577551458761022267)
    ·
      refine ⟨82739384366327188141533401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55159589577551458761022267 82739384366327188141533401)
      ·
        refine ⟨62054538274745391106150051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82739384366327188141533401 62054538274745391106150051)
        ·
          refine ⟨93081807412118086659225077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62054538274745391106150051 93081807412118086659225077)
          ·
            refine ⟨8726419444886070624302351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93081807412118086659225077 8726419444886070624302351)
            ·
              refine ⟨13089629167329105936453527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726419444886070624302351 13089629167329105936453527)
              ·
                refine ⟨19634443750993658904680291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13089629167329105936453527 19634443750993658904680291)
                ·
                  refine ⟨29451665626490488357020437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19634443750993658904680291 29451665626490488357020437)
                  ·
                    refine ⟨1380546826241741641735333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29451665626490488357020437 1380546826241741641735333)
                    ·
                      rfl

theorem cell22_4032908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_4032908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032908 prefixEnd_4032908 := by exact prefixLift 4032908
  have htrace : WordTrace (prefixWord ++ tailWord_4032908) baseStart_4032908 baseEnd_4032908 := by
    simpa [prefixWord, tailWord_4032908, baseEnd_4032908] using wordTrace_append hprefix tailTrace_4032908
  have hstable : (prefixWord ++ tailWord_4032908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032908).length < 2 ^ (prefixWord ++ tailWord_4032908).sum := by decide
  have hdescent : baseEnd_4032908 < baseStart_4032908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032910 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_4032910 : Nat := 118140960795 + 4032910 * 2 ^ 59
def prefixEnd_4032910 : Nat := 4983230072969 + 3 ^ 40 * 4032910 * 2
def baseEnd_4032910 : Nat := 1380547510882614303185327

theorem tailTrace_4032910 : CollatzResearch.WordTrace tailWord_4032910 prefixEnd_4032910 1380547510882614303185327 := by
  unfold tailWord_4032910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18386538977432913879704023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98061541212975540691754789 18386538977432913879704023)
  ·
    refine ⟨27579808466149370819556035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18386538977432913879704023 27579808466149370819556035)
    ·
      refine ⟨41369712699224056229334053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27579808466149370819556035 41369712699224056229334053)
      ·
        refine ⟨7756821131104510543000135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41369712699224056229334053 7756821131104510543000135)
        ·
          refine ⟨11635231696656765814500203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7756821131104510543000135 11635231696656765814500203)
          ·
            refine ⟨17452847544985148721750305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11635231696656765814500203 17452847544985148721750305)
            ·
              refine ⟨13089635658738861541312729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17452847544985148721750305 13089635658738861541312729)
              ·
                refine ⟨9817226744054146155984547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13089635658738861541312729 9817226744054146155984547)
                ·
                  refine ⟨14725840116081219233976821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817226744054146155984547 14725840116081219233976821)
                  ·
                    refine ⟨1380547510882614303185327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14725840116081219233976821 1380547510882614303185327)
                    ·
                      rfl

theorem cell22_4032910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_4032910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032910 prefixEnd_4032910 := by exact prefixLift 4032910
  have htrace : WordTrace (prefixWord ++ tailWord_4032910) baseStart_4032910 baseEnd_4032910 := by
    simpa [prefixWord, tailWord_4032910, baseEnd_4032910] using wordTrace_append hprefix tailTrace_4032910
  have hstable : (prefixWord ++ tailWord_4032910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032910).length < 2 ^ (prefixWord ++ tailWord_4032910).sum := by decide
  have hdescent : baseEnd_4032910 < baseStart_4032910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032918 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4032918 : Nat := 118140960795 + 4032918 * 2 ^ 59
def prefixEnd_4032918 : Nat := 4983230072969 + 3 ^ 40 * 4032918 * 2
def baseEnd_4032918 : Nat := 460183416482034982995101

theorem tailTrace_4032918 : CollatzResearch.WordTrace tailWord_4032918 prefixEnd_4032918 460183416482034982995101 := by
  unfold tailWord_4032918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9193287725214645525245213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98061735735622885602615605 9193287725214645525245213)
  ·
    refine ⟨3447482896955492071966955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9193287725214645525245213 3447482896955492071966955)
    ·
      refine ⟨5171224345433238107950433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447482896955492071966955 5171224345433238107950433)
      ·
        refine ⟨3878418259074928580962825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5171224345433238107950433 3878418259074928580962825)
        ·
          refine ⟨2908813694306196435722119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3878418259074928580962825 2908813694306196435722119)
          ·
            refine ⟨4363220541459294653583179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908813694306196435722119 4363220541459294653583179)
            ·
              refine ⟨6544830812188941980374769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363220541459294653583179 6544830812188941980374769)
              ·
                refine ⟨4908623109141706485281077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544830812188941980374769 4908623109141706485281077)
                ·
                  refine ⟨460183416482034982995101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4908623109141706485281077 460183416482034982995101)
                  ·
                    rfl

theorem cell22_4032918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4032918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032918 prefixEnd_4032918 := by exact prefixLift 4032918
  have htrace : WordTrace (prefixWord ++ tailWord_4032918) baseStart_4032918 baseEnd_4032918 := by
    simpa [prefixWord, tailWord_4032918, baseEnd_4032918] using wordTrace_append hprefix tailTrace_4032918
  have hstable : (prefixWord ++ tailWord_4032918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032918).length < 2 ^ (prefixWord ++ tailWord_4032918).sum := by decide
  have hdescent : baseEnd_4032918 < baseStart_4032918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032968 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 7]
def baseStart_4032968 : Nat := 118140960795 + 4032968 * 2 ^ 59
def prefixEnd_4032968 : Nat := 4983230072969 + 3 ^ 40 * 4032968 * 2
def baseEnd_4032968 : Nat := 460189121822640495078383

theorem tailTrace_4032968 : CollatzResearch.WordTrace tailWord_4032968 prefixEnd_4032968 460189121822640495078383 := by
  unfold tailWord_4032968
  simp only [CollatzResearch.WordTrace]
  refine ⟨73547213626626593471621779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98062951502168791295495705 73547213626626593471621779)
  ·
    refine ⟨110320820439939890207432669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73547213626626593471621779 110320820439939890207432669)
    ·
      refine ⟨41370307664977458827787251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110320820439939890207432669 41370307664977458827787251)
      ·
        refine ⟨62055461497466188241680877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41370307664977458827787251 62055461497466188241680877)
        ·
          refine ⟨23270798061549820590630329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62055461497466188241680877 23270798061549820590630329)
          ·
            refine ⟨17453098546162365442972747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23270798061549820590630329 17453098546162365442972747)
            ·
              refine ⟨26179647819243548164459121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17453098546162365442972747 26179647819243548164459121)
              ·
                refine ⟨19634735864432661123344341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26179647819243548164459121 19634735864432661123344341)
                ·
                  refine ⟨460189121822640495078383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19634735864432661123344341 460189121822640495078383)
                  ·
                    rfl

theorem cell22_4032968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_4032968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4032968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4032968 prefixEnd_4032968 := by exact prefixLift 4032968
  have htrace : WordTrace (prefixWord ++ tailWord_4032968) baseStart_4032968 baseEnd_4032968 := by
    simpa [prefixWord, tailWord_4032968, baseEnd_4032968] using wordTrace_append hprefix tailTrace_4032968
  have hstable : (prefixWord ++ tailWord_4032968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032968).length < 2 ^ (prefixWord ++ tailWord_4032968).sum := by decide
  have hdescent : baseEnd_4032968 < baseStart_4032968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033002 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_4033002 : Nat := 118140960795 + 4033002 * 2 ^ 59
def prefixEnd_4033002 : Nat := 4983230072969 + 3 ^ 40 * 4033002 * 2
def baseEnd_4033002 : Nat := 460193001454252243295015

theorem tailTrace_4033002 : CollatzResearch.WordTrace tailWord_4033002 prefixEnd_4033002 460193001454252243295015 := by
  unfold tailWord_4033002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36773916833782502687495315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98063778223420007166654173 36773916833782502687495315)
  ·
    refine ⟨55160875250673754031242973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36773916833782502687495315 55160875250673754031242973)
    ·
      refine ⟨20685328219002657761716115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55160875250673754031242973 20685328219002657761716115)
      ·
        refine ⟨31027992328503986642574173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20685328219002657761716115 31027992328503986642574173)
        ·
          refine ⟨11635497123188994990965315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31027992328503986642574173 11635497123188994990965315)
          ·
            refine ⟨17453245684783492486447973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11635497123188994990965315 17453245684783492486447973)
            ·
              refine ⟨3272483565896904841208995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17453245684783492486447973 3272483565896904841208995)
              ·
                refine ⟨4908725348845357261813493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272483565896904841208995 4908725348845357261813493)
                ·
                  refine ⟨460193001454252243295015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4908725348845357261813493 460193001454252243295015)
                  ·
                    rfl

theorem cell22_4033002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_4033002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033002 prefixEnd_4033002 := by exact prefixLift 4033002
  have htrace : WordTrace (prefixWord ++ tailWord_4033002) baseStart_4033002 baseEnd_4033002 := by
    simpa [prefixWord, tailWord_4033002, baseEnd_4033002] using wordTrace_append hprefix tailTrace_4033002
  have hstable : (prefixWord ++ tailWord_4033002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033002).length < 2 ^ (prefixWord ++ tailWord_4033002).sum := by decide
  have hdescent : baseEnd_4033002 < baseStart_4033002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033075 : List Nat := [1, 1, 1, 2, 4, 2, 5, 6]
def baseStart_4033075 : Nat := 118140960795 + 4033075 * 2 ^ 59
def prefixEnd_4033075 : Nat := 4983230072969 + 3 ^ 40 * 4033075 * 2
def baseEnd_4033075 : Nat := 153400443750512096978869

theorem tailTrace_4033075 : CollatzResearch.WordTrace tailWord_4033075 prefixEnd_4033075 153400443750512096978869 := by
  unfold tailWord_4033075
  simp only [CollatzResearch.WordTrace]
  refine ⟨147098329863865544217388679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98065553242577029478259119 147098329863865544217388679)
  ·
    refine ⟨220647494795798316326083019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147098329863865544217388679 220647494795798316326083019)
    ·
      refine ⟨330971242193697474489124529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220647494795798316326083019 330971242193697474489124529)
      ·
        refine ⟨248228431645273105866843397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330971242193697474489124529 248228431645273105866843397)
        ·
          refine ⟨46542830933488707350033137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248228431645273105866843397 46542830933488707350033137)
          ·
            refine ⟨34907123200116530512524853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46542830933488707350033137 34907123200116530512524853)
            ·
              refine ⟨3272542800010924735549205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34907123200116530512524853 3272542800010924735549205)
              ·
                refine ⟨153400443750512096978869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3272542800010924735549205 153400443750512096978869)
                ·
                  rfl

theorem cell22_4033075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 6].length) (baseStart_4033075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033075 prefixEnd_4033075 := by exact prefixLift 4033075
  have htrace : WordTrace (prefixWord ++ tailWord_4033075) baseStart_4033075 baseEnd_4033075 := by
    simpa [prefixWord, tailWord_4033075, baseEnd_4033075] using wordTrace_append hprefix tailTrace_4033075
  have hstable : (prefixWord ++ tailWord_4033075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033075).length < 2 ^ (prefixWord ++ tailWord_4033075).sum := by decide
  have hdescent : baseEnd_4033075 < baseStart_4033075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033120 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 5]
def baseStart_4033120 : Nat := 118140960795 + 4033120 * 2 ^ 59
def prefixEnd_4033120 : Nat := 4983230072969 + 3 ^ 40 * 4033120 * 2
def baseEnd_4033120 : Nat := 460206466058081251811561

theorem tailTrace_4033120 : CollatzResearch.WordTrace tailWord_4033120 prefixEnd_4033120 460206466058081251811561 := by
  unfold tailWord_4033120
  simp only [CollatzResearch.WordTrace]
  refine ⟨73549985574351258451388407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98066647432468344601851209 73549985574351258451388407)
  ·
    refine ⟨110324978361526887677082611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73549985574351258451388407 110324978361526887677082611)
    ·
      refine ⟨165487467542290331515623917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110324978361526887677082611 165487467542290331515623917)
      ·
        refine ⟨62057800328358874318358969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165487467542290331515623917 62057800328358874318358969)
        ·
          refine ⟨46543350246269155738769227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62057800328358874318358969 46543350246269155738769227)
          ·
            refine ⟨69815025369403733608153841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46543350246269155738769227 69815025369403733608153841)
            ·
              refine ⟨52361269027052800206115381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69815025369403733608153841 52361269027052800206115381)
              ·
                refine ⟨4908868971286200019323317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52361269027052800206115381 4908868971286200019323317)
                ·
                  refine ⟨460206466058081251811561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4908868971286200019323317 460206466058081251811561)
                  ·
                    rfl

theorem cell22_4033120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_4033120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033120 prefixEnd_4033120 := by exact prefixLift 4033120
  have htrace : WordTrace (prefixWord ++ tailWord_4033120) baseStart_4033120 baseEnd_4033120 := by
    simpa [prefixWord, tailWord_4033120, baseEnd_4033120] using wordTrace_append hprefix tailTrace_4033120
  have hstable : (prefixWord ++ tailWord_4033120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033120).length < 2 ^ (prefixWord ++ tailWord_4033120).sum := by decide
  have hdescent : baseEnd_4033120 < baseStart_4033120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033182 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_4033182 : Nat := 118140960795 + 4033182 * 2 ^ 59
def prefixEnd_4033182 : Nat := 4983230072969 + 3 ^ 40 * 4033182 * 2
def baseEnd_4033182 : Nat := 460213540680432086794831

theorem tailTrace_4033182 : CollatzResearch.WordTrace tailWord_4033182 prefixEnd_4033182 460213540680432086794831 := by
  unfold tailWord_4033182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18387779059309737686441725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98068154982985267661022533 18387779059309737686441725)
  ·
    refine ⟨6895417147241151632415647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18387779059309737686441725 6895417147241151632415647)
    ·
      refine ⟨10343125720861727448623471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6895417147241151632415647 10343125720861727448623471)
      ·
        refine ⟨15514688581292591172935207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10343125720861727448623471 15514688581292591172935207)
        ·
          refine ⟨23272032871938886759402811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15514688581292591172935207 23272032871938886759402811)
          ·
            refine ⟨34908049307908330139104217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23272032871938886759402811 34908049307908330139104217)
            ·
              refine ⟨26181036980931247604328163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34908049307908330139104217 26181036980931247604328163)
              ·
                refine ⟨39271555471396871406492245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26181036980931247604328163 39271555471396871406492245)
                ·
                  refine ⟨460213540680432086794831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39271555471396871406492245 460213540680432086794831)
                  ·
                    rfl

theorem cell22_4033182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_4033182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033182 prefixEnd_4033182 := by exact prefixLift 4033182
  have htrace : WordTrace (prefixWord ++ tailWord_4033182) baseStart_4033182 baseEnd_4033182 := by
    simpa [prefixWord, tailWord_4033182, baseEnd_4033182] using wordTrace_append hprefix tailTrace_4033182
  have hstable : (prefixWord ++ tailWord_4033182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033182).length < 2 ^ (prefixWord ++ tailWord_4033182).sum := by decide
  have hdescent : baseEnd_4033182 < baseStart_4033182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033197 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4033197 : Nat := 118140960795 + 4033197 * 2 ^ 59
def prefixEnd_4033197 : Nat := 4983230072969 + 3 ^ 40 * 4033197 * 2
def baseEnd_4033197 : Nat := 1380645756847841221259447

theorem tailTrace_4033197 : CollatzResearch.WordTrace tailWord_4033197 prefixEnd_4033197 1380645756847841221259447 := by
  unfold tailWord_4033197
  simp only [CollatzResearch.WordTrace]
  refine ⟨147102779569423559053329845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98068519712949039368886563 147102779569423559053329845)
  ·
    refine ⟨13790885584633458661249673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147102779569423559053329845 13790885584633458661249673)
    ·
      refine ⟨10343164188475093995937255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13790885584633458661249673 10343164188475093995937255)
      ·
        refine ⟨15514746282712640993905883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10343164188475093995937255 15514746282712640993905883)
        ·
          refine ⟨23272119424068961490858825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15514746282712640993905883 23272119424068961490858825)
          ·
            refine ⟨17454089568051721118144119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23272119424068961490858825 17454089568051721118144119)
            ·
              refine ⟨26181134352077581677216179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17454089568051721118144119 26181134352077581677216179)
              ·
                refine ⟨39271701528116372515824269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26181134352077581677216179 39271701528116372515824269)
                ·
                  refine ⟨14726888073043639693434101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39271701528116372515824269 14726888073043639693434101)
                  ·
                    refine ⟨1380645756847841221259447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14726888073043639693434101 1380645756847841221259447)
                    ·
                      rfl

theorem cell22_4033197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4033197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033197 prefixEnd_4033197 := by exact prefixLift 4033197
  have htrace : WordTrace (prefixWord ++ tailWord_4033197) baseStart_4033197 baseEnd_4033197 := by
    simpa [prefixWord, tailWord_4033197, baseEnd_4033197] using wordTrace_append hprefix tailTrace_4033197
  have hstable : (prefixWord ++ tailWord_4033197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033197).length < 2 ^ (prefixWord ++ tailWord_4033197).sum := by decide
  have hdescent : baseEnd_4033197 < baseStart_4033197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033212 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_4033212 : Nat := 118140960795 + 4033212 * 2 ^ 59
def prefixEnd_4033212 : Nat := 4983230072969 + 3 ^ 40 * 4033212 * 2
def baseEnd_4033212 : Nat := 1380650891654386182134401

theorem tailTrace_4033212 : CollatzResearch.WordTrace tailWord_4033212 prefixEnd_4033212 1380650891654386182134401 := by
  unfold tailWord_4033212
  simp only [CollatzResearch.WordTrace]
  refine ⟨73551663332184608307562945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98068884442912811076750593 73551663332184608307562945)
  ·
    refine ⟨55163747499138456230672209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73551663332184608307562945 55163747499138456230672209)
    ·
      refine ⟨41372810624353842173004157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55163747499138456230672209 41372810624353842173004157)
      ·
        refine ⟨15514803984132690814876559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41372810624353842173004157 15514803984132690814876559)
        ·
          refine ⟨23272205976199036222314839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15514803984132690814876559 23272205976199036222314839)
          ·
            refine ⟨34908308964298554333472259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23272205976199036222314839 34908308964298554333472259)
            ·
              refine ⟨52362463446447831500208389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34908308964298554333472259 52362463446447831500208389)
              ·
                refine ⟨9817961896208968406289073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52362463446447831500208389 9817961896208968406289073)
                ·
                  refine ⟨7363471422156726304716805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9817961896208968406289073 7363471422156726304716805)
                  ·
                    refine ⟨1380650891654386182134401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7363471422156726304716805 1380650891654386182134401)
                    ·
                      rfl

theorem cell22_4033212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_4033212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033212 prefixEnd_4033212 := by exact prefixLift 4033212
  have htrace : WordTrace (prefixWord ++ tailWord_4033212) baseStart_4033212 baseEnd_4033212 := by
    simpa [prefixWord, tailWord_4033212, baseEnd_4033212] using wordTrace_append hprefix tailTrace_4033212
  have hstable : (prefixWord ++ tailWord_4033212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033212).length < 2 ^ (prefixWord ++ tailWord_4033212).sum := by decide
  have hdescent : baseEnd_4033212 < baseStart_4033212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033216 : List Nat := [2, 1, 1, 2, 4, 4, 2, 2, 4]
def baseStart_4033216 : Nat := 118140960795 + 4033216 * 2 ^ 59
def prefixEnd_4033216 : Nat := 4983230072969 + 3 ^ 40 * 4033216 * 2
def baseEnd_4033216 : Nat := 460217420312043835011463

theorem tailTrace_4033216 : CollatzResearch.WordTrace tailWord_4033216 prefixEnd_4033216 460217420312043835011463 := by
  unfold tailWord_4033216
  simp only [CollatzResearch.WordTrace]
  refine ⟨73551736278177362649135751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98068981704236483532181001 73551736278177362649135751)
  ·
    refine ⟨110327604417266043973703627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73551736278177362649135751 110327604417266043973703627)
    ·
      refine ⟨165491406625899065960555441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110327604417266043973703627 165491406625899065960555441)
      ·
        refine ⟨124118554969424299470416581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165491406625899065960555441 124118554969424299470416581)
        ·
          refine ⟨23272229056767056150703109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124118554969424299470416581 23272229056767056150703109)
          ·
            refine ⟨4363542948143823028256833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23272229056767056150703109 4363542948143823028256833)
            ·
              refine ⟨3272657211107867271192625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4363542948143823028256833 3272657211107867271192625)
              ·
                refine ⟨2454492908330900453394469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3272657211107867271192625 2454492908330900453394469)
                ·
                  refine ⟨460217420312043835011463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2454492908330900453394469 460217420312043835011463)
                  ·
                    rfl

theorem cell22_4033216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 4].length) (baseStart_4033216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033216 prefixEnd_4033216 := by exact prefixLift 4033216
  have htrace : WordTrace (prefixWord ++ tailWord_4033216) baseStart_4033216 baseEnd_4033216 := by
    simpa [prefixWord, tailWord_4033216, baseEnd_4033216] using wordTrace_append hprefix tailTrace_4033216
  have hstable : (prefixWord ++ tailWord_4033216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033216).length < 2 ^ (prefixWord ++ tailWord_4033216).sum := by decide
  have hdescent : baseEnd_4033216 < baseStart_4033216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033276 : List Nat := [2, 2, 2, 1, 3, 2, 2, 4, 1, 3]
def baseStart_4033276 : Nat := 118140960795 + 4033276 * 2 ^ 59
def prefixEnd_4033276 : Nat := 4983230072969 + 3 ^ 40 * 4033276 * 2
def baseEnd_4033276 : Nat := 1380672800162311348534205

theorem tailTrace_4033276 : CollatzResearch.WordTrace tailWord_4033276 prefixEnd_4033276 1380672800162311348534205 := by
  unfold tailWord_4033276
  simp only [CollatzResearch.WordTrace]
  refine ⟨73552830468068677772727841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98070440624091570363637121 73552830468068677772727841)
  ·
    refine ⟨55164622851051508329545881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73552830468068677772727841 55164622851051508329545881)
    ·
      refine ⟨41373467138288631247159411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55164622851051508329545881 41373467138288631247159411)
      ·
        refine ⟨62060200707432946870739117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41373467138288631247159411 62060200707432946870739117)
        ·
          refine ⟨23272575265287355076527169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62060200707432946870739117 23272575265287355076527169)
          ·
            refine ⟨17454431448965516307395377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23272575265287355076527169 17454431448965516307395377)
            ·
              refine ⟨13090823586724137230546533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17454431448965516307395377 13090823586724137230546533)
              ·
                refine ⟨2454529422510775730727475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13090823586724137230546533 2454529422510775730727475)
                ·
                  refine ⟨3681794133766163596091213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454529422510775730727475 3681794133766163596091213)
                  ·
                    refine ⟨1380672800162311348534205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3681794133766163596091213 1380672800162311348534205)
                    ·
                      rfl

theorem cell22_4033276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_4033276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033276 prefixEnd_4033276 := by exact prefixLift 4033276
  have htrace : WordTrace (prefixWord ++ tailWord_4033276) baseStart_4033276 baseEnd_4033276 := by
    simpa [prefixWord, tailWord_4033276, baseEnd_4033276] using wordTrace_append hprefix tailTrace_4033276
  have hstable : (prefixWord ++ tailWord_4033276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033276).length < 2 ^ (prefixWord ++ tailWord_4033276).sum := by decide
  have hdescent : baseEnd_4033276 < baseStart_4033276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033347 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 4, 4]
def baseStart_4033347 : Nat := 118140960795 + 4033347 * 2 ^ 59
def prefixEnd_4033347 : Nat := 4983230072969 + 3 ^ 40 * 4033347 * 2
def baseEnd_4033347 : Nat := 1380697104913290830008987

theorem tailTrace_4033347 : CollatzResearch.WordTrace tailWord_4033347 prefixEnd_4033347 1380697104913290830008987 := by
  unfold tailWord_4033347
  simp only [CollatzResearch.WordTrace]
  refine ⟨147108250518880134671290295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98072167012586756447526863 147108250518880134671290295)
  ·
    refine ⟨220662375778320202006935443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147108250518880134671290295 220662375778320202006935443)
    ·
      refine ⟨330993563667480303010403165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220662375778320202006935443 330993563667480303010403165)
      ·
        refine ⟨124122586375305113628901187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330993563667480303010403165 124122586375305113628901187)
        ·
          refine ⟨186183879562957670443351781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124122586375305113628901187 186183879562957670443351781)
          ·
            refine ⟨34909477418054563208128459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186183879562957670443351781 34909477418054563208128459)
            ·
              refine ⟨52364216127081844812192689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34909477418054563208128459 52364216127081844812192689)
              ·
                refine ⟨39273162095311383609144517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52364216127081844812192689 39273162095311383609144517)
                ·
                  refine ⟨7363717892870884426714597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39273162095311383609144517 7363717892870884426714597)
                  ·
                    refine ⟨1380697104913290830008987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7363717892870884426714597 1380697104913290830008987)
                    ·
                      rfl

theorem cell22_4033347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 4].length) (baseStart_4033347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033347 prefixEnd_4033347 := by exact prefixLift 4033347
  have htrace : WordTrace (prefixWord ++ tailWord_4033347) baseStart_4033347 baseEnd_4033347 := by
    simpa [prefixWord, tailWord_4033347, baseEnd_4033347] using wordTrace_append hprefix tailTrace_4033347
  have hstable : (prefixWord ++ tailWord_4033347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033347).length < 2 ^ (prefixWord ++ tailWord_4033347).sum := by decide
  have hdescent : baseEnd_4033347 < baseStart_4033347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033362 : List Nat := [3, 2, 2, 1, 1, 2, 1, 10]
def baseStart_4033362 : Nat := 118140960795 + 4033362 * 2 ^ 59
def prefixEnd_4033362 : Nat := 4983230072969 + 3 ^ 40 * 4033362 * 2
def baseEnd_4033362 : Nat := 153411359968870643431549

theorem tailTrace_4033362 : CollatzResearch.WordTrace tailWord_4033362 prefixEnd_4033362 153411359968870643431549 := by
  unfold tailWord_4033362
  simp only [CollatzResearch.WordTrace]
  refine ⟨36777199403456448058271585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98072531742550528155390893 36777199403456448058271585)
  ·
    refine ⟨27582899552592336043703689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36777199403456448058271585 27582899552592336043703689)
    ·
      refine ⟨20687174664444252032777767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27582899552592336043703689 20687174664444252032777767)
      ·
        refine ⟨31030761996666378049166651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20687174664444252032777767 31030761996666378049166651)
        ·
          refine ⟨46546142994999567073749977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31030761996666378049166651 46546142994999567073749977)
          ·
            refine ⟨34909607246249675305312483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46546142994999567073749977 34909607246249675305312483)
            ·
              refine ⟨52364410869374512957968725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34909607246249675305312483 52364410869374512957968725)
              ·
                refine ⟨153411359968870643431549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52364410869374512957968725 153411359968870643431549)
                ·
                  rfl

theorem cell22_4033362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_4033362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033362 prefixEnd_4033362 := by exact prefixLift 4033362
  have htrace : WordTrace (prefixWord ++ tailWord_4033362) baseStart_4033362 baseEnd_4033362 := by
    simpa [prefixWord, tailWord_4033362, baseEnd_4033362] using wordTrace_append hprefix tailTrace_4033362
  have hstable : (prefixWord ++ tailWord_4033362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033362).length < 2 ^ (prefixWord ++ tailWord_4033362).sum := by decide
  have hdescent : baseEnd_4033362 < baseStart_4033362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033392 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_4033392 : Nat := 118140960795 + 4033392 * 2 ^ 59
def prefixEnd_4033392 : Nat := 4983230072969 + 3 ^ 40 * 4033392 * 2
def baseEnd_4033392 : Nat := 1380712509332925712633849

theorem tailTrace_4033392 : CollatzResearch.WordTrace tailWord_4033392 prefixEnd_4033392 1380712509332925712633849 := by
  unfold tailWord_4033392
  simp only [CollatzResearch.WordTrace]
  refine ⟨73554945901858553678339215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98073261202478071571118953 73554945901858553678339215)
  ·
    refine ⟨110332418852787830517508823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73554945901858553678339215 110332418852787830517508823)
    ·
      refine ⟨165498628279181745776263235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110332418852787830517508823 165498628279181745776263235)
      ·
        refine ⟨248247942418772618664394853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165498628279181745776263235 248247942418772618664394853)
        ·
          refine ⟨46546489203519865999574035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248247942418772618664394853 46546489203519865999574035)
          ·
            refine ⟨69819733805279798999361053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46546489203519865999574035 69819733805279798999361053)
            ·
              refine ⟨26182400176979924624760395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69819733805279798999361053 26182400176979924624760395)
              ·
                refine ⟨39273600265469886937140593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26182400176979924624760395 39273600265469886937140593)
                ·
                  refine ⟨29455200199102415202855445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39273600265469886937140593 29455200199102415202855445)
                  ·
                    refine ⟨1380712509332925712633849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29455200199102415202855445 1380712509332925712633849)
                    ·
                      rfl

theorem cell22_4033392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_4033392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033392 prefixEnd_4033392 := by exact prefixLift 4033392
  have htrace : WordTrace (prefixWord ++ tailWord_4033392) baseStart_4033392 baseEnd_4033392 := by
    simpa [prefixWord, tailWord_4033392, baseEnd_4033392] using wordTrace_append hprefix tailTrace_4033392
  have hstable : (prefixWord ++ tailWord_4033392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033392).length < 2 ^ (prefixWord ++ tailWord_4033392).sum := by decide
  have hdescent : baseEnd_4033392 < baseStart_4033392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033439 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 2, 5]
def baseStart_4033439 : Nat := 118140960795 + 4033439 * 2 ^ 59
def prefixEnd_4033439 : Nat := 4983230072969 + 3 ^ 40 * 4033439 * 2
def baseEnd_4033439 : Nat := 1380728598393433256708705

theorem tailTrace_4033439 : CollatzResearch.WordTrace tailWord_4033439 prefixEnd_4033439 1380728598393433256708705 := by
  unfold tailWord_4033439
  simp only [CollatzResearch.WordTrace]
  refine ⟨147111606034546834383639371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98074404023031222922426247 147111606034546834383639371)
  ·
    refine ⟨220667409051820251575459057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147111606034546834383639371 220667409051820251575459057)
    ·
      refine ⟨165500556788865188681594293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220667409051820251575459057 165500556788865188681594293)
      ·
        refine ⟨15515677198956111438899465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165500556788865188681594293 15515677198956111438899465)
        ·
          refine ⟨11636757899217083579174599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15515677198956111438899465 11636757899217083579174599)
          ·
            refine ⟨17455136848825625368761899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11636757899217083579174599 17455136848825625368761899)
            ·
              refine ⟨26182705273238438053142849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17455136848825625368761899 26182705273238438053142849)
              ·
                refine ⟨19637028954928828539857137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26182705273238438053142849 19637028954928828539857137)
                ·
                  refine ⟨14727771716196621404892853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19637028954928828539857137 14727771716196621404892853)
                  ·
                    refine ⟨1380728598393433256708705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14727771716196621404892853 1380728598393433256708705)
                    ·
                      rfl

theorem cell22_4033439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_4033439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033439 prefixEnd_4033439 := by exact prefixLift 4033439
  have htrace : WordTrace (prefixWord ++ tailWord_4033439) baseStart_4033439 baseEnd_4033439 := by
    simpa [prefixWord, tailWord_4033439, baseEnd_4033439] using wordTrace_append hprefix tailTrace_4033439
  have hstable : (prefixWord ++ tailWord_4033439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033439).length < 2 ^ (prefixWord ++ tailWord_4033439).sum := by decide
  have hdescent : baseEnd_4033439 < baseStart_4033439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033441 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 5]
def baseStart_4033441 : Nat := 118140960795 + 4033441 * 2 ^ 59
def prefixEnd_4033441 : Nat := 4983230072969 + 3 ^ 40 * 4033441 * 2
def baseEnd_4033441 : Nat := 460243094344768639386233

theorem tailTrace_4033441 : CollatzResearch.WordTrace tailWord_4033441 prefixEnd_4033441 460243094344768639386233 := by
  unfold tailWord_4033441
  simp only [CollatzResearch.WordTrace]
  refine ⟨147111678980539588725212177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98074452653693059150141451 147111678980539588725212177)
  ·
    refine ⟨110333759235404691543909133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147111678980539588725212177 110333759235404691543909133)
    ·
      refine ⟨41375159713276759328965925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110333759235404691543909133 41375159713276759328965925)
      ·
        refine ⟨7757842446239392374181111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41375159713276759328965925 7757842446239392374181111)
        ·
          refine ⟨11636763669359088561271667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7757842446239392374181111 11636763669359088561271667)
          ·
            refine ⟨17455145504038632841907501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11636763669359088561271667 17455145504038632841907501)
            ·
              refine ⟨6545679564014487315715313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17455145504038632841907501 6545679564014487315715313)
              ·
                refine ⟨4909259673010865486786485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545679564014487315715313 4909259673010865486786485)
                ·
                  refine ⟨460243094344768639386233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4909259673010865486786485 460243094344768639386233)
                  ·
                    rfl

theorem cell22_4033441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_4033441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033441 prefixEnd_4033441 := by exact prefixLift 4033441
  have htrace : WordTrace (prefixWord ++ tailWord_4033441) baseStart_4033441 baseEnd_4033441 := by
    simpa [prefixWord, tailWord_4033441, baseEnd_4033441] using wordTrace_append hprefix tailTrace_4033441
  have hstable : (prefixWord ++ tailWord_4033441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033441).length < 2 ^ (prefixWord ++ tailWord_4033441).sum := by decide
  have hdescent : baseEnd_4033441 < baseStart_4033441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033452 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 10]
def baseStart_4033452 : Nat := 118140960795 + 4033452 * 2 ^ 59
def prefixEnd_4033452 : Nat := 4983230072969 + 3 ^ 40 * 4033452 * 2
def baseEnd_4033452 : Nat := 460244349519701852044555

theorem tailTrace_4033452 : CollatzResearch.WordTrace tailWord_4033452 prefixEnd_4033452 460244349519701852044555 := by
  unfold tailWord_4033452
  simp only [CollatzResearch.WordTrace]
  refine ⟨73556040091749868801931305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98074720122333158402575073 73556040091749868801931305)
  ·
    refine ⟨55167030068812401601448479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73556040091749868801931305 55167030068812401601448479)
    ·
      refine ⟨82750545103218602402172719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55167030068812401601448479 82750545103218602402172719)
      ·
        refine ⟨124125817654827903603259079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82750545103218602402172719 124125817654827903603259079)
        ·
          refine ⟨186188726482241855404888619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124125817654827903603259079 186188726482241855404888619)
          ·
            refine ⟨279283089723362783107332929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186188726482241855404888619 279283089723362783107332929)
            ·
              refine ⟨209462317292522087330499697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279283089723362783107332929 209462317292522087330499697)
              ·
                refine ⟨157096737969391565497874773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209462317292522087330499697 157096737969391565497874773)
                ·
                  refine ⟨460244349519701852044555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 157096737969391565497874773 460244349519701852044555)
                  ·
                    rfl

theorem cell22_4033452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_4033452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033452 prefixEnd_4033452 := by exact prefixLift 4033452
  have htrace : WordTrace (prefixWord ++ tailWord_4033452) baseStart_4033452 baseEnd_4033452 := by
    simpa [prefixWord, tailWord_4033452, baseEnd_4033452] using wordTrace_append hprefix tailTrace_4033452
  have hstable : (prefixWord ++ tailWord_4033452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033452).length < 2 ^ (prefixWord ++ tailWord_4033452).sum := by decide
  have hdescent : baseEnd_4033452 < baseStart_4033452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033484 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_4033484 : Nat := 118140960795 + 4033484 * 2 ^ 59
def prefixEnd_4033484 : Nat := 4983230072969 + 3 ^ 40 * 4033484 * 2
def baseEnd_4033484 : Nat := 1380744002813068139333567

theorem tailTrace_4033484 : CollatzResearch.WordTrace tailWord_4033484 prefixEnd_4033484 1380744002813068139333567 := by
  unfold tailWord_4033484
  simp only [CollatzResearch.WordTrace]
  refine ⟨73556623659691903534513753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98075498212922538046018337 73556623659691903534513753)
  ·
    refine ⟨55167467744768927650885315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73556623659691903534513753 55167467744768927650885315)
    ·
      refine ⟨82751201617153391476327973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55167467744768927650885315 82751201617153391476327973)
      ·
        refine ⟨15515850303216260901811495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82751201617153391476327973 15515850303216260901811495)
        ·
          refine ⟨23273775454824391352717243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15515850303216260901811495 23273775454824391352717243)
          ·
            refine ⟨34910663182236587029075865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23273775454824391352717243 34910663182236587029075865)
            ·
              refine ⟨26182997386677440271806899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34910663182236587029075865 26182997386677440271806899)
              ·
                refine ⟨39274496080016160407710349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26182997386677440271806899 39274496080016160407710349)
                ·
                  refine ⟨14727936030006060152891381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39274496080016160407710349 14727936030006060152891381)
                  ·
                    refine ⟨1380744002813068139333567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14727936030006060152891381 1380744002813068139333567)
                    ·
                      rfl

theorem cell22_4033484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_4033484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033484 prefixEnd_4033484 := by exact prefixLift 4033484
  have htrace : WordTrace (prefixWord ++ tailWord_4033484) baseStart_4033484 baseEnd_4033484 := by
    simpa [prefixWord, tailWord_4033484, baseEnd_4033484] using wordTrace_append hprefix tailTrace_4033484
  have hstable : (prefixWord ++ tailWord_4033484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033484).length < 2 ^ (prefixWord ++ tailWord_4033484).sum := by decide
  have hdescent : baseEnd_4033484 < baseStart_4033484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033503 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 6]
def baseStart_4033503 : Nat := 118140960795 + 4033503 * 2 ^ 59
def prefixEnd_4033503 : Nat := 4983230072969 + 3 ^ 40 * 4033503 * 2
def baseEnd_4033503 : Nat := 460250168967119474369503

theorem tailTrace_4033503 : CollatzResearch.WordTrace tailWord_4033503 prefixEnd_4033503 460250168967119474369503 := by
  unfold tailWord_4033503
  simp only [CollatzResearch.WordTrace]
  refine ⟨147113940306314973313969163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98075960204209982209312775 147113940306314973313969163)
  ·
    refine ⟨220670910459472459970953745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147113940306314973313969163 220670910459472459970953745)
    ·
      refine ⟨165503182844604344978215309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220670910459472459970953745 165503182844604344978215309)
      ·
        refine ⟨62063693566726629366830741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165503182844604344978215309 62063693566726629366830741)
        ·
          refine ⟨2909235635940310751570191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62063693566726629366830741 2909235635940310751570191)
          ·
            refine ⟨4363853453910466127355287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909235635940310751570191 4363853453910466127355287)
            ·
              refine ⟨6545780180865699191032931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363853453910466127355287 6545780180865699191032931)
              ·
                refine ⟨9818670271298548786549397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545780180865699191032931 9818670271298548786549397)
                ·
                  refine ⟨460250168967119474369503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9818670271298548786549397 460250168967119474369503)
                  ·
                    rfl

theorem cell22_4033503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 6].length) (baseStart_4033503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033503 prefixEnd_4033503 := by exact prefixLift 4033503
  have htrace : WordTrace (prefixWord ++ tailWord_4033503) baseStart_4033503 baseEnd_4033503 := by
    simpa [prefixWord, tailWord_4033503, baseEnd_4033503] using wordTrace_append hprefix tailTrace_4033503
  have hstable : (prefixWord ++ tailWord_4033503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033503).length < 2 ^ (prefixWord ++ tailWord_4033503).sum := by decide
  have hdescent : baseEnd_4033503 < baseStart_4033503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033514 : List Nat := [3, 1, 3, 1, 2, 2, 1, 9]
def baseStart_4033514 : Nat := 118140960795 + 4033514 * 2 ^ 59
def prefixEnd_4033514 : Nat := 4983230072969 + 3 ^ 40 * 4033514 * 2
def baseEnd_4033514 : Nat := 153417141380684229009275

theorem tailTrace_4033514 : CollatzResearch.WordTrace tailWord_4033514 prefixEnd_4033514 153417141380684229009275 := by
  unfold tailWord_4033514
  simp only [CollatzResearch.WordTrace]
  refine ⟨36778585377318780548154899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98076227672850081461746397 36778585377318780548154899)
  ·
    refine ⟨55167878065978170822232349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36778585377318780548154899 55167878065978170822232349)
    ·
      refine ⟨20687954274741814058337131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55167878065978170822232349 20687954274741814058337131)
      ·
        refine ⟨31031931412112721087505697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20687954274741814058337131 31031931412112721087505697)
        ·
          refine ⟨23273948559084540815629273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31031931412112721087505697 23273948559084540815629273)
          ·
            refine ⟨17455461419313405611721955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23273948559084540815629273 17455461419313405611721955)
            ·
              refine ⟨26183192128970108417582933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17455461419313405611721955 26183192128970108417582933)
              ·
                refine ⟨153417141380684229009275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26183192128970108417582933 153417141380684229009275)
                ·
                  rfl

theorem cell22_4033514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_4033514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033514 prefixEnd_4033514 := by exact prefixLift 4033514
  have htrace : WordTrace (prefixWord ++ tailWord_4033514) baseStart_4033514 baseEnd_4033514 := by
    simpa [prefixWord, tailWord_4033514, baseEnd_4033514] using wordTrace_append hprefix tailTrace_4033514
  have hstable : (prefixWord ++ tailWord_4033514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033514).length < 2 ^ (prefixWord ++ tailWord_4033514).sum := by decide
  have hdescent : baseEnd_4033514 < baseStart_4033514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033522 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_4033522 : Nat := 118140960795 + 4033522 * 2 ^ 59
def prefixEnd_4033522 : Nat := 4983230072969 + 3 ^ 40 * 4033522 * 2
def baseEnd_4033522 : Nat := 1380757010989648706883451

theorem tailTrace_4033522 : CollatzResearch.WordTrace tailWord_4033522 prefixEnd_4033522 1380757010989648706883451 := by
  unfold tailWord_4033522
  simp only [CollatzResearch.WordTrace]
  refine ⟨36778658323311534889727705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98076422195497426372607213 36778658323311534889727705)
  ·
    refine ⟨27583993742483651167295779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36778658323311534889727705 27583993742483651167295779)
    ·
      refine ⟨41375990613725476750943669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27583993742483651167295779 41375990613725476750943669)
      ·
        refine ⟨3878999120036763445400969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41375990613725476750943669 3878999120036763445400969)
        ·
          refine ⟨2909249340027572584050727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3878999120036763445400969 2909249340027572584050727)
          ·
            refine ⟨4363874010041358876076091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909249340027572584050727 4363874010041358876076091)
            ·
              refine ⟨6545811015062038314114137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363874010041358876076091 6545811015062038314114137)
              ·
                refine ⟨4909358261296528735585603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545811015062038314114137 4909358261296528735585603)
                ·
                  refine ⟨7364037391944793103378405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909358261296528735585603 7364037391944793103378405)
                  ·
                    refine ⟨1380757010989648706883451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7364037391944793103378405 1380757010989648706883451)
                    ·
                      rfl

theorem cell22_4033522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_4033522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033522 prefixEnd_4033522 := by exact prefixLift 4033522
  have htrace : WordTrace (prefixWord ++ tailWord_4033522) baseStart_4033522 baseEnd_4033522 := by
    simpa [prefixWord, tailWord_4033522, baseEnd_4033522] using wordTrace_append hprefix tailTrace_4033522
  have hstable : (prefixWord ++ tailWord_4033522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033522).length < 2 ^ (prefixWord ++ tailWord_4033522).sum := by decide
  have hdescent : baseEnd_4033522 < baseStart_4033522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033619 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 5, 5]
def baseStart_4033619 : Nat := 118140960795 + 4033619 * 2 ^ 59
def prefixEnd_4033619 : Nat := 4983230072969 + 3 ^ 40 * 4033619 * 2
def baseEnd_4033619 : Nat := 1380790216071972787208153

theorem tailTrace_4033619 : CollatzResearch.WordTrace tailWord_4033619 prefixEnd_4033619 1380790216071972787208153 := by
  unfold tailWord_4033619
  simp only [CollatzResearch.WordTrace]
  refine ⟨147118171173894725125191911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98078780782596483416794607 147118171173894725125191911)
  ·
    refine ⟨220677256760842087687787867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147118171173894725125191911 220677256760842087687787867)
    ·
      refine ⟨331015885141263131531681801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220677256760842087687787867 331015885141263131531681801)
      ·
        refine ⟨248261913855947348648761351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331015885141263131531681801 248261913855947348648761351)
        ·
          refine ⟨372392870783921022973142027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248261913855947348648761351 372392870783921022973142027)
          ·
            refine ⟨558589306175881534459713041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372392870783921022973142027 558589306175881534459713041)
            ·
              refine ⟨418941979631911150844784781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558589306175881534459713041 418941979631911150844784781)
              ·
                refine ⟨157103242361966681566794293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418941979631911150844784781 157103242361966681566794293)
                ·
                  refine ⟨14728428971434376396886965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157103242361966681566794293 14728428971434376396886965)
                  ·
                    refine ⟨1380790216071972787208153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14728428971434376396886965 1380790216071972787208153)
                    ·
                      rfl

theorem cell22_4033619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_4033619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033619 prefixEnd_4033619 := by exact prefixLift 4033619
  have htrace : WordTrace (prefixWord ++ tailWord_4033619) baseStart_4033619 baseEnd_4033619 := by
    simpa [prefixWord, tailWord_4033619, baseEnd_4033619] using wordTrace_append hprefix tailTrace_4033619
  have hstable : (prefixWord ++ tailWord_4033619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033619).length < 2 ^ (prefixWord ++ tailWord_4033619).sum := by decide
  have hdescent : baseEnd_4033619 < baseStart_4033619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033621 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 6]
def baseStart_4033621 : Nat := 118140960795 + 4033621 * 2 ^ 59
def prefixEnd_4033621 : Nat := 4983230072969 + 3 ^ 40 * 4033621 * 2
def baseEnd_4033621 : Nat := 460263633570948482886049

theorem tailTrace_4033621 : CollatzResearch.WordTrace tailWord_4033621 prefixEnd_4033621 460263633570948482886049 := by
  unfold tailWord_4033621
  simp only [CollatzResearch.WordTrace]
  refine ⟨147118244119887479466764717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98078829413258319644509811 147118244119887479466764717)
  ·
    refine ⟨55169341544957804800036769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147118244119887479466764717 55169341544957804800036769)
    ·
      refine ⟨41377006158718353600027577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55169341544957804800036769 41377006158718353600027577)
      ·
        refine ⟨31032754619038765200020683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41377006158718353600027577 31032754619038765200020683)
        ·
          refine ⟨46549131928558147800031025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31032754619038765200020683 46549131928558147800031025)
          ·
            refine ⟨34911848946418610850023269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46549131928558147800031025 34911848946418610850023269)
            ·
              refine ⟨6545971677453489534379363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34911848946418610850023269 6545971677453489534379363)
              ·
                refine ⟨9818957516180234301569045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545971677453489534379363 9818957516180234301569045)
                ·
                  refine ⟨460263633570948482886049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9818957516180234301569045 460263633570948482886049)
                  ·
                    rfl

theorem cell22_4033621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_4033621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033621 prefixEnd_4033621 := by exact prefixLift 4033621
  have htrace : WordTrace (prefixWord ++ tailWord_4033621) baseStart_4033621 baseEnd_4033621 := by
    simpa [prefixWord, tailWord_4033621, baseEnd_4033621] using wordTrace_append hprefix tailTrace_4033621
  have hstable : (prefixWord ++ tailWord_4033621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033621).length < 2 ^ (prefixWord ++ tailWord_4033621).sum := by decide
  have hdescent : baseEnd_4033621 < baseStart_4033621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033668 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_4033668 : Nat := 118140960795 + 4033668 * 2 ^ 59
def prefixEnd_4033668 : Nat := 4983230072969 + 3 ^ 40 * 4033668 * 2
def baseEnd_4033668 : Nat := 1380806989773352992733003

theorem tailTrace_4033668 : CollatzResearch.WordTrace tailWord_4033668 prefixEnd_4033668 1380806989773352992733003 := by
  unfold tailWord_4033668
  simp only [CollatzResearch.WordTrace]
  refine ⟨73559979175358603246862829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98079972233811470995817105 73559979175358603246862829)
  ·
    refine ⟨27584992190759476217573561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73559979175358603246862829 27584992190759476217573561)
    ·
      refine ⟨20688744143069607163180171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27584992190759476217573561 20688744143069607163180171)
      ·
        refine ⟨31033116214604410744770257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20688744143069607163180171 31033116214604410744770257)
        ·
          refine ⟨23274837160953308058577693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31033116214604410744770257 23274837160953308058577693)
          ·
            refine ⟨8728063935357490521966635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23274837160953308058577693 8728063935357490521966635)
            ·
              refine ⟨13092095903036235782949953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728063935357490521966635 13092095903036235782949953)
              ·
                refine ⟨9819071927277176837212465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13092095903036235782949953 9819071927277176837212465)
                ·
                  refine ⟨7364303945457882627909349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9819071927277176837212465 7364303945457882627909349)
                  ·
                    refine ⟨1380806989773352992733003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7364303945457882627909349 1380806989773352992733003)
                    ·
                      rfl

theorem cell22_4033668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_4033668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033668 prefixEnd_4033668 := by exact prefixLift 4033668
  have htrace : WordTrace (prefixWord ++ tailWord_4033668) baseStart_4033668 baseEnd_4033668 := by
    simpa [prefixWord, tailWord_4033668, baseEnd_4033668] using wordTrace_append hprefix tailTrace_4033668
  have hstable : (prefixWord ++ tailWord_4033668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033668).length < 2 ^ (prefixWord ++ tailWord_4033668).sum := by decide
  have hdescent : baseEnd_4033668 < baseStart_4033668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033672 : List Nat := [2, 1, 3, 4, 2, 1, 3, 2, 4]
def baseStart_4033672 : Nat := 118140960795 + 4033672 * 2 ^ 59
def prefixEnd_4033672 : Nat := 4983230072969 + 3 ^ 40 * 4033672 * 2
def baseEnd_4033672 : Nat := 460269453018366105210997

theorem tailTrace_4033672 : CollatzResearch.WordTrace tailWord_4033672 prefixEnd_4033672 460269453018366105210997 := by
  unfold tailWord_4033672
  simp only [CollatzResearch.WordTrace]
  refine ⟨73560052121351357588435635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98080069495135143451247513 73560052121351357588435635)
  ·
    refine ⟨110340078182027036382653453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73560052121351357588435635 110340078182027036382653453)
    ·
      refine ⟨41377529318260138643495045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110340078182027036382653453 41377529318260138643495045)
      ·
        refine ⟨7758286747173775995655321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41377529318260138643495045 7758286747173775995655321)
        ·
          refine ⟨5818715060380331996741491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7758286747173775995655321 5818715060380331996741491)
          ·
            refine ⟨8728072590570497995112237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5818715060380331996741491 8728072590570497995112237)
            ·
              refine ⟨3273027221463936748167089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8728072590570497995112237 3273027221463936748167089)
              ·
                refine ⟨2454770416097952561125317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273027221463936748167089 2454770416097952561125317)
                ·
                  refine ⟨460269453018366105210997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2454770416097952561125317 460269453018366105210997)
                  ·
                    rfl

theorem cell22_4033672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 4].length) (baseStart_4033672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033672 prefixEnd_4033672 := by exact prefixLift 4033672
  have htrace : WordTrace (prefixWord ++ tailWord_4033672) baseStart_4033672 baseEnd_4033672 := by
    simpa [prefixWord, tailWord_4033672, baseEnd_4033672] using wordTrace_append hprefix tailTrace_4033672
  have hstable : (prefixWord ++ tailWord_4033672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033672).length < 2 ^ (prefixWord ++ tailWord_4033672).sum := by decide
  have hdescent : baseEnd_4033672 < baseStart_4033672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033687 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 2, 3]
def baseStart_4033687 : Nat := 118140960795 + 4033687 * 2 ^ 59
def prefixEnd_4033687 : Nat := 4983230072969 + 3 ^ 40 * 4033687 * 2
def baseEnd_4033687 : Nat := 1380813493861643276507945

theorem tailTrace_4033687 : CollatzResearch.WordTrace tailWord_4033687 prefixEnd_4033687 1380813493861643276507945 := by
  unfold tailWord_4033687
  simp only [CollatzResearch.WordTrace]
  refine ⟨147120651337648372738667315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98080434225098915159111543 147120651337648372738667315)
  ·
    refine ⟨220680977006472559108000973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147120651337648372738667315 220680977006472559108000973)
    ·
      refine ⟨82755366377427209665500365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220680977006472559108000973 82755366377427209665500365)
      ·
        refine ⟨31033262391535203624562637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82755366377427209665500365 31033262391535203624562637)
        ·
          refine ⟨11637473396825701359210989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31033262391535203624562637 11637473396825701359210989)
          ·
            refine ⟨4364052523809638009704121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11637473396825701359210989 4364052523809638009704121)
            ·
              refine ⟨3273039392857228507278091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364052523809638009704121 3273039392857228507278091)
              ·
                refine ⟨4909559089285842760917137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273039392857228507278091 4909559089285842760917137)
                ·
                  refine ⟨3682169316964382070687853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4909559089285842760917137 3682169316964382070687853)
                  ·
                    refine ⟨1380813493861643276507945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3682169316964382070687853 1380813493861643276507945)
                    ·
                      rfl

theorem cell22_4033687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_4033687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033687 prefixEnd_4033687 := by exact prefixLift 4033687
  have htrace : WordTrace (prefixWord ++ tailWord_4033687) baseStart_4033687 baseEnd_4033687 := by
    simpa [prefixWord, tailWord_4033687, baseEnd_4033687] using wordTrace_append hprefix tailTrace_4033687
  have hstable : (prefixWord ++ tailWord_4033687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033687).length < 2 ^ (prefixWord ++ tailWord_4033687).sum := by decide
  have hdescent : baseEnd_4033687 < baseStart_4033687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033734 : List Nat := [6, 1, 2, 2, 1, 2, 1, 7]
def baseStart_4033734 : Nat := 118140960795 + 4033734 * 2 ^ 59
def prefixEnd_4033734 : Nat := 4983230072969 + 3 ^ 40 * 4033734 * 2
def baseEnd_4033734 : Nat := 153425509213572313398089

theorem tailTrace_4033734 : CollatzResearch.WordTrace tailWord_4033734 prefixEnd_4033734 153425509213572313398089 := by
  unfold tailWord_4033734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597573924014940617675883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98081577045652066510418837 4597573924014940617675883)
  ·
    refine ⟨6896360886022410926513825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4597573924014940617675883 6896360886022410926513825)
    ·
      refine ⟨5172270664516808194885369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6896360886022410926513825 5172270664516808194885369)
      ·
        refine ⟨3879202998387606146164027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5172270664516808194885369 3879202998387606146164027)
        ·
          refine ⟨5818804497581409219246041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3879202998387606146164027 5818804497581409219246041)
          ·
            refine ⟨4364103373186056914434531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5818804497581409219246041 4364103373186056914434531)
            ·
              refine ⟨6546155059779085371651797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364103373186056914434531 6546155059779085371651797)
              ·
                refine ⟨153425509213572313398089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6546155059779085371651797 153425509213572313398089)
                ·
                  rfl

theorem cell22_4033734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_4033734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033734 prefixEnd_4033734 := by exact prefixLift 4033734
  have htrace : WordTrace (prefixWord ++ tailWord_4033734) baseStart_4033734 baseEnd_4033734 := by
    simpa [prefixWord, tailWord_4033734, baseEnd_4033734] using wordTrace_append hprefix tailTrace_4033734
  have hstable : (prefixWord ++ tailWord_4033734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033734).length < 2 ^ (prefixWord ++ tailWord_4033734).sum := by decide
  have hdescent : baseEnd_4033734 < baseStart_4033734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033775 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 1, 4]
def baseStart_4033775 : Nat := 118140960795 + 4033775 * 2 ^ 59
def prefixEnd_4033775 : Nat := 4983230072969 + 3 ^ 40 * 4033775 * 2
def baseEnd_4033775 : Nat := 1380843618060040380307675

theorem tailTrace_4033775 : CollatzResearch.WordTrace tailWord_4033775 prefixEnd_4033775 1380843618060040380307675 := by
  unfold tailWord_4033775
  simp only [CollatzResearch.WordTrace]
  refine ⟨147123860961329563767870779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98082573974219709178580519 147123860961329563767870779)
  ·
    refine ⟨220685791441994345651806169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147123860961329563767870779 220685791441994345651806169)
    ·
      refine ⟨165514343581495759238854627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220685791441994345651806169 165514343581495759238854627)
      ·
        refine ⟨248271515372243638858281941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165514343581495759238854627 248271515372243638858281941)
        ·
          refine ⟨5818863641536960285740983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 248271515372243638858281941 5818863641536960285740983)
          ·
            refine ⟨8728295462305440428611475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5818863641536960285740983 8728295462305440428611475)
            ·
              refine ⟨13092443193458160642917213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728295462305440428611475 13092443193458160642917213)
              ·
                refine ⟨4909666197546810241093955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13092443193458160642917213 4909666197546810241093955)
                ·
                  refine ⟨7364499296320215361640933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909666197546810241093955 7364499296320215361640933)
                  ·
                    refine ⟨1380843618060040380307675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7364499296320215361640933 1380843618060040380307675)
                    ·
                      rfl

theorem cell22_4033775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_4033775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033775 prefixEnd_4033775 := by exact prefixLift 4033775
  have htrace : WordTrace (prefixWord ++ tailWord_4033775) baseStart_4033775 baseEnd_4033775 := by
    simpa [prefixWord, tailWord_4033775, baseEnd_4033775] using wordTrace_append hprefix tailTrace_4033775
  have hstable : (prefixWord ++ tailWord_4033775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033775).length < 2 ^ (prefixWord ++ tailWord_4033775).sum := by decide
  have hdescent : baseEnd_4033775 < baseStart_4033775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033790 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_4033790 : Nat := 118140960795 + 4033790 * 2 ^ 59
def prefixEnd_4033790 : Nat := 4983230072969 + 3 ^ 40 * 4033790 * 2
def baseEnd_4033790 : Nat := 460282917622195113727543

theorem tailTrace_4033790 : CollatzResearch.WordTrace tailWord_4033790 prefixEnd_4033790 460282917622195113727543 := by
  unfold tailWord_4033790
  simp only [CollatzResearch.WordTrace]
  refine ⟨18390551007034402666208353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98082938704183480886444549 18390551007034402666208353)
  ·
    refine ⟨13792913255275801999656265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18390551007034402666208353 13792913255275801999656265)
    ·
      refine ⟨10344684941456851499742199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13792913255275801999656265 10344684941456851499742199)
      ·
        refine ⟨15517027412185277249613299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10344684941456851499742199 15517027412185277249613299)
        ·
          refine ⟨23275541118277915874419949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15517027412185277249613299 23275541118277915874419949)
          ·
            refine ⟨8728327919354218452907481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23275541118277915874419949 8728327919354218452907481)
            ·
              refine ⟨6546245939515663839680611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8728327919354218452907481 6546245939515663839680611)
              ·
                refine ⟨9819368909273495759520917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546245939515663839680611 9819368909273495759520917)
                ·
                  refine ⟨460282917622195113727543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9819368909273495759520917 460282917622195113727543)
                  ·
                    rfl

theorem cell22_4033790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_4033790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033790 prefixEnd_4033790 := by exact prefixLift 4033790
  have htrace : WordTrace (prefixWord ++ tailWord_4033790) baseStart_4033790 baseEnd_4033790 := by
    simpa [prefixWord, tailWord_4033790, baseEnd_4033790] using wordTrace_append hprefix tailTrace_4033790
  have hstable : (prefixWord ++ tailWord_4033790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033790).length < 2 ^ (prefixWord ++ tailWord_4033790).sum := by decide
  have hdescent : baseEnd_4033790 < baseStart_4033790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033801 : List Nat := [1, 2, 1, 1, 3, 3, 2, 9]
def baseStart_4033801 : Nat := 118140960795 + 4033801 * 2 ^ 59
def prefixEnd_4033801 : Nat := 4983230072969 + 3 ^ 40 * 4033801 * 2
def baseEnd_4033801 : Nat := 153428057599042775461955

theorem tailTrace_4033801 : CollatzResearch.WordTrace tailWord_4033801 prefixEnd_4033801 153428057599042775461955 := by
  unfold tailWord_4033801
  simp only [CollatzResearch.WordTrace]
  refine ⟨147124809259235370208317257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98083206172823580138878171 147124809259235370208317257)
  ·
    refine ⟨110343606944426527656237943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147124809259235370208317257 110343606944426527656237943)
    ·
      refine ⟨165515410416639791484356915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110343606944426527656237943 165515410416639791484356915)
      ·
        refine ⟨248273115624959687226535373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165515410416639791484356915 248273115624959687226535373)
        ·
          refine ⟨93102418359359882709950765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248273115624959687226535373 93102418359359882709950765)
          ·
            refine ⟨34913406884759956016231537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93102418359359882709950765 34913406884759956016231537)
            ·
              refine ⟨26185055163569967012173653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34913406884759956016231537 26185055163569967012173653)
              ·
                refine ⟨153428057599042775461955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26185055163569967012173653 153428057599042775461955)
                ·
                  rfl

theorem cell22_4033801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 9].length) (baseStart_4033801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033801 prefixEnd_4033801 := by exact prefixLift 4033801
  have htrace : WordTrace (prefixWord ++ tailWord_4033801) baseStart_4033801 baseEnd_4033801 := by
    simpa [prefixWord, tailWord_4033801, baseEnd_4033801] using wordTrace_append hprefix tailTrace_4033801
  have hstable : (prefixWord ++ tailWord_4033801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033801).length < 2 ^ (prefixWord ++ tailWord_4033801).sum := by decide
  have hdescent : baseEnd_4033801 < baseStart_4033801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033818 : List Nat := [3, 1, 1, 3, 3, 2, 1, 8]
def baseStart_4033818 : Nat := 118140960795 + 4033818 * 2 ^ 59
def prefixEnd_4033818 : Nat := 4983230072969 + 3 ^ 40 * 4033818 * 2
def baseEnd_4033818 : Nat := 153428704204311400164727

theorem tailTrace_4033818 : CollatzResearch.WordTrace tailWord_4033818 prefixEnd_4033818 153428704204311400164727 := by
  unfold tailWord_4033818
  simp only [CollatzResearch.WordTrace]
  refine ⟨36781357325043445527921527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98083619533449188074457405 36781357325043445527921527)
  ·
    refine ⟨55172035987565168291882291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36781357325043445527921527 55172035987565168291882291)
    ·
      refine ⟨82758053981347752437823437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55172035987565168291882291 82758053981347752437823437)
      ·
        refine ⟨31034270243005407164183789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82758053981347752437823437 31034270243005407164183789)
        ·
          refine ⟨11637851341127027686568921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31034270243005407164183789 11637851341127027686568921)
          ·
            refine ⟨8728388505845270764926691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11637851341127027686568921 8728388505845270764926691)
            ·
              refine ⟨13092582758767906147390037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728388505845270764926691 13092582758767906147390037)
              ·
                refine ⟨153428704204311400164727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13092582758767906147390037 153428704204311400164727)
                ·
                  rfl

theorem cell22_4033818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_4033818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033818 prefixEnd_4033818 := by exact prefixLift 4033818
  have htrace : WordTrace (prefixWord ++ tailWord_4033818) baseStart_4033818 baseEnd_4033818 := by
    simpa [prefixWord, tailWord_4033818, baseEnd_4033818] using wordTrace_append hprefix tailTrace_4033818
  have hstable : (prefixWord ++ tailWord_4033818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033818).length < 2 ^ (prefixWord ++ tailWord_4033818).sum := by decide
  have hdescent : baseEnd_4033818 < baseStart_4033818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033824 : List Nat := [2, 1, 1, 5, 4, 1, 1, 3, 4]
def baseStart_4033824 : Nat := 118140960795 + 4033824 * 2 ^ 59
def prefixEnd_4033824 : Nat := 4983230072969 + 3 ^ 40 * 4033824 * 2
def baseEnd_4033824 : Nat := 460286797253806861944175

theorem tailTrace_4033824 : CollatzResearch.WordTrace tailWord_4033824 prefixEnd_4033824 460286797253806861944175 := by
  unfold tailWord_4033824
  simp only [CollatzResearch.WordTrace]
  refine ⟨73562824069076022568202263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98083765425434696757603017 73562824069076022568202263)
  ·
    refine ⟨110344236103614033852303395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73562824069076022568202263 110344236103614033852303395)
    ·
      refine ⟨165516354155421050778455093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110344236103614033852303395 165516354155421050778455093)
      ·
        refine ⟨15517158202070723510480165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165516354155421050778455093 15517158202070723510480165)
        ·
          refine ⟨2909467162888260658215031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15517158202070723510480165 2909467162888260658215031)
          ·
            refine ⟨4364200744332390987322547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909467162888260658215031 4364200744332390987322547)
            ·
              refine ⟨6546301116498586480983821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364200744332390987322547 6546301116498586480983821)
              ·
                refine ⟨2454862918686969930368933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6546301116498586480983821 2454862918686969930368933)
                ·
                  refine ⟨460286797253806861944175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2454862918686969930368933 460286797253806861944175)
                  ·
                    rfl

theorem cell22_4033824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 4].length) (baseStart_4033824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033824 prefixEnd_4033824 := by exact prefixLift 4033824
  have htrace : WordTrace (prefixWord ++ tailWord_4033824) baseStart_4033824 baseEnd_4033824 := by
    simpa [prefixWord, tailWord_4033824, baseEnd_4033824] using wordTrace_append hprefix tailTrace_4033824
  have hstable : (prefixWord ++ tailWord_4033824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033824).length < 2 ^ (prefixWord ++ tailWord_4033824).sum := by decide
  have hdescent : baseEnd_4033824 < baseStart_4033824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033837 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4033837 : Nat := 118140960795 + 4033837 * 2 ^ 59
def prefixEnd_4033837 : Nat := 4983230072969 + 3 ^ 40 * 4033837 * 2
def baseEnd_4033837 : Nat := 1380864841927092885257485

theorem tailTrace_4033837 : CollatzResearch.WordTrace tailWord_4033837 prefixEnd_4033837 1380864841927092885257485 := by
  unfold tailWord_4033837
  simp only [CollatzResearch.WordTrace]
  refine ⟨147126122287104948356627765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98084081524736632237751843 147126122287104948356627765)
  ·
    refine ⟨13793073964416088908433853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147126122287104948356627765 13793073964416088908433853)
    ·
      refine ⟨5172402736656033340662695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13793073964416088908433853 5172402736656033340662695)
      ·
        refine ⟨7758604104984050010994043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172402736656033340662695 7758604104984050010994043)
        ·
          refine ⟨11637906157476075016491065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758604104984050010994043 11637906157476075016491065)
          ·
            refine ⟨8728429618107056262368299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11637906157476075016491065 8728429618107056262368299)
            ·
              refine ⟨13092644427160584393552449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728429618107056262368299 13092644427160584393552449)
              ·
                refine ⟨9819483320370438295164337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13092644427160584393552449 9819483320370438295164337)
                ·
                  refine ⟨7364612490277828721373253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9819483320370438295164337 7364612490277828721373253)
                  ·
                    refine ⟨1380864841927092885257485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7364612490277828721373253 1380864841927092885257485)
                    ·
                      rfl

theorem cell22_4033837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4033837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033837 prefixEnd_4033837 := by exact prefixLift 4033837
  have htrace : WordTrace (prefixWord ++ tailWord_4033837) baseStart_4033837 baseEnd_4033837 := by
    simpa [prefixWord, tailWord_4033837, baseEnd_4033837] using wordTrace_append hprefix tailTrace_4033837
  have hstable : (prefixWord ++ tailWord_4033837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033837).length < 2 ^ (prefixWord ++ tailWord_4033837).sum := by decide
  have hdescent : baseEnd_4033837 < baseStart_4033837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033901 : List Nat := [1, 5, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_4033901 : Nat := 118140960795 + 4033901 * 2 ^ 59
def prefixEnd_4033901 : Nat := 4983230072969 + 3 ^ 40 * 4033901 * 2
def baseEnd_4033901 : Nat := 1380886750435018051657289

theorem tailTrace_4033901 : CollatzResearch.WordTrace tailWord_4033901 prefixEnd_4033901 1380886750435018051657289 := by
  unfold tailWord_4033901
  simp only [CollatzResearch.WordTrace]
  refine ⟨147128456558873087286957557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98085637705915391524638371 147128456558873087286957557)
  ·
    refine ⟨13793292802394351933152271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147128456558873087286957557 13793292802394351933152271)
    ·
      refine ⟨20689939203591527899728407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13793292802394351933152271 20689939203591527899728407)
      ·
        refine ⟨31034908805387291849592611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20689939203591527899728407 31034908805387291849592611)
        ·
          refine ⟨46552363208080937774388917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31034908805387291849592611 46552363208080937774388917)
          ·
            refine ⟨4364284050757587916348961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46552363208080937774388917 4364284050757587916348961)
            ·
              refine ⟨3273213038068190937261721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364284050757587916348961 3273213038068190937261721)
              ·
                refine ⟨2454909778551143202946291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273213038068190937261721 2454909778551143202946291)
                ·
                  refine ⟨3682364667826714804419437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454909778551143202946291 3682364667826714804419437)
                  ·
                    refine ⟨1380886750435018051657289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3682364667826714804419437 1380886750435018051657289)
                    ·
                      rfl

theorem cell22_4033901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_4033901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033901 prefixEnd_4033901 := by exact prefixLift 4033901
  have htrace : WordTrace (prefixWord ++ tailWord_4033901) baseStart_4033901 baseEnd_4033901 := by
    simpa [prefixWord, tailWord_4033901, baseEnd_4033901] using wordTrace_append hprefix tailTrace_4033901
  have hstable : (prefixWord ++ tailWord_4033901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033901).length < 2 ^ (prefixWord ++ tailWord_4033901).sum := by decide
  have hdescent : baseEnd_4033901 < baseStart_4033901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033983 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 2, 6]
def baseStart_4033983 : Nat := 118140960795 + 4033983 * 2 ^ 59
def prefixEnd_4033983 : Nat := 4983230072969 + 3 ^ 40 * 4033983 * 2
def baseEnd_4033983 : Nat := 1380914820710797171107037

theorem tailTrace_4033983 : CollatzResearch.WordTrace tailWord_4033983 prefixEnd_4033983 1380914820710797171107037 := by
  unfold tailWord_4033983
  simp only [CollatzResearch.WordTrace]
  refine ⟨147131447344576015291442603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98087631563050676860961735 147131447344576015291442603)
  ·
    refine ⟨220697171016864022937163905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147131447344576015291442603 220697171016864022937163905)
    ·
      refine ⟨165522878262648017202872929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220697171016864022937163905 165522878262648017202872929)
      ·
        refine ⟨124142158696986012902154697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165522878262648017202872929 124142158696986012902154697)
        ·
          refine ⟨93106619022739509676616023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124142158696986012902154697 93106619022739509676616023)
          ·
            refine ⟨139659928534109264514924035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93106619022739509676616023 139659928534109264514924035)
            ·
              refine ⟨209489892801163896772386053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139659928534109264514924035 209489892801163896772386053)
              ·
                refine ⟨39279354900218230644822385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209489892801163896772386053 39279354900218230644822385)
                ·
                  refine ⟨29459516175163672983616789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39279354900218230644822385 29459516175163672983616789)
                  ·
                    refine ⟨1380914820710797171107037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29459516175163672983616789 1380914820710797171107037)
                    ·
                      rfl

theorem cell22_4033983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_4033983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4033983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4033983 prefixEnd_4033983 := by exact prefixLift 4033983
  have htrace : WordTrace (prefixWord ++ tailWord_4033983) baseStart_4033983 baseEnd_4033983 := by
    simpa [prefixWord, tailWord_4033983, baseEnd_4033983] using wordTrace_append hprefix tailTrace_4033983
  have hstable : (prefixWord ++ tailWord_4033983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033983).length < 2 ^ (prefixWord ++ tailWord_4033983).sum := by decide
  have hdescent : baseEnd_4033983 < baseStart_4033983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034015 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 5]
def baseStart_4034015 : Nat := 118140960795 + 4034015 * 2 ^ 59
def prefixEnd_4034015 : Nat := 4983230072969 + 3 ^ 40 * 4034015 * 2
def baseEnd_4034015 : Nat := 460308591654919918102313

theorem tailTrace_4034015 : CollatzResearch.WordTrace tailWord_4034015 prefixEnd_4034015 460308591654919918102313 := by
  unfold tailWord_4034015
  simp only [CollatzResearch.WordTrace]
  refine ⟨147132614480460084756607499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98088409653640056504404999 147132614480460084756607499)
  ·
    refine ⟨220698921720690127134911249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147132614480460084756607499 220698921720690127134911249)
    ·
      refine ⟨165524191290517595351183437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220698921720690127134911249 165524191290517595351183437)
      ·
        refine ⟨62071571733944098256693789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165524191290517595351183437 62071571733944098256693789)
        ·
          refine ⟨23276839400229036846260171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62071571733944098256693789 23276839400229036846260171)
          ·
            refine ⟨34915259100343555269390257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23276839400229036846260171 34915259100343555269390257)
            ·
              refine ⟨26186444325257666452042693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34915259100343555269390257 26186444325257666452042693)
              ·
                refine ⟨4909958310985812459758005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26186444325257666452042693 4909958310985812459758005)
                ·
                  refine ⟨460308591654919918102313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4909958310985812459758005 460308591654919918102313)
                  ·
                    rfl

theorem cell22_4034015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 5].length) (baseStart_4034015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034015 prefixEnd_4034015 := by exact prefixLift 4034015
  have htrace : WordTrace (prefixWord ++ tailWord_4034015) baseStart_4034015 baseEnd_4034015 := by
    simpa [prefixWord, tailWord_4034015, baseEnd_4034015] using wordTrace_append hprefix tailTrace_4034015
  have hstable : (prefixWord ++ tailWord_4034015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034015).length < 2 ^ (prefixWord ++ tailWord_4034015).sum := by decide
  have hdescent : baseEnd_4034015 < baseStart_4034015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034019 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 3, 3]
def baseStart_4034019 : Nat := 118140960795 + 4034019 * 2 ^ 59
def prefixEnd_4034019 : Nat := 4983230072969 + 3 ^ 40 * 4034019 * 2
def baseEnd_4034019 : Nat := 1380927144246505077206927

theorem tailTrace_4034019 : CollatzResearch.WordTrace tailWord_4034019 prefixEnd_4034019 1380927144246505077206927 := by
  unfold tailWord_4034019
  simp only [CollatzResearch.WordTrace]
  refine ⟨147132760372445593439753111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98088506914963728959835407 147132760372445593439753111)
  ·
    refine ⟨220699140558668390159629667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147132760372445593439753111 220699140558668390159629667)
    ·
      refine ⟨331048710838002585239444501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220699140558668390159629667 331048710838002585239444501)
      ·
        refine ⟨15517908320531371183098961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 331048710838002585239444501 15517908320531371183098961)
        ·
          refine ⟨11638431240398528387324221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15517908320531371183098961 11638431240398528387324221)
          ·
            refine ⟨4364411715149448145246583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11638431240398528387324221 4364411715149448145246583)
            ·
              refine ⟨6546617572724172217869875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364411715149448145246583 6546617572724172217869875)
              ·
                refine ⟨9819926359086258326804813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546617572724172217869875 9819926359086258326804813)
                ·
                  refine ⟨3682472384657346872551805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9819926359086258326804813 3682472384657346872551805)
                  ·
                    refine ⟨1380927144246505077206927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3682472384657346872551805 1380927144246505077206927)
                    ·
                      rfl

theorem cell22_4034019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 3].length) (baseStart_4034019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034019 prefixEnd_4034019 := by exact prefixLift 4034019
  have htrace : WordTrace (prefixWord ++ tailWord_4034019) baseStart_4034019 baseEnd_4034019 := by
    simpa [prefixWord, tailWord_4034019, baseEnd_4034019] using wordTrace_append hprefix tailTrace_4034019
  have hstable : (prefixWord ++ tailWord_4034019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034019).length < 2 ^ (prefixWord ++ tailWord_4034019).sum := by decide
  have hdescent : baseEnd_4034019 < baseStart_4034019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034030 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_4034030 : Nat := 118140960795 + 4034030 * 2 ^ 59
def prefixEnd_4034030 : Nat := 4983230072969 + 3 ^ 40 * 4034030 * 2
def baseEnd_4034030 : Nat := 1380930909771304715181893

theorem tailTrace_4034030 : CollatzResearch.WordTrace tailWord_4034030 prefixEnd_4034030 1380930909771304715181893 := by
  unfold tailWord_4034030
  simp only [CollatzResearch.WordTrace]
  refine ⟨18391645196925717789800443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98088774383603828212269029 18391645196925717789800443)
  ·
    refine ⟨27587467795388576684700665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18391645196925717789800443 27587467795388576684700665)
    ·
      refine ⟨20690600846541432513525499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27587467795388576684700665 20690600846541432513525499)
      ·
        refine ⟨31035901269812148770288249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20690600846541432513525499 31035901269812148770288249)
        ·
          refine ⟨23276925952359111577716187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31035901269812148770288249 23276925952359111577716187)
          ·
            refine ⟨34915388928538667366574281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23276925952359111577716187 34915388928538667366574281)
            ·
              refine ⟨26186541696404000524930711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34915388928538667366574281 26186541696404000524930711)
              ·
                refine ⟨39279812544606000787396067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26186541696404000524930711 39279812544606000787396067)
                ·
                  refine ⟨58919718816909001181094101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39279812544606000787396067 58919718816909001181094101)
                  ·
                    refine ⟨1380930909771304715181893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58919718816909001181094101 1380930909771304715181893)
                    ·
                      rfl

theorem cell22_4034030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_4034030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034030 prefixEnd_4034030 := by exact prefixLift 4034030
  have htrace : WordTrace (prefixWord ++ tailWord_4034030) baseStart_4034030 baseEnd_4034030 := by
    simpa [prefixWord, tailWord_4034030, baseEnd_4034030] using wordTrace_append hprefix tailTrace_4034030
  have hstable : (prefixWord ++ tailWord_4034030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034030).length < 2 ^ (prefixWord ++ tailWord_4034030).sum := by decide
  have hdescent : baseEnd_4034030 < baseStart_4034030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034032 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 5]
def baseStart_4034032 : Nat := 118140960795 + 4034032 * 2 ^ 59
def prefixEnd_4034032 : Nat := 4983230072969 + 3 ^ 40 * 4034032 * 2
def baseEnd_4034032 : Nat := 460310531470725792210629

theorem tailTrace_4034032 : CollatzResearch.WordTrace tailWord_4034032 prefixEnd_4034032 460310531470725792210629 := by
  unfold tailWord_4034032
  simp only [CollatzResearch.WordTrace]
  refine ⟨73566617260699248329988175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98088823014265664439984233 73566617260699248329988175)
  ·
    refine ⟨110349925891048872494982263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73566617260699248329988175 110349925891048872494982263)
    ·
      refine ⟨165524888836573308742473395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110349925891048872494982263 165524888836573308742473395)
      ·
        refine ⟨248287333254859963113710093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165524888836573308742473395 248287333254859963113710093)
        ·
          refine ⟨93107749970572486167641285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248287333254859963113710093 93107749970572486167641285)
          ·
            refine ⟨17457703119482341156432741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93107749970572486167641285 17457703119482341156432741)
            ·
              refine ⟨3273319334902938966831139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17457703119482341156432741 3273319334902938966831139)
              ·
                refine ⟨4909979002354408450246709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273319334902938966831139 4909979002354408450246709)
                ·
                  refine ⟨460310531470725792210629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4909979002354408450246709 460310531470725792210629)
                  ·
                    rfl

theorem cell22_4034032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 5].length) (baseStart_4034032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034032 prefixEnd_4034032 := by exact prefixLift 4034032
  have htrace : WordTrace (prefixWord ++ tailWord_4034032) baseStart_4034032 baseEnd_4034032 := by
    simpa [prefixWord, tailWord_4034032, baseEnd_4034032] using wordTrace_append hprefix tailTrace_4034032
  have hstable : (prefixWord ++ tailWord_4034032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034032).length < 2 ^ (prefixWord ++ tailWord_4034032).sum := by decide
  have hdescent : baseEnd_4034032 < baseStart_4034032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034154 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 3, 3]
def baseStart_4034154 : Nat := 118140960795 + 4034154 * 2 ^ 59
def prefixEnd_4034154 : Nat := 4983230072969 + 3 ^ 40 * 4034154 * 2
def baseEnd_4034154 : Nat := 1380973357505409725081513

theorem tailTrace_4034154 : CollatzResearch.WordTrace tailWord_4034154 prefixEnd_4034154 1380973357505409725081513 := by
  unfold tailWord_4034154
  simp only [CollatzResearch.WordTrace]
  refine ⟨36784421056739127873979379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98091789484637674330611677 36784421056739127873979379)
  ·
    refine ⟨55176631585108691810969069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36784421056739127873979379 55176631585108691810969069)
    ·
      refine ⟨20691236844415759429113401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55176631585108691810969069 20691236844415759429113401)
      ·
        refine ⟨15518427633311819571835051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20691236844415759429113401 15518427633311819571835051)
        ·
          refine ⟨23277641449967729357752577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15518427633311819571835051 23277641449967729357752577)
          ·
            refine ⟨17458231087475797018314433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23277641449967729357752577 17458231087475797018314433)
            ·
              refine ⟨13093673315606847763735825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17458231087475797018314433 13093673315606847763735825)
              ·
                refine ⟨9820254986705135822801869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13093673315606847763735825 9820254986705135822801869)
                ·
                  refine ⟨3682595620014425933550701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9820254986705135822801869 3682595620014425933550701)
                  ·
                    refine ⟨1380973357505409725081513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3682595620014425933550701 1380973357505409725081513)
                    ·
                      rfl

theorem cell22_4034154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_4034154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034154 prefixEnd_4034154 := by exact prefixLift 4034154
  have htrace : WordTrace (prefixWord ++ tailWord_4034154) baseStart_4034154 baseEnd_4034154 := by
    simpa [prefixWord, tailWord_4034154, baseEnd_4034154] using wordTrace_append hprefix tailTrace_4034154
  have hstable : (prefixWord ++ tailWord_4034154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034154).length < 2 ^ (prefixWord ++ tailWord_4034154).sum := by decide
  have hdescent : baseEnd_4034154 < baseStart_4034154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034227 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 1, 5]
def baseStart_4034227 : Nat := 118140960795 + 4034227 * 2 ^ 59
def prefixEnd_4034227 : Nat := 4983230072969 + 3 ^ 40 * 4034227 * 2
def baseEnd_4034227 : Nat := 1380998346897261868006289

theorem tailTrace_4034227 : CollatzResearch.WordTrace tailWord_4034227 prefixEnd_4034227 1380998346897261868006289 := by
  unfold tailWord_4034227
  simp only [CollatzResearch.WordTrace]
  refine ⟨147140346755692044963324935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98093564503794696642216623 147140346755692044963324935)
  ·
    refine ⟨220710520133538067444987403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147140346755692044963324935 220710520133538067444987403)
    ·
      refine ⟨331065780200307101167481105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220710520133538067444987403 331065780200307101167481105)
      ·
        refine ⟨248299335150230325875610829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331065780200307101167481105 248299335150230325875610829)
        ·
          refine ⟨93112250681336372203354061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248299335150230325875610829 93112250681336372203354061)
          ·
            refine ⟨34917094005501139576257773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93112250681336372203354061 34917094005501139576257773)
            ·
              refine ⟨13093910252062927341096665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34917094005501139576257773 13093910252062927341096665)
              ·
                refine ⟨9820432689047195505822499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13093910252062927341096665 9820432689047195505822499)
                ·
                  refine ⟨14730649033570793258733749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9820432689047195505822499 14730649033570793258733749)
                  ·
                    refine ⟨1380998346897261868006289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14730649033570793258733749 1380998346897261868006289)
                    ·
                      rfl

theorem cell22_4034227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 5].length) (baseStart_4034227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034227 prefixEnd_4034227 := by exact prefixLift 4034227
  have htrace : WordTrace (prefixWord ++ tailWord_4034227) baseStart_4034227 baseEnd_4034227 := by
    simpa [prefixWord, tailWord_4034227, baseEnd_4034227] using wordTrace_append hprefix tailTrace_4034227
  have hstable : (prefixWord ++ tailWord_4034227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034227).length < 2 ^ (prefixWord ++ tailWord_4034227).sum := by decide
  have hdescent : baseEnd_4034227 < baseStart_4034227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034231 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 1, 4]
def baseStart_4034231 : Nat := 118140960795 + 4034231 * 2 ^ 59
def prefixEnd_4034231 : Nat := 4983230072969 + 3 ^ 40 * 4034231 * 2
def baseEnd_4034231 : Nat := 1380999716179007190906277

theorem tailTrace_4034231 : CollatzResearch.WordTrace tailWord_4034231 prefixEnd_4034231 1380999716179007190906277 := by
  unfold tailWord_4034231
  simp only [CollatzResearch.WordTrace]
  refine ⟨147140492647677553646470547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98093661765118369097647031 147140492647677553646470547)
  ·
    refine ⟨220710738971516330469705821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147140492647677553646470547 220710738971516330469705821)
    ·
      refine ⟨82766527114318623926139683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220710738971516330469705821 82766527114318623926139683)
      ·
        refine ⟨124149790671477935889209525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82766527114318623926139683 124149790671477935889209525)
        ·
          refine ⟨11639042875451056489613393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124149790671477935889209525 11639042875451056489613393)
          ·
            refine ⟨8729282156588292367210045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11639042875451056489613393 8729282156588292367210045)
            ·
              refine ⟨3273480808720609637703767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8729282156588292367210045 3273480808720609637703767)
              ·
                refine ⟨4910221213080914456555651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273480808720609637703767 4910221213080914456555651)
                ·
                  refine ⟨7365331819621371684833477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910221213080914456555651 7365331819621371684833477)
                  ·
                    refine ⟨1380999716179007190906277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7365331819621371684833477 1380999716179007190906277)
                    ·
                      rfl

theorem cell22_4034231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_4034231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034231 prefixEnd_4034231 := by exact prefixLift 4034231
  have htrace : WordTrace (prefixWord ++ tailWord_4034231) baseStart_4034231 baseEnd_4034231 := by
    simpa [prefixWord, tailWord_4034231, baseEnd_4034231] using wordTrace_append hprefix tailTrace_4034231
  have hstable : (prefixWord ++ tailWord_4034231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034231).length < 2 ^ (prefixWord ++ tailWord_4034231).sum := by decide
  have hdescent : baseEnd_4034231 < baseStart_4034231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034257 : List Nat := [1, 2, 2, 1, 2, 4, 3, 7]
def baseStart_4034257 : Nat := 118140960795 + 4034257 * 2 ^ 59
def prefixEnd_4034257 : Nat := 4983230072969 + 3 ^ 40 * 4034257 * 2
def baseEnd_4034257 : Nat := 153445401834483532195133

theorem tailTrace_4034257 : CollatzResearch.WordTrace tailWord_4034257 prefixEnd_4034257 153445401834483532195133 := by
  unfold tailWord_4034257
  simp only [CollatzResearch.WordTrace]
  refine ⟨147141440945583360086917025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98094293963722240057944683 147141440945583360086917025)
  ·
    refine ⟨110356080709187520065187769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147141440945583360086917025 110356080709187520065187769)
    ·
      refine ⟨82767060531890640048890827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110356080709187520065187769 82767060531890640048890827)
      ·
        refine ⟨124150590797835960073336241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82767060531890640048890827 124150590797835960073336241)
        ·
          refine ⟨93112943098376970055002181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124150590797835960073336241 93112943098376970055002181)
          ·
            refine ⟨17458676830945681885312909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93112943098376970055002181 17458676830945681885312909)
            ·
              refine ⟨6547003811604630706992341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17458676830945681885312909 6547003811604630706992341)
              ·
                refine ⟨153445401834483532195133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6547003811604630706992341 153445401834483532195133)
                ·
                  rfl

theorem cell22_4034257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 7].length) (baseStart_4034257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034257 prefixEnd_4034257 := by exact prefixLift 4034257
  have htrace : WordTrace (prefixWord ++ tailWord_4034257) baseStart_4034257 baseEnd_4034257 := by
    simpa [prefixWord, tailWord_4034257, baseEnd_4034257] using wordTrace_append hprefix tailTrace_4034257
  have hstable : (prefixWord ++ tailWord_4034257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034257).length < 2 ^ (prefixWord ++ tailWord_4034257).sum := by decide
  have hdescent : baseEnd_4034257 < baseStart_4034257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034340 : List Nat := [2, 3, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_4034340 : Nat := 118140960795 + 4034340 * 2 ^ 59
def prefixEnd_4034340 : Nat := 4983230072969 + 3 ^ 40 * 4034340 * 2
def baseEnd_4034340 : Nat := 1381037029106567239930943

theorem tailTrace_4034340 : CollatzResearch.WordTrace tailWord_4034340 prefixEnd_4034340 1381037029106567239930943 := by
  unfold tailWord_4034340
  simp only [CollatzResearch.WordTrace]
  refine ⟨73572234102141332631094237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98096312136188443508125649 73572234102141332631094237)
  ·
    refine ⟨27589587788302999736660339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73572234102141332631094237 27589587788302999736660339)
    ·
      refine ⟨41384381682454499604990509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27589587788302999736660339 41384381682454499604990509)
      ·
        refine ⟨15519143130920437351871441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41384381682454499604990509 15519143130920437351871441)
        ·
          refine ⟨11639357348190328013903581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15519143130920437351871441 11639357348190328013903581)
          ·
            refine ⟨4364759005571373005213843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11639357348190328013903581 4364759005571373005213843)
            ·
              refine ⟨6547138508357059507820765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364759005571373005213843 6547138508357059507820765)
              ·
                refine ⟨2455176940633897315432787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6547138508357059507820765 2455176940633897315432787)
                ·
                  refine ⟨3682765410950845973149181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2455176940633897315432787 3682765410950845973149181)
                  ·
                    refine ⟨1381037029106567239930943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3682765410950845973149181 1381037029106567239930943)
                    ·
                      rfl

theorem cell22_4034340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_4034340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034340 prefixEnd_4034340 := by exact prefixLift 4034340
  have htrace : WordTrace (prefixWord ++ tailWord_4034340) baseStart_4034340 baseEnd_4034340 := by
    simpa [prefixWord, tailWord_4034340, baseEnd_4034340] using wordTrace_append hprefix tailTrace_4034340
  have hstable : (prefixWord ++ tailWord_4034340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034340).length < 2 ^ (prefixWord ++ tailWord_4034340).sum := by decide
  have hdescent : baseEnd_4034340 < baseStart_4034340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034364 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 6]
def baseStart_4034364 : Nat := 118140960795 + 4034364 * 2 ^ 59
def prefixEnd_4034364 : Nat := 4983230072969 + 3 ^ 40 * 4034364 * 2
def baseEnd_4034364 : Nat := 460348414932346392443623

theorem tailTrace_4034364 : CollatzResearch.WordTrace tailWord_4034364 prefixEnd_4034364 460348414932346392443623 := by
  unfold tailWord_4034364
  simp only [CollatzResearch.WordTrace]
  refine ⟨73572671778097858680531073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98096895704130478240708097 73572671778097858680531073)
  ·
    refine ⟨55179503833573394010398305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73572671778097858680531073 55179503833573394010398305)
    ·
      refine ⟨41384627875180045507798729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55179503833573394010398305 41384627875180045507798729)
      ·
        refine ⟨31038470906385034130849047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41384627875180045507798729 31038470906385034130849047)
        ·
          refine ⟨46557706359577551196273571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31038470906385034130849047 46557706359577551196273571)
          ·
            refine ⟨69836559539366326794410357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46557706359577551196273571 69836559539366326794410357)
            ·
              refine ⟨6547177456815593136975971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69836559539366326794410357 6547177456815593136975971)
              ·
                refine ⟨9820766185223389705463957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6547177456815593136975971 9820766185223389705463957)
                ·
                  refine ⟨460348414932346392443623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9820766185223389705463957 460348414932346392443623)
                  ·
                    rfl

theorem cell22_4034364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_4034364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034364 prefixEnd_4034364 := by exact prefixLift 4034364
  have htrace : WordTrace (prefixWord ++ tailWord_4034364) baseStart_4034364 baseEnd_4034364 := by
    simpa [prefixWord, tailWord_4034364, baseEnd_4034364] using wordTrace_append hprefix tailTrace_4034364
  have hstable : (prefixWord ++ tailWord_4034364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034364).length < 2 ^ (prefixWord ++ tailWord_4034364).sum := by decide
  have hdescent : baseEnd_4034364 < baseStart_4034364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034430 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4034430 : Nat := 118140960795 + 4034430 * 2 ^ 59
def prefixEnd_4034430 : Nat := 4983230072969 + 3 ^ 40 * 4034430 * 2
def baseEnd_4034430 : Nat := 1381067837945837005180667

theorem tailTrace_4034430 : CollatzResearch.WordTrace tailWord_4034430 prefixEnd_4034430 1381067837945837005180667 := by
  unfold tailWord_4034430
  simp only [CollatzResearch.WordTrace]
  refine ⟨18393468846744576329120593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98098500515971073755309829 18393468846744576329120593)
  ·
    refine ⟨13795101635058432246840445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18393468846744576329120593 13795101635058432246840445)
    ·
      refine ⟨5173163113146912092565167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13795101635058432246840445 5173163113146912092565167)
      ·
        refine ⟨7759744669720368138847751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173163113146912092565167 7759744669720368138847751)
        ·
          refine ⟨11639617004580552208271627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7759744669720368138847751 11639617004580552208271627)
          ·
            refine ⟨17459425506870828312407441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11639617004580552208271627 17459425506870828312407441)
            ·
              refine ⟨13094569130153121234305581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17459425506870828312407441 13094569130153121234305581)
              ·
                refine ⟨4910463423807420462864593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13094569130153121234305581 4910463423807420462864593)
                ·
                  refine ⟨3682847567855565347148445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910463423807420462864593 3682847567855565347148445)
                  ·
                    refine ⟨1381067837945837005180667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3682847567855565347148445 1381067837945837005180667)
                    ·
                      rfl

theorem cell22_4034430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4034430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034430 prefixEnd_4034430 := by exact prefixLift 4034430
  have htrace : WordTrace (prefixWord ++ tailWord_4034430) baseStart_4034430 baseEnd_4034430 := by
    simpa [prefixWord, tailWord_4034430, baseEnd_4034430] using wordTrace_append hprefix tailTrace_4034430
  have hstable : (prefixWord ++ tailWord_4034430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034430).length < 2 ^ (prefixWord ++ tailWord_4034430).sum := by decide
  have hdescent : baseEnd_4034430 < baseStart_4034430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034441 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 3, 3]
def baseStart_4034441 : Nat := 118140960795 + 4034441 * 2 ^ 59
def prefixEnd_4034441 : Nat := 4983230072969 + 3 ^ 40 * 4034441 * 2
def baseEnd_4034441 : Nat := 1381071603470636643155633

theorem tailTrace_4034441 : CollatzResearch.WordTrace tailWord_4034441 prefixEnd_4034441 1381071603470636643155633 := by
  unfold tailWord_4034441
  simp only [CollatzResearch.WordTrace]
  refine ⟨147148151976916759511615177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98098767984611173007743451 147148151976916759511615177)
  ·
    refine ⟨110361113982687569633711383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147148151976916759511615177 110361113982687569633711383)
    ·
      refine ⟨165541670974031354450567075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110361113982687569633711383 165541670974031354450567075)
      ·
        refine ⟨248312506461047031675850613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165541670974031354450567075 248312506461047031675850613)
        ·
          refine ⟨23279297480723159219610995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 248312506461047031675850613 23279297480723159219610995)
          ·
            refine ⟨34918946221084738829416493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23279297480723159219610995 34918946221084738829416493)
            ·
              refine ⟨13094604832906777061031185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34918946221084738829416493 13094604832906777061031185)
              ·
                refine ⟨9820953624680082795773389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13094604832906777061031185 9820953624680082795773389)
                ·
                  refine ⟨3682857609255031048415021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9820953624680082795773389 3682857609255031048415021)
                  ·
                    refine ⟨1381071603470636643155633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3682857609255031048415021 1381071603470636643155633)
                    ·
                      rfl

theorem cell22_4034441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 3].length) (baseStart_4034441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034441 prefixEnd_4034441 := by exact prefixLift 4034441
  have htrace : WordTrace (prefixWord ++ tailWord_4034441) baseStart_4034441 baseEnd_4034441 := by
    simpa [prefixWord, tailWord_4034441, baseEnd_4034441] using wordTrace_append hprefix tailTrace_4034441
  have hstable : (prefixWord ++ tailWord_4034441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034441).length < 2 ^ (prefixWord ++ tailWord_4034441).sum := by decide
  have hdescent : baseEnd_4034441 < baseStart_4034441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034471 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 7]
def baseStart_4034471 : Nat := 118140960795 + 4034471 * 2 ^ 59
def prefixEnd_4034471 : Nat := 4983230072969 + 3 ^ 40 * 4034471 * 2
def baseEnd_4034471 : Nat := 460360624361242188301847

theorem tailTrace_4034471 : CollatzResearch.WordTrace tailWord_4034471 prefixEnd_4034471 460360624361242188301847 := by
  unfold tailWord_4034471
  simp only [CollatzResearch.WordTrace]
  refine ⟨147149246166808074635207267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98099497444538716423471511 147149246166808074635207267)
  ·
    refine ⟨220723869250212111952810901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147149246166808074635207267 220723869250212111952810901)
    ·
      refine ⟨10346431371103692747788011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 220723869250212111952810901 10346431371103692747788011)
      ·
        refine ⟨15519647056655539121682017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10346431371103692747788011 15519647056655539121682017)
        ·
          refine ⟨11639735292491654341261513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15519647056655539121682017 11639735292491654341261513)
          ·
            refine ⟨8729801469368740755946135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11639735292491654341261513 8729801469368740755946135)
            ·
              refine ⟨13094702204053111133919203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8729801469368740755946135 13094702204053111133919203)
              ·
                refine ⟨19642053306079666700878805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13094702204053111133919203 19642053306079666700878805)
                ·
                  refine ⟨460360624361242188301847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19642053306079666700878805 460360624361242188301847)
                  ·
                    rfl

theorem cell22_4034471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 7].length) (baseStart_4034471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034471 prefixEnd_4034471 := by exact prefixLift 4034471
  have htrace : WordTrace (prefixWord ++ tailWord_4034471) baseStart_4034471 baseEnd_4034471 := by
    simpa [prefixWord, tailWord_4034471, baseEnd_4034471] using wordTrace_append hprefix tailTrace_4034471
  have hstable : (prefixWord ++ tailWord_4034471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034471).length < 2 ^ (prefixWord ++ tailWord_4034471).sum := by decide
  have hdescent : baseEnd_4034471 < baseStart_4034471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034544 : List Nat := [2, 1, 1, 1, 3, 2, 3, 9]
def baseStart_4034544 : Nat := 118140960795 + 4034544 * 2 ^ 59
def prefixEnd_4034544 : Nat := 4983230072969 + 3 ^ 40 * 4034544 * 2
def baseEnd_4034544 : Nat := 153456318052842078647813

theorem tailTrace_4034544 : CollatzResearch.WordTrace tailWord_4034544 prefixEnd_4034544 153456318052842078647813 := by
  unfold tailWord_4034544
  simp only [CollatzResearch.WordTrace]
  refine ⟨73575954347771804051307343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98101272463695738735076457 73575954347771804051307343)
  ·
    refine ⟨110363931521657706076961015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73575954347771804051307343 110363931521657706076961015)
    ·
      refine ⟨165545897282486559115441523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110363931521657706076961015 165545897282486559115441523)
      ·
        refine ⟨248318845923729838673162285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165545897282486559115441523 248318845923729838673162285)
        ·
          refine ⟨93119567221398689502435857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248318845923729838673162285 93119567221398689502435857)
          ·
            refine ⟨69839675416049017126826893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93119567221398689502435857 69839675416049017126826893)
            ·
              refine ⟨26189878281018381422560085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69839675416049017126826893 26189878281018381422560085)
              ·
                refine ⟨153456318052842078647813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26189878281018381422560085 153456318052842078647813)
                ·
                  rfl

theorem cell22_4034544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 9].length) (baseStart_4034544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034544 prefixEnd_4034544 := by exact prefixLift 4034544
  have htrace : WordTrace (prefixWord ++ tailWord_4034544) baseStart_4034544 baseEnd_4034544 := by
    simpa [prefixWord, tailWord_4034544, baseEnd_4034544] using wordTrace_append hprefix tailTrace_4034544
  have hstable : (prefixWord ++ tailWord_4034544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034544).length < 2 ^ (prefixWord ++ tailWord_4034544).sum := by decide
  have hdescent : baseEnd_4034544 < baseStart_4034544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034559 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 2, 7]
def baseStart_4034559 : Nat := 118140960795 + 4034559 * 2 ^ 59
def prefixEnd_4034559 : Nat := 4983230072969 + 3 ^ 40 * 4034559 * 2
def baseEnd_4034559 : Nat := 1381111997282123668705271

theorem tailTrace_4034559 : CollatzResearch.WordTrace tailWord_4034559 prefixEnd_4034559 1381111997282123668705271 := by
  unfold tailWord_4034559
  simp only [CollatzResearch.WordTrace]
  refine ⟨147152455790489265664410731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98101637193659510442940487 147152455790489265664410731)
  ·
    refine ⟨220728683685733898496616097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147152455790489265664410731 220728683685733898496616097)
    ·
      refine ⟨165546512764300423872462073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220728683685733898496616097 165546512764300423872462073)
      ·
        refine ⟨124159884573225317904346555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165546512764300423872462073 124159884573225317904346555)
        ·
          refine ⟨186239826859837976856519833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124159884573225317904346555 186239826859837976856519833)
          ·
            refine ⟨139679870144878482642389875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186239826859837976856519833 139679870144878482642389875)
            ·
              refine ⟨209519805217317723963584813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139679870144878482642389875 209519805217317723963584813)
              ·
                refine ⟨78569926956494146486344305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209519805217317723963584813 78569926956494146486344305)
                ·
                  refine ⟨58927445217370609864758229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78569926956494146486344305 58927445217370609864758229)
                  ·
                    refine ⟨1381111997282123668705271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58927445217370609864758229 1381111997282123668705271)
                    ·
                      rfl

theorem cell22_4034559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_4034559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034559 prefixEnd_4034559 := by exact prefixLift 4034559
  have htrace : WordTrace (prefixWord ++ tailWord_4034559) baseStart_4034559 baseEnd_4034559 := by
    simpa [prefixWord, tailWord_4034559, baseEnd_4034559] using wordTrace_append hprefix tailTrace_4034559
  have hstable : (prefixWord ++ tailWord_4034559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034559).length < 2 ^ (prefixWord ++ tailWord_4034559).sum := by decide
  have hdescent : baseEnd_4034559 < baseStart_4034559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034576 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 5, 3]
def baseStart_4034576 : Nat := 118140960795 + 4034576 * 2 ^ 59
def prefixEnd_4034576 : Nat := 4983230072969 + 3 ^ 40 * 4034576 * 2
def baseEnd_4034576 : Nat := 1381117816729541291030219

theorem tailTrace_4034576 : CollatzResearch.WordTrace tailWord_4034576 prefixEnd_4034576 1381117816729541291030219 := by
  unfold tailWord_4034576
  simp only [CollatzResearch.WordTrace]
  refine ⟨73576537915713838783889791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98102050554285118378519721 73576537915713838783889791)
  ·
    refine ⟨110364806873570758175834687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73576537915713838783889791 110364806873570758175834687)
    ·
      refine ⟨165547210310356137263752031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110364806873570758175834687 165547210310356137263752031)
      ·
        refine ⟨248320815465534205895628047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165547210310356137263752031 248320815465534205895628047)
        ·
          refine ⟨372481223198301308843442071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248320815465534205895628047 372481223198301308843442071)
          ·
            refine ⟨558721834797451963265163107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372481223198301308843442071 558721834797451963265163107)
            ·
              refine ⟨838082752196177944897744661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558721834797451963265163107 838082752196177944897744661)
              ·
                refine ⟨39285129009195841167081781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 838082752196177944897744661 39285129009195841167081781)
                ·
                  refine ⟨3682980844612110109413917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39285129009195841167081781 3682980844612110109413917)
                  ·
                    refine ⟨1381117816729541291030219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3682980844612110109413917 1381117816729541291030219)
                    ·
                      rfl

theorem cell22_4034576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5, 3].length) (baseStart_4034576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034576 prefixEnd_4034576 := by exact prefixLift 4034576
  have htrace : WordTrace (prefixWord ++ tailWord_4034576) baseStart_4034576 baseEnd_4034576 := by
    simpa [prefixWord, tailWord_4034576, baseEnd_4034576] using wordTrace_append hprefix tailTrace_4034576
  have hstable : (prefixWord ++ tailWord_4034576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034576).length < 2 ^ (prefixWord ++ tailWord_4034576).sum := by decide
  have hdescent : baseEnd_4034576 < baseStart_4034576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034621 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_4034621 : Nat := 118140960795 + 4034621 * 2 ^ 59
def prefixEnd_4034621 : Nat := 4983230072969 + 3 ^ 40 * 4034621 * 2
def baseEnd_4034621 : Nat := 1381133221149176173655081

theorem tailTrace_4034621 : CollatzResearch.WordTrace tailWord_4034621 prefixEnd_4034621 1381133221149176173655081 := by
  unfold tailWord_4034621
  simp only [CollatzResearch.WordTrace]
  refine ⟨147154717116264650253167717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98103144744176433502111811 147154717116264650253167717)
  ·
    refine ⟨27591509459299621922468947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147154717116264650253167717 27591509459299621922468947)
    ·
      refine ⟨41387264188949432883703421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27591509459299621922468947 41387264188949432883703421)
      ·
        refine ⟨15520224070856037331388783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41387264188949432883703421 15520224070856037331388783)
        ·
          refine ⟨23280336106284055997083175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15520224070856037331388783 23280336106284055997083175)
          ·
            refine ⟨34920504159426083995624763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23280336106284055997083175 34920504159426083995624763)
            ·
              refine ⟨52380756239139125993437145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34920504159426083995624763 52380756239139125993437145)
              ·
                refine ⟨39285567179354344495077859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52380756239139125993437145 39285567179354344495077859)
                ·
                  refine ⟨58928350769031516742616789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39285567179354344495077859 58928350769031516742616789)
                  ·
                    refine ⟨1381133221149176173655081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58928350769031516742616789 1381133221149176173655081)
                    ·
                      rfl

theorem cell22_4034621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_4034621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034621 prefixEnd_4034621 := by exact prefixLift 4034621
  have htrace : WordTrace (prefixWord ++ tailWord_4034621) baseStart_4034621 baseEnd_4034621 := by
    simpa [prefixWord, tailWord_4034621, baseEnd_4034621] using wordTrace_append hprefix tailTrace_4034621
  have hstable : (prefixWord ++ tailWord_4034621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034621).length < 2 ^ (prefixWord ++ tailWord_4034621).sum := by decide
  have hdescent : baseEnd_4034621 < baseStart_4034621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034670 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_4034670 : Nat := 118140960795 + 4034670 * 2 ^ 59
def prefixEnd_4034670 : Nat := 4983230072969 + 3 ^ 40 * 4034670 * 2
def baseEnd_4034670 : Nat := 1381149994850556379179931

theorem tailTrace_4034670 : CollatzResearch.WordTrace tailWord_4034670 prefixEnd_4034670 1381149994850556379179931 := by
  unfold tailWord_4034670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18394563036635891452712683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98104336195391421081134309 18394563036635891452712683)
  ·
    refine ⟨27591844554953837179069025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18394563036635891452712683 27591844554953837179069025)
    ·
      refine ⟨20693883416215377884301769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27591844554953837179069025 20693883416215377884301769)
      ·
        refine ⟨15520412562161533413226327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20693883416215377884301769 15520412562161533413226327)
        ·
          refine ⟨23280618843242300119839491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15520412562161533413226327 23280618843242300119839491)
          ·
            refine ⟨34920928264863450179759237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23280618843242300119839491 34920928264863450179759237)
            ·
              refine ⟨6547674049661896908704857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34920928264863450179759237 6547674049661896908704857)
              ·
                refine ⟨4910755537246422681528643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6547674049661896908704857 4910755537246422681528643)
                ·
                  refine ⟨7366133305869634022292965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910755537246422681528643 7366133305869634022292965)
                  ·
                    refine ⟨1381149994850556379179931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7366133305869634022292965 1381149994850556379179931)
                    ·
                      rfl

theorem cell22_4034670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_4034670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034670 prefixEnd_4034670 := by exact prefixLift 4034670
  have htrace : WordTrace (prefixWord ++ tailWord_4034670) baseStart_4034670 baseEnd_4034670 := by
    simpa [prefixWord, tailWord_4034670, baseEnd_4034670] using wordTrace_append hprefix tailTrace_4034670
  have hstable : (prefixWord ++ tailWord_4034670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034670).length < 2 ^ (prefixWord ++ tailWord_4034670).sum := by decide
  have hdescent : baseEnd_4034670 < baseStart_4034670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034685 : List Nat := [1, 4, 1, 1, 3, 2, 3, 3, 4]
def baseStart_4034685 : Nat := 118140960795 + 4034685 * 2 ^ 59
def prefixEnd_4034685 : Nat := 4983230072969 + 3 ^ 40 * 4034685 * 2
def baseEnd_4034685 : Nat := 460385043219033780018295

theorem tailTrace_4034685 : CollatzResearch.WordTrace tailWord_4034685 prefixEnd_4034685 460385043219033780018295 := by
  unfold tailWord_4034685
  simp only [CollatzResearch.WordTrace]
  refine ⟨147157051388032789183497509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98104700925355192788998339 147157051388032789183497509)
  ·
    refine ⟨27591947135256147971905783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147157051388032789183497509 27591947135256147971905783)
    ·
      refine ⟨41387920702884221957858675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27591947135256147971905783 41387920702884221957858675)
      ·
        refine ⟨62081881054326332936788013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41387920702884221957858675 62081881054326332936788013)
        ·
          refine ⟨23280705395372374851295505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62081881054326332936788013 23280705395372374851295505)
          ·
            refine ⟨17460529046529281138471629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23280705395372374851295505 17460529046529281138471629)
            ·
              refine ⟨6547698392448480426926861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17460529046529281138471629 6547698392448480426926861)
              ·
                refine ⟨2455386897168180160097573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6547698392448480426926861 2455386897168180160097573)
                ·
                  refine ⟨460385043219033780018295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2455386897168180160097573 460385043219033780018295)
                  ·
                    rfl

theorem cell22_4034685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_4034685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034685 prefixEnd_4034685 := by exact prefixLift 4034685
  have htrace : WordTrace (prefixWord ++ tailWord_4034685) baseStart_4034685 baseEnd_4034685 := by
    simpa [prefixWord, tailWord_4034685, baseEnd_4034685] using wordTrace_append hprefix tailTrace_4034685
  have hstable : (prefixWord ++ tailWord_4034685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034685).length < 2 ^ (prefixWord ++ tailWord_4034685).sum := by decide
  have hdescent : baseEnd_4034685 < baseStart_4034685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034698 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_4034698 : Nat := 118140960795 + 4034698 * 2 ^ 59
def prefixEnd_4034698 : Nat := 4983230072969 + 3 ^ 40 * 4034698 * 2
def baseEnd_4034698 : Nat := 1381159579822773639479845

theorem tailTrace_4034698 : CollatzResearch.WordTrace tailWord_4034698 prefixEnd_4034698 1381159579822773639479845 := by
  unfold tailWord_4034698
  simp only [CollatzResearch.WordTrace]
  refine ⟨36789381384246423100930187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98105017024657128269147165 36789381384246423100930187)
  ·
    refine ⟨55184072076369634651395281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36789381384246423100930187 55184072076369634651395281)
    ·
      refine ⟨41388054057277225988546461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55184072076369634651395281 41388054057277225988546461)
      ·
        refine ⟨15520520271478959745704923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41388054057277225988546461 15520520271478959745704923)
        ·
          refine ⟨23280780407218439618557385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15520520271478959745704923 23280780407218439618557385)
          ·
            refine ⟨17460585305413829713918039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23280780407218439618557385 17460585305413829713918039)
            ·
              refine ⟨26190877958120744570877059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17460585305413829713918039 26190877958120744570877059)
              ·
                refine ⟨39286316937181116856315589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26190877958120744570877059 39286316937181116856315589)
                ·
                  refine ⟨7366184425721459410559173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39286316937181116856315589 7366184425721459410559173)
                  ·
                    refine ⟨1381159579822773639479845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7366184425721459410559173 1381159579822773639479845)
                    ·
                      rfl

theorem cell22_4034698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_4034698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034698 prefixEnd_4034698 := by exact prefixLift 4034698
  have htrace : WordTrace (prefixWord ++ tailWord_4034698) baseStart_4034698 baseEnd_4034698 := by
    simpa [prefixWord, tailWord_4034698, baseEnd_4034698] using wordTrace_append hprefix tailTrace_4034698
  have hstable : (prefixWord ++ tailWord_4034698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034698).length < 2 ^ (prefixWord ++ tailWord_4034698).sum := by decide
  have hdescent : baseEnd_4034698 < baseStart_4034698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034702 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_4034702 : Nat := 118140960795 + 4034702 * 2 ^ 59
def prefixEnd_4034702 : Nat := 4983230072969 + 3 ^ 40 * 4034702 * 2
def baseEnd_4034702 : Nat := 460386983034839654126611

theorem tailTrace_4034702 : CollatzResearch.WordTrace tailWord_4034702 prefixEnd_4034702 460386983034839654126611 := by
  unfold tailWord_4034702
  simp only [CollatzResearch.WordTrace]
  refine ⟨18394708928621400135858295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98105114285980800724577573 18394708928621400135858295)
  ·
    refine ⟨27592063392932100203787443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18394708928621400135858295 27592063392932100203787443)
    ·
      refine ⟨41388095089398150305681165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27592063392932100203787443 41388095089398150305681165)
      ·
        refine ⟨15520535658524306364630437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41388095089398150305681165 15520535658524306364630437)
        ·
          refine ⟨2910100435973307443368207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15520535658524306364630437 2910100435973307443368207)
          ·
            refine ⟨4365150653959961165052311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910100435973307443368207 4365150653959961165052311)
            ·
              refine ⟨6547725980939941747578467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365150653959961165052311 6547725980939941747578467)
              ·
                refine ⟨9821588971409912621367701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6547725980939941747578467 9821588971409912621367701)
                ·
                  refine ⟨460386983034839654126611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9821588971409912621367701 460386983034839654126611)
                  ·
                    rfl

theorem cell22_4034702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_4034702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034702 prefixEnd_4034702 := by exact prefixLift 4034702
  have htrace : WordTrace (prefixWord ++ tailWord_4034702) baseStart_4034702 baseEnd_4034702 := by
    simpa [prefixWord, tailWord_4034702, baseEnd_4034702] using wordTrace_append hprefix tailTrace_4034702
  have hstable : (prefixWord ++ tailWord_4034702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034702).length < 2 ^ (prefixWord ++ tailWord_4034702).sum := by decide
  have hdescent : baseEnd_4034702 < baseStart_4034702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034717 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_4034717 : Nat := 118140960795 + 4034717 * 2 ^ 59
def prefixEnd_4034717 : Nat := 4983230072969 + 3 ^ 40 * 4034717 * 2
def baseEnd_4034717 : Nat := 1381166083911063923254787

theorem tailTrace_4034717 : CollatzResearch.WordTrace tailWord_4034717 prefixEnd_4034717 1381166083911063923254787 := by
  unfold tailWord_4034717
  simp only [CollatzResearch.WordTrace]
  refine ⟨147158218523916858648662405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98105479015944572432441603 147158218523916858648662405)
  ·
    refine ⟨27592165973234410996624201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147158218523916858648662405 27592165973234410996624201)
    ·
      refine ⟨20694124479925808247468151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27592165973234410996624201 20694124479925808247468151)
      ·
        refine ⟨31041186719888712371202227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20694124479925808247468151 31041186719888712371202227)
        ·
          refine ⟨46561780079833068556803341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31041186719888712371202227 46561780079833068556803341)
          ·
            refine ⟨17460667529937400708801253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46561780079833068556803341 17460667529937400708801253)
            ·
              refine ⟨3273875161863262632900235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17460667529937400708801253 3273875161863262632900235)
              ·
                refine ⟨4910812742794893949350353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273875161863262632900235 4910812742794893949350353)
                ·
                  refine ⟨3683109557096170462012765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910812742794893949350353 3683109557096170462012765)
                  ·
                    refine ⟨1381166083911063923254787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683109557096170462012765 1381166083911063923254787)
                    ·
                      rfl

theorem cell22_4034717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_4034717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034717 prefixEnd_4034717 := by exact prefixLift 4034717
  have htrace : WordTrace (prefixWord ++ tailWord_4034717) baseStart_4034717 baseEnd_4034717 := by
    simpa [prefixWord, tailWord_4034717, baseEnd_4034717] using wordTrace_append hprefix tailTrace_4034717
  have hstable : (prefixWord ++ tailWord_4034717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034717).length < 2 ^ (prefixWord ++ tailWord_4034717).sum := by decide
  have hdescent : baseEnd_4034717 < baseStart_4034717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034762 : List Nat := [3, 1, 2, 1, 3, 1, 3, 4, 1, 3]
def baseStart_4034762 : Nat := 118140960795 + 4034762 * 2 ^ 59
def prefixEnd_4034762 : Nat := 4983230072969 + 3 ^ 40 * 4034762 * 2
def baseEnd_4034762 : Nat := 1381181488330698805879649

theorem tailTrace_4034762 : CollatzResearch.WordTrace tailWord_4034762 prefixEnd_4034762 1381181488330698805879649 := by
  unfold tailWord_4034762
  simp only [CollatzResearch.WordTrace]
  refine ⟨36789964952188457833512635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98106573205835887556033693 36789964952188457833512635)
  ·
    refine ⟨55184947428282686750268953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36789964952188457833512635 55184947428282686750268953)
    ·
      refine ⟨41388710571212015062701715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55184947428282686750268953 41388710571212015062701715)
      ·
        refine ⟨62083065856818022594052573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41388710571212015062701715 62083065856818022594052573)
        ·
          refine ⟨23281149696306758472769715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62083065856818022594052573 23281149696306758472769715)
          ·
            refine ⟨34921724544460137709154573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23281149696306758472769715 34921724544460137709154573)
            ·
              refine ⟨13095646704172551640932965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34921724544460137709154573 13095646704172551640932965)
              ·
                refine ⟨2455433757032353432674931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13095646704172551640932965 2455433757032353432674931)
                ·
                  refine ⟨3683150635548530149012397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2455433757032353432674931 3683150635548530149012397)
                  ·
                    refine ⟨1381181488330698805879649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683150635548530149012397 1381181488330698805879649)
                    ·
                      rfl

theorem cell22_4034762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_4034762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034762 prefixEnd_4034762 := by exact prefixLift 4034762
  have htrace : WordTrace (prefixWord ++ tailWord_4034762) baseStart_4034762 baseEnd_4034762 := by
    simpa [prefixWord, tailWord_4034762, baseEnd_4034762] using wordTrace_append hprefix tailTrace_4034762
  have hstable : (prefixWord ++ tailWord_4034762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034762).length < 2 ^ (prefixWord ++ tailWord_4034762).sum := by decide
  have hdescent : baseEnd_4034762 < baseStart_4034762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034771 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 1, 10]
def baseStart_4034771 : Nat := 118140960795 + 4034771 * 2 ^ 59
def prefixEnd_4034771 : Nat := 4983230072969 + 3 ^ 40 * 4034771 * 2
def baseEnd_4034771 : Nat := 1381184569214625782404621

theorem tailTrace_4034771 : CollatzResearch.WordTrace tailWord_4034771 prefixEnd_4034771 1381184569214625782404621 := by
  unfold tailWord_4034771
  simp only [CollatzResearch.WordTrace]
  refine ⟨147160188065721225871128167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98106792043814150580752111 147160188065721225871128167)
  ·
    refine ⟨220740282098581838806692251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147160188065721225871128167 220740282098581838806692251)
    ·
      refine ⟨331110423147872758210038377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220740282098581838806692251 331110423147872758210038377)
      ·
        refine ⟨248332817360904568657528783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331110423147872758210038377 248332817360904568657528783)
        ·
          refine ⟨372499226041356852986293175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248332817360904568657528783 372499226041356852986293175)
          ·
            refine ⟨558748839062035279479439763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372499226041356852986293175 558748839062035279479439763)
            ·
              refine ⟨838123258593052919219159645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558748839062035279479439763 838123258593052919219159645)
              ·
                refine ⟨314296221972394844707184867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 838123258593052919219159645 314296221972394844707184867)
                ·
                  refine ⟨471444332958592267060777301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314296221972394844707184867 471444332958592267060777301)
                  ·
                    refine ⟨1381184569214625782404621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 471444332958592267060777301 1381184569214625782404621)
                    ·
                      rfl

theorem cell22_4034771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_4034771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034771 prefixEnd_4034771 := by exact prefixLift 4034771
  have htrace : WordTrace (prefixWord ++ tailWord_4034771) baseStart_4034771 baseEnd_4034771 := by
    simpa [prefixWord, tailWord_4034771, baseEnd_4034771] using wordTrace_append hprefix tailTrace_4034771
  have hstable : (prefixWord ++ tailWord_4034771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034771).length < 2 ^ (prefixWord ++ tailWord_4034771).sum := by decide
  have hdescent : baseEnd_4034771 < baseStart_4034771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034833 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_4034833 : Nat := 118140960795 + 4034833 * 2 ^ 59
def prefixEnd_4034833 : Nat := 4983230072969 + 3 ^ 40 * 4034833 * 2
def baseEnd_4034833 : Nat := 1381205793081678287354431

theorem tailTrace_4034833 : CollatzResearch.WordTrace tailWord_4034833 prefixEnd_4034833 1381205793081678287354431 := by
  unfold tailWord_4034833
  simp only [CollatzResearch.WordTrace]
  refine ⟨147162449391496610459885153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98108299594331073639923435 147162449391496610459885153)
  ·
    refine ⟨110371837043622457844913865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147162449391496610459885153 110371837043622457844913865)
    ·
      refine ⟨82778877782716843383685399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110371837043622457844913865 82778877782716843383685399)
      ·
        refine ⟨124168316674075265075528099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82778877782716843383685399 124168316674075265075528099)
        ·
          refine ⟨186252475011112897613292149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124168316674075265075528099 186252475011112897613292149)
          ·
            refine ⟨17461169532291834151246139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186252475011112897613292149 17461169532291834151246139)
            ·
              refine ⟨26191754298437751226869209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17461169532291834151246139 26191754298437751226869209)
              ·
                refine ⟨19643815723828313420151907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26191754298437751226869209 19643815723828313420151907)
                ·
                  refine ⟨29465723585742470130227861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19643815723828313420151907 29465723585742470130227861)
                  ·
                    refine ⟨1381205793081678287354431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29465723585742470130227861 1381205793081678287354431)
                    ·
                      rfl

theorem cell22_4034833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_4034833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034833 prefixEnd_4034833 := by exact prefixLift 4034833
  have htrace : WordTrace (prefixWord ++ tailWord_4034833) baseStart_4034833 baseEnd_4034833 := by
    simpa [prefixWord, tailWord_4034833, baseEnd_4034833] using wordTrace_append hprefix tailTrace_4034833
  have hstable : (prefixWord ++ tailWord_4034833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034833).length < 2 ^ (prefixWord ++ tailWord_4034833).sum := by decide
  have hdescent : baseEnd_4034833 < baseStart_4034833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034835 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 2, 3]
def baseStart_4034835 : Nat := 118140960795 + 4034835 * 2 ^ 59
def prefixEnd_4034835 : Nat := 4983230072969 + 3 ^ 40 * 4034835 * 2
def baseEnd_4034835 : Nat := 1381206477722550948804425

theorem tailTrace_4034835 : CollatzResearch.WordTrace tailWord_4034835 prefixEnd_4034835 1381206477722550948804425 := by
  unfold tailWord_4034835
  simp only [CollatzResearch.WordTrace]
  refine ⟨147162522337489364801457959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98108348224992909867638639 147162522337489364801457959)
  ·
    refine ⟨220743783506234047202186939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147162522337489364801457959 220743783506234047202186939)
    ·
      refine ⟨331115675259351070803280409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220743783506234047202186939 331115675259351070803280409)
      ·
        refine ⟨248336756444513303102460307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331115675259351070803280409 248336756444513303102460307)
        ·
          refine ⟨372505134666769954653690461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248336756444513303102460307 372505134666769954653690461)
          ·
            refine ⟨139689425500038732995133923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372505134666769954653690461 139689425500038732995133923)
            ·
              refine ⟨209534138250058099492700885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139689425500038732995133923 209534138250058099492700885)
              ·
                refine ⟨4910956365235736706860177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 209534138250058099492700885 4910956365235736706860177)
                ·
                  refine ⟨3683217273926802530145133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910956365235736706860177 3683217273926802530145133)
                  ·
                    refine ⟨1381206477722550948804425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683217273926802530145133 1381206477722550948804425)
                    ·
                      rfl

theorem cell22_4034835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 3].length) (baseStart_4034835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034835 prefixEnd_4034835 := by exact prefixLift 4034835
  have htrace : WordTrace (prefixWord ++ tailWord_4034835) baseStart_4034835 baseEnd_4034835 := by
    simpa [prefixWord, tailWord_4034835, baseEnd_4034835] using wordTrace_append hprefix tailTrace_4034835
  have hstable : (prefixWord ++ tailWord_4034835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034835).length < 2 ^ (prefixWord ++ tailWord_4034835).sum := by decide
  have hdescent : baseEnd_4034835 < baseStart_4034835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034850 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_4034850 : Nat := 118140960795 + 4034850 * 2 ^ 59
def prefixEnd_4034850 : Nat := 4983230072969 + 3 ^ 40 * 4034850 * 2
def baseEnd_4034850 : Nat := 1381211612529095909679379

theorem tailTrace_4034850 : CollatzResearch.WordTrace tailWord_4034850 prefixEnd_4034850 1381211612529095909679379 := by
  unfold tailWord_4034850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36790767358108755590813501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98108712954956681575502669 36790767358108755590813501)
  ·
    refine ⟨13796537759290783346555063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36790767358108755590813501 13796537759290783346555063)
    ·
      refine ⟨20694806638936175019832595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13796537759290783346555063 20694806638936175019832595)
      ·
        refine ⟨31042209958404262529748893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20694806638936175019832595 31042209958404262529748893)
        ·
          refine ⟨11640828734401598448655835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31042209958404262529748893 11640828734401598448655835)
          ·
            refine ⟨17461243101602397672983753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11640828734401598448655835 17461243101602397672983753)
            ·
              refine ⟨13095932326201798254737815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17461243101602397672983753 13095932326201798254737815)
              ·
                refine ⟨19643898489302697382106723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13095932326201798254737815 19643898489302697382106723)
                ·
                  refine ⟨29465847733954046073160085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19643898489302697382106723 29465847733954046073160085)
                  ·
                    refine ⟨1381211612529095909679379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29465847733954046073160085 1381211612529095909679379)
                    ·
                      rfl

theorem cell22_4034850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_4034850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034850 prefixEnd_4034850 := by exact prefixLift 4034850
  have htrace : WordTrace (prefixWord ++ tailWord_4034850) baseStart_4034850 baseEnd_4034850 := by
    simpa [prefixWord, tailWord_4034850, baseEnd_4034850] using wordTrace_append hprefix tailTrace_4034850
  have hstable : (prefixWord ++ tailWord_4034850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034850).length < 2 ^ (prefixWord ++ tailWord_4034850).sum := by decide
  have hdescent : baseEnd_4034850 < baseStart_4034850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034865 : List Nat := [1, 2, 2, 3, 4, 2, 8]
def baseStart_4034865 : Nat := 118140960795 + 4034865 * 2 ^ 59
def prefixEnd_4034865 : Nat := 4983230072969 + 3 ^ 40 * 4034865 * 2
def baseEnd_4034865 : Nat := 51156175827245958168679

theorem tailTrace_4034865 : CollatzResearch.WordTrace tailWord_4034865 prefixEnd_4034865 51156175827245958168679 := by
  unfold tailWord_4034865
  simp only [CollatzResearch.WordTrace]
  refine ⟨147163616527380679925050049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98109077684920453283366699 147163616527380679925050049)
  ·
    refine ⟨110372712395535509943787537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147163616527380679925050049 110372712395535509943787537)
    ·
      refine ⟨82779534296651632457840653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110372712395535509943787537 82779534296651632457840653)
      ·
        refine ⟨31042325361244362171690245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82779534296651632457840653 31042325361244362171690245)
        ·
          refine ⟨5820436005233317907191921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31042325361244362171690245 5820436005233317907191921)
          ·
            refine ⟨4365327003924988430393941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5820436005233317907191921 4365327003924988430393941)
            ·
              refine ⟨51156175827245958168679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4365327003924988430393941 51156175827245958168679)
              ·
                rfl

theorem cell22_4034865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 8].length) (baseStart_4034865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034865 prefixEnd_4034865 := by exact prefixLift 4034865
  have htrace : WordTrace (prefixWord ++ tailWord_4034865) baseStart_4034865 baseEnd_4034865 := by
    simpa [prefixWord, tailWord_4034865, baseEnd_4034865] using wordTrace_append hprefix tailTrace_4034865
  have hstable : (prefixWord ++ tailWord_4034865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034865).length < 2 ^ (prefixWord ++ tailWord_4034865).sum := by decide
  have hdescent : baseEnd_4034865 < baseStart_4034865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034880 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 3, 3]
def baseStart_4034880 : Nat := 118140960795 + 4034880 * 2 ^ 59
def prefixEnd_4034880 : Nat := 4983230072969 + 3 ^ 40 * 4034880 * 2
def baseEnd_4034880 : Nat := 1381221882142185831429287

theorem tailTrace_4034880 : CollatzResearch.WordTrace tailWord_4034880 prefixEnd_4034880 1381221882142185831429287 := by
  unfold tailWord_4034880
  simp only [CollatzResearch.WordTrace]
  refine ⟨73582081811163168743423047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98109442414884224991230729 73582081811163168743423047)
  ·
    refine ⟨110373122716744753115134571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73582081811163168743423047 110373122716744753115134571)
    ·
      refine ⟨165559684075117129672701857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110373122716744753115134571 165559684075117129672701857)
      ·
        refine ⟨124169763056337847254526393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165559684075117129672701857 124169763056337847254526393)
        ·
          refine ⟨93127322292253385440894795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124169763056337847254526393 93127322292253385440894795)
          ·
            refine ⟨139690983438380078161342193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93127322292253385440894795 139690983438380078161342193)
            ·
              refine ⟨104768237578785058621006645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139690983438380078161342193 104768237578785058621006645)
              ·
                refine ⟨9822022273011099245719373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104768237578785058621006645 9822022273011099245719373)
                ·
                  refine ⟨3683258352379162217144765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9822022273011099245719373 3683258352379162217144765)
                  ·
                    refine ⟨1381221882142185831429287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683258352379162217144765 1381221882142185831429287)
                    ·
                      rfl

theorem cell22_4034880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3, 3].length) (baseStart_4034880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034880 prefixEnd_4034880 := by exact prefixLift 4034880
  have htrace : WordTrace (prefixWord ++ tailWord_4034880) baseStart_4034880 baseEnd_4034880 := by
    simpa [prefixWord, tailWord_4034880, baseEnd_4034880] using wordTrace_append hprefix tailTrace_4034880
  have hstable : (prefixWord ++ tailWord_4034880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034880).length < 2 ^ (prefixWord ++ tailWord_4034880).sum := by decide
  have hdescent : baseEnd_4034880 < baseStart_4034880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034925 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_4034925 : Nat := 118140960795 + 4034925 * 2 ^ 59
def prefixEnd_4034925 : Nat := 4983230072969 + 3 ^ 40 * 4034925 * 2
def baseEnd_4034925 : Nat := 1381237286561820714054149

theorem tailTrace_4034925 : CollatzResearch.WordTrace tailWord_4034925 prefixEnd_4034925 1381237286561820714054149 := by
  unfold tailWord_4034925
  simp only [CollatzResearch.WordTrace]
  refine ⟨147165804907163310172234229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98110536604775540114822819 147165804907163310172234229)
  ·
    refine ⟨13796794210046560328646959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147165804907163310172234229 13796794210046560328646959)
    ·
      refine ⟨20695191315069840492970439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13796794210046560328646959 20695191315069840492970439)
      ·
        refine ⟨31042786972604760739455659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20695191315069840492970439 31042786972604760739455659)
        ·
          refine ⟨46564180458907141109183489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31042786972604760739455659 46564180458907141109183489)
          ·
            refine ⟨34923135344180355831887617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46564180458907141109183489 34923135344180355831887617)
            ·
              refine ⟨26192351508135266873915713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34923135344180355831887617 26192351508135266873915713)
              ·
                refine ⟨19644263631101450155436785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26192351508135266873915713 19644263631101450155436785)
                ·
                  refine ⟨14733197723326087616577589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19644263631101450155436785 14733197723326087616577589)
                  ·
                    refine ⟨1381237286561820714054149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14733197723326087616577589 1381237286561820714054149)
                    ·
                      rfl

theorem cell22_4034925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_4034925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034925 prefixEnd_4034925 := by exact prefixLift 4034925
  have htrace : WordTrace (prefixWord ++ tailWord_4034925) baseStart_4034925 baseEnd_4034925 := by
    simpa [prefixWord, tailWord_4034925, baseEnd_4034925] using wordTrace_append hprefix tailTrace_4034925
  have hstable : (prefixWord ++ tailWord_4034925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034925).length < 2 ^ (prefixWord ++ tailWord_4034925).sum := by decide
  have hdescent : baseEnd_4034925 < baseStart_4034925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034955 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 6]
def baseStart_4034955 : Nat := 118140960795 + 4034955 * 2 ^ 59
def prefixEnd_4034955 : Nat := 4983230072969 + 3 ^ 40 * 4034955 * 2
def baseEnd_4034955 : Nat := 460415852058303545268019

theorem tailTrace_4034955 : CollatzResearch.WordTrace tailWord_4034955 prefixEnd_4034955 460415852058303545268019 := by
  unfold tailWord_4034955
  simp only [CollatzResearch.WordTrace]
  refine ⟨147166899097054625295826319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98111266064703083530550879 147166899097054625295826319)
  ·
    refine ⟨220750348645581937943739479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147166899097054625295826319 220750348645581937943739479)
    ·
      refine ⟨331125522968372906915609219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220750348645581937943739479 331125522968372906915609219)
      ·
        refine ⟨496688284452559360373413829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331125522968372906915609219 496688284452559360373413829)
        ·
          refine ⟨93129053334854880070015093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 496688284452559360373413829 93129053334854880070015093)
          ·
            refine ⟨8730848750142645006563915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93129053334854880070015093 8730848750142645006563915)
            ·
              refine ⟨13096273125213967509845873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8730848750142645006563915 13096273125213967509845873)
              ·
                refine ⟨9822204843910475632384405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13096273125213967509845873 9822204843910475632384405)
                ·
                  refine ⟨460415852058303545268019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9822204843910475632384405 460415852058303545268019)
                  ·
                    rfl

theorem cell22_4034955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 6].length) (baseStart_4034955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034955 prefixEnd_4034955 := by exact prefixLift 4034955
  have htrace : WordTrace (prefixWord ++ tailWord_4034955) baseStart_4034955 baseEnd_4034955 := by
    simpa [prefixWord, tailWord_4034955, baseEnd_4034955] using wordTrace_append hprefix tailTrace_4034955
  have hstable : (prefixWord ++ tailWord_4034955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034955).length < 2 ^ (prefixWord ++ tailWord_4034955).sum := by decide
  have hdescent : baseEnd_4034955 < baseStart_4034955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034985 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_4034985 : Nat := 118140960795 + 4034985 * 2 ^ 59
def prefixEnd_4034985 : Nat := 4983230072969 + 3 ^ 40 * 4034985 * 2
def baseEnd_4034985 : Nat := 1381257825788000557553965

theorem tailTrace_4034985 : CollatzResearch.WordTrace tailWord_4034985 prefixEnd_4034985 1381257825788000557553965 := by
  unfold tailWord_4034985
  simp only [CollatzResearch.WordTrace]
  refine ⟨147167993286945940419418409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98111995524630626946278939 147167993286945940419418409)
  ·
    refine ⟨110375994965209455314563807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147167993286945940419418409 110375994965209455314563807)
    ·
      refine ⟨165563992447814182971845711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110375994965209455314563807 165563992447814182971845711)
      ·
        refine ⟨248345988671721274457768567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165563992447814182971845711 248345988671721274457768567)
        ·
          refine ⟨372518983007581911686652851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248345988671721274457768567 372518983007581911686652851)
          ·
            refine ⟨558778474511372867529979277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372518983007581911686652851 558778474511372867529979277)
            ·
              refine ⟨209541927941764825323742229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558778474511372867529979277 209541927941764825323742229)
              ·
                refine ⟨9822277872270226187050417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209541927941764825323742229 9822277872270226187050417)
                ·
                  refine ⟨7366708404202669640287813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9822277872270226187050417 7366708404202669640287813)
                  ·
                    refine ⟨1381257825788000557553965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7366708404202669640287813 1381257825788000557553965)
                    ·
                      rfl

theorem cell22_4034985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_4034985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034985 prefixEnd_4034985 := by exact prefixLift 4034985
  have htrace : WordTrace (prefixWord ++ tailWord_4034985) baseStart_4034985 baseEnd_4034985 := by
    simpa [prefixWord, tailWord_4034985, baseEnd_4034985] using wordTrace_append hprefix tailTrace_4034985
  have hstable : (prefixWord ++ tailWord_4034985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034985).length < 2 ^ (prefixWord ++ tailWord_4034985).sum := by decide
  have hdescent : baseEnd_4034985 < baseStart_4034985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034989 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 6]
def baseStart_4034989 : Nat := 118140960795 + 4034989 * 2 ^ 59
def prefixEnd_4034989 : Nat := 4983230072969 + 3 ^ 40 * 4034989 * 2
def baseEnd_4034989 : Nat := 460419731689915293484651

theorem tailTrace_4034989 : CollatzResearch.WordTrace tailWord_4034989 prefixEnd_4034989 460419731689915293484651 := by
  unfold tailWord_4034989
  simp only [CollatzResearch.WordTrace]
  refine ⟨147168139178931449102564021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98112092785954299401709347 147168139178931449102564021)
  ·
    refine ⟨13797013048024823353365377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147168139178931449102564021 13797013048024823353365377)
    ·
      refine ⟨10347759786018617515024033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13797013048024823353365377 10347759786018617515024033)
      ·
        refine ⟨7760819839513963136268025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10347759786018617515024033 7760819839513963136268025)
        ·
          refine ⟨5820614879635472352201019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7760819839513963136268025 5820614879635472352201019)
          ·
            refine ⟨8730922319453208528301529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820614879635472352201019 8730922319453208528301529)
            ·
              refine ⟨6548191739589906396226147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8730922319453208528301529 6548191739589906396226147)
              ·
                refine ⟨9822287609384859594339221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548191739589906396226147 9822287609384859594339221)
                ·
                  refine ⟨460419731689915293484651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9822287609384859594339221 460419731689915293484651)
                  ·
                    rfl

theorem cell22_4034989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_4034989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4034989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4034989 prefixEnd_4034989 := by exact prefixLift 4034989
  have htrace : WordTrace (prefixWord ++ tailWord_4034989) baseStart_4034989 baseEnd_4034989 := by
    simpa [prefixWord, tailWord_4034989, baseEnd_4034989] using wordTrace_append hprefix tailTrace_4034989
  have hstable : (prefixWord ++ tailWord_4034989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034989).length < 2 ^ (prefixWord ++ tailWord_4034989).sum := by decide
  have hdescent : baseEnd_4034989 < baseStart_4034989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035004 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 1, 5]
def baseStart_4035004 : Nat := 118140960795 + 4035004 * 2 ^ 59
def prefixEnd_4035004 : Nat := 4983230072969 + 3 ^ 40 * 4035004 * 2
def baseEnd_4035004 : Nat := 1381264329876290841328907

theorem tailTrace_4035004 : CollatzResearch.WordTrace tailWord_4035004 prefixEnd_4035004 1381264329876290841328907 := by
  unfold tailWord_4035004
  simp only [CollatzResearch.WordTrace]
  refine ⟨73584343136938553332180033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98112457515918071109573377 73584343136938553332180033)
  ·
    refine ⟨55188257352703914999135025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73584343136938553332180033 55188257352703914999135025)
    ·
      refine ⟨41391193014527936249351269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55188257352703914999135025 41391193014527936249351269)
      ·
        refine ⟨7760848690223988046753363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41391193014527936249351269 7760848690223988046753363)
        ·
          refine ⟨11641273035335982070130045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760848690223988046753363 11641273035335982070130045)
          ·
            refine ⟨4365477388250993276298767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11641273035335982070130045 4365477388250993276298767)
            ·
              refine ⟨6548216082376489914448151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365477388250993276298767 6548216082376489914448151)
              ·
                refine ⟨9822324123564734871672227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548216082376489914448151 9822324123564734871672227)
                ·
                  refine ⟨14733486185347102307508341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9822324123564734871672227 14733486185347102307508341)
                  ·
                    refine ⟨1381264329876290841328907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14733486185347102307508341 1381264329876290841328907)
                    ·
                      rfl

theorem cell22_4035004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_4035004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035004 prefixEnd_4035004 := by exact prefixLift 4035004
  have htrace : WordTrace (prefixWord ++ tailWord_4035004) baseStart_4035004 baseEnd_4035004 := by
    simpa [prefixWord, tailWord_4035004, baseEnd_4035004] using wordTrace_append hprefix tailTrace_4035004
  have hstable : (prefixWord ++ tailWord_4035004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035004).length < 2 ^ (prefixWord ++ tailWord_4035004).sum := by decide
  have hdescent : baseEnd_4035004 < baseStart_4035004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035111 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4035111 : Nat := 118140960795 + 4035111 * 2 ^ 59
def prefixEnd_4035111 : Nat := 4983230072969 + 3 ^ 40 * 4035111 * 2
def baseEnd_4035111 : Nat := 1381300958162978228903579

theorem tailTrace_4035111 : CollatzResearch.WordTrace tailWord_4035111 prefixEnd_4035111 1381300958162978228903579 := by
  unfold tailWord_4035111
  simp only [CollatzResearch.WordTrace]
  refine ⟨147172588884489463938505187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98115059256326309292336791 147172588884489463938505187)
  ·
    refine ⟨220758883326734195907757781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147172588884489463938505187 220758883326734195907757781)
    ·
      refine ⟨5174036327970332716588073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 220758883326734195907757781 5174036327970332716588073)
      ·
        refine ⟨3880527245977749537441055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5174036327970332716588073 3880527245977749537441055)
        ·
          refine ⟨5820790868966624306161583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880527245977749537441055 5820790868966624306161583)
          ·
            refine ⟨8731186303449936459242375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820790868966624306161583 8731186303449936459242375)
            ·
              refine ⟨13096779455174904688863563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8731186303449936459242375 13096779455174904688863563)
              ·
                refine ⟨19645169182762357033295345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13096779455174904688863563 19645169182762357033295345)
                ·
                  refine ⟨14733876887071767774971509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19645169182762357033295345 14733876887071767774971509)
                  ·
                    refine ⟨1381300958162978228903579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14733876887071767774971509 1381300958162978228903579)
                    ·
                      rfl

theorem cell22_4035111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4035111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035111 prefixEnd_4035111 := by exact prefixLift 4035111
  have htrace : WordTrace (prefixWord ++ tailWord_4035111) baseStart_4035111 baseEnd_4035111 := by
    simpa [prefixWord, tailWord_4035111, baseEnd_4035111] using wordTrace_append hprefix tailTrace_4035111
  have hstable : (prefixWord ++ tailWord_4035111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035111).length < 2 ^ (prefixWord ++ tailWord_4035111).sum := by decide
  have hdescent : baseEnd_4035111 < baseStart_4035111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035122 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_4035122 : Nat := 118140960795 + 4035122 * 2 ^ 59
def prefixEnd_4035122 : Nat := 4983230072969 + 3 ^ 40 * 4035122 * 2
def baseEnd_4035122 : Nat := 1381304723687777866878545

theorem tailTrace_4035122 : CollatzResearch.WordTrace tailWord_4035122 prefixEnd_4035122 1381304723687777866878545 := by
  unfold tailWord_4035122
  simp only [CollatzResearch.WordTrace]
  refine ⟨36793247521862403204288905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98115326724966408544770413 36793247521862403204288905)
  ·
    refine ⟨27594935641396802403216679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36793247521862403204288905 27594935641396802403216679)
    ·
      refine ⟨41392403462095203604825019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27594935641396802403216679 41392403462095203604825019)
      ·
        refine ⟨62088605193142805407237529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41392403462095203604825019 62088605193142805407237529)
        ·
          refine ⟨46566453894857104055428147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62088605193142805407237529 46566453894857104055428147)
          ·
            refine ⟨69849680842285656083142221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46566453894857104055428147 69849680842285656083142221)
            ·
              refine ⟨26193630315857121031178333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69849680842285656083142221 26193630315857121031178333)
              ·
                refine ⟨9822611368446420386691875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26193630315857121031178333 9822611368446420386691875)
                ·
                  refine ⟨14733917052669630580037813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9822611368446420386691875 14733917052669630580037813)
                  ·
                    refine ⟨1381304723687777866878545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14733917052669630580037813 1381304723687777866878545)
                    ·
                      rfl

theorem cell22_4035122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_4035122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035122 prefixEnd_4035122 := by exact prefixLift 4035122
  have htrace : WordTrace (prefixWord ++ tailWord_4035122) baseStart_4035122 baseEnd_4035122 := by
    simpa [prefixWord, tailWord_4035122, baseEnd_4035122] using wordTrace_append hprefix tailTrace_4035122
  have hstable : (prefixWord ++ tailWord_4035122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035122).length < 2 ^ (prefixWord ++ tailWord_4035122).sum := by decide
  have hdescent : baseEnd_4035122 < baseStart_4035122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035156 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_4035156 : Nat := 118140960795 + 4035156 * 2 ^ 59
def prefixEnd_4035156 : Nat := 4983230072969 + 3 ^ 40 * 4035156 * 2
def baseEnd_4035156 : Nat := 1381316362582613111528441

theorem tailTrace_4035156 : CollatzResearch.WordTrace tailWord_4035156 prefixEnd_4035156 1381316362582613111528441 := by
  unfold tailWord_4035156
  simp only [CollatzResearch.WordTrace]
  refine ⟨73587115084663218311946661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98116153446217624415928881 73587115084663218311946661)
  ·
    refine ⟨13797584078374353433489999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73587115084663218311946661 13797584078374353433489999)
    ·
      refine ⟨20696376117561530150234999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13797584078374353433489999 20696376117561530150234999)
      ·
        refine ⟨31044564176342295225352499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20696376117561530150234999 31044564176342295225352499)
        ·
          refine ⟨46566846264513442838028749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31044564176342295225352499 46566846264513442838028749)
          ·
            refine ⟨17462567349192541064260781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46566846264513442838028749 17462567349192541064260781)
            ·
              refine ⟨6548462755947202899097793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17462567349192541064260781 6548462755947202899097793)
              ·
                refine ⟨4911347066960402174323345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6548462755947202899097793 4911347066960402174323345)
                ·
                  refine ⟨3683510300220301630742509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4911347066960402174323345 3683510300220301630742509)
                  ·
                    refine ⟨1381316362582613111528441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683510300220301630742509 1381316362582613111528441)
                    ·
                      rfl

theorem cell22_4035156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_4035156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035156 prefixEnd_4035156 := by exact prefixLift 4035156
  have htrace : WordTrace (prefixWord ++ tailWord_4035156) baseStart_4035156 baseEnd_4035156 := by
    simpa [prefixWord, tailWord_4035156, baseEnd_4035156] using wordTrace_append hprefix tailTrace_4035156
  have hstable : (prefixWord ++ tailWord_4035156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035156).length < 2 ^ (prefixWord ++ tailWord_4035156).sum := by decide
  have hdescent : baseEnd_4035156 < baseStart_4035156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035173 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 2, 3]
def baseStart_4035173 : Nat := 118140960795 + 4035173 * 2 ^ 59
def prefixEnd_4035173 : Nat := 4983230072969 + 3 ^ 40 * 4035173 * 2
def baseEnd_4035173 : Nat := 1381322182030030733853389

theorem tailTrace_4035173 : CollatzResearch.WordTrace tailWord_4035173 prefixEnd_4035173 1381322182030030733853389 := by
  unfold tailWord_4035173
  simp only [CollatzResearch.WordTrace]
  refine ⟨147174850210264848527262173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98116566806843232351508115 147174850210264848527262173)
  ·
    refine ⟨55190568828849318197723315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147174850210264848527262173 55190568828849318197723315)
    ·
      refine ⟨82785853243273977296584973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55190568828849318197723315 82785853243273977296584973)
      ·
        refine ⟨31044694966227741486219365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82785853243273977296584973 31044694966227741486219365)
        ·
          refine ⟨5820880306167701528666131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31044694966227741486219365 5820880306167701528666131)
          ·
            refine ⟨8731320459251552292999197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820880306167701528666131 8731320459251552292999197)
            ·
              refine ⟨3274245172219332109874699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8731320459251552292999197 3274245172219332109874699)
              ·
                refine ⟨4911367758328998164812049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274245172219332109874699 4911367758328998164812049)
                ·
                  refine ⟨3683525818746748623609037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4911367758328998164812049 3683525818746748623609037)
                  ·
                    refine ⟨1381322182030030733853389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683525818746748623609037 1381322182030030733853389)
                    ·
                      rfl

theorem cell22_4035173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_4035173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035173 prefixEnd_4035173 := by exact prefixLift 4035173
  have htrace : WordTrace (prefixWord ++ tailWord_4035173) baseStart_4035173 baseEnd_4035173 := by
    simpa [prefixWord, tailWord_4035173, baseEnd_4035173] using wordTrace_append hprefix tailTrace_4035173
  have hstable : (prefixWord ++ tailWord_4035173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035173).length < 2 ^ (prefixWord ++ tailWord_4035173).sum := by decide
  have hdescent : baseEnd_4035173 < baseStart_4035173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035186 : List Nat := [3, 2, 1, 2, 4, 2, 2, 6]
def baseStart_4035186 : Nat := 118140960795 + 4035186 * 2 ^ 59
def prefixEnd_4035186 : Nat := 4983230072969 + 3 ^ 40 * 4035186 * 2
def baseEnd_4035186 : Nat := 153480736910633670364261

theorem tailTrace_4035186 : CollatzResearch.WordTrace tailWord_4035186 prefixEnd_4035186 153480736910633670364261 := by
  unfold tailWord_4035186
  simp only [CollatzResearch.WordTrace]
  refine ⟨36793831089804437936871353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98116882906145167831656941 36793831089804437936871353)
  ·
    refine ⟨27595373317353328452653515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36793831089804437936871353 27595373317353328452653515)
    ·
      refine ⟨41393059976029992678980273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27595373317353328452653515 41393059976029992678980273)
      ·
        refine ⟨31044794982022494509235205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41393059976029992678980273 31044794982022494509235205)
        ·
          refine ⟨5820899059129217720481601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31044794982022494509235205 5820899059129217720481601)
          ·
            refine ⟨4365674294346913290361201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5820899059129217720481601 4365674294346913290361201)
            ·
              refine ⟨3274255720760184967770901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365674294346913290361201 3274255720760184967770901)
              ·
                refine ⟨153480736910633670364261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3274255720760184967770901 153480736910633670364261)
                ·
                  rfl

theorem cell22_4035186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_4035186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035186 prefixEnd_4035186 := by exact prefixLift 4035186
  have htrace : WordTrace (prefixWord ++ tailWord_4035186) baseStart_4035186 baseEnd_4035186 := by
    simpa [prefixWord, tailWord_4035186, baseEnd_4035186] using wordTrace_append hprefix tailTrace_4035186
  have hstable : (prefixWord ++ tailWord_4035186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035186).length < 2 ^ (prefixWord ++ tailWord_4035186).sum := by decide
  have hdescent : baseEnd_4035186 < baseStart_4035186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035212 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_4035212 : Nat := 118140960795 + 4035212 * 2 ^ 59
def prefixEnd_4035212 : Nat := 4983230072969 + 3 ^ 40 * 4035212 * 2
def baseEnd_4035212 : Nat := 1381335532527047632128269

theorem tailTrace_4035212 : CollatzResearch.WordTrace tailWord_4035212 prefixEnd_4035212 1381335532527047632128269 := by
  unfold tailWord_4035212
  simp only [CollatzResearch.WordTrace]
  refine ⟨73588136328561779093965945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98117515104749038791954593 73588136328561779093965945)
  ·
    refine ⟨55191102246421334320474459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73588136328561779093965945 55191102246421334320474459)
    ·
      refine ⟨82786653369632001480711689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55191102246421334320474459 82786653369632001480711689)
      ·
        refine ⟨62089990027224001110533767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82786653369632001480711689 62089990027224001110533767)
        ·
          refine ⟨93134985040836001665800651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62089990027224001110533767 93134985040836001665800651)
          ·
            refine ⟨139702477561254002498700977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93134985040836001665800651 139702477561254002498700977)
            ·
              refine ⟨104776858170940501874025733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139702477561254002498700977 104776858170940501874025733)
              ·
                refine ⟨19645660907051344101379825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104776858170940501874025733 19645660907051344101379825)
                ·
                  refine ⟨14734245680288508076034869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19645660907051344101379825 14734245680288508076034869)
                  ·
                    refine ⟨1381335532527047632128269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14734245680288508076034869 1381335532527047632128269)
                    ·
                      rfl

theorem cell22_4035212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_4035212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035212 prefixEnd_4035212 := by exact prefixLift 4035212
  have htrace : WordTrace (prefixWord ++ tailWord_4035212) baseStart_4035212 baseEnd_4035212 := by
    simpa [prefixWord, tailWord_4035212, baseEnd_4035212] using wordTrace_append hprefix tailTrace_4035212
  have hstable : (prefixWord ++ tailWord_4035212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035212).length < 2 ^ (prefixWord ++ tailWord_4035212).sum := by decide
  have hdescent : baseEnd_4035212 < baseStart_4035212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035214 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_4035214 : Nat := 118140960795 + 4035214 * 2 ^ 59
def prefixEnd_4035214 : Nat := 4983230072969 + 3 ^ 40 * 4035214 * 2
def baseEnd_4035214 : Nat := 460445405722640097859421

theorem tailTrace_4035214 : CollatzResearch.WordTrace tailWord_4035214 prefixEnd_4035214 460445405722640097859421 := by
  unfold tailWord_4035214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18397043200389539066188087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98117563735410875019669797 18397043200389539066188087)
  ·
    refine ⟨27595564800584308599282131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18397043200389539066188087 27595564800584308599282131)
    ·
      refine ⟨41393347200876462898923197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27595564800584308599282131 41393347200876462898923197)
      ·
        refine ⟨15522505200328673587096199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41393347200876462898923197 15522505200328673587096199)
        ·
          refine ⟨23283757800493010380644299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15522505200328673587096199 23283757800493010380644299)
          ·
            refine ⟨34925636700739515570966449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23283757800493010380644299 34925636700739515570966449)
            ·
              refine ⟨26194227525554636678224837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34925636700739515570966449 26194227525554636678224837)
              ·
                refine ⟨4911417661041494377167157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26194227525554636678224837 4911417661041494377167157)
                ·
                  refine ⟨460445405722640097859421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4911417661041494377167157 460445405722640097859421)
                  ·
                    rfl

theorem cell22_4035214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_4035214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035214 prefixEnd_4035214 := by exact prefixLift 4035214
  have htrace : WordTrace (prefixWord ++ tailWord_4035214) baseStart_4035214 baseEnd_4035214 := by
    simpa [prefixWord, tailWord_4035214, baseEnd_4035214] using wordTrace_append hprefix tailTrace_4035214
  have hstable : (prefixWord ++ tailWord_4035214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035214).length < 2 ^ (prefixWord ++ tailWord_4035214).sum := by decide
  have hdescent : baseEnd_4035214 < baseStart_4035214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035218 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_4035218 : Nat := 118140960795 + 4035218 * 2 ^ 59
def prefixEnd_4035218 : Nat := 4983230072969 + 3 ^ 40 * 4035218 * 2
def baseEnd_4035218 : Nat := 1381337586449665616478251

theorem tailTrace_4035218 : CollatzResearch.WordTrace tailWord_4035218 prefixEnd_4035218 1381337586449665616478251 := by
  unfold tailWord_4035218
  simp only [CollatzResearch.WordTrace]
  refine ⟨36794122873775455303162577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98117660996734547475100205 36794122873775455303162577)
  ·
    refine ⟨27595592155331591477371933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36794122873775455303162577 27595592155331591477371933)
    ·
      refine ⟨10348347058249346804014475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27595592155331591477371933 10348347058249346804014475)
      ·
        refine ⟨15522520587374020206021713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10348347058249346804014475 15522520587374020206021713)
        ·
          refine ⟨11641890440530515154516285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15522520587374020206021713 11641890440530515154516285)
          ·
            refine ⟨4365708915198943182943607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11641890440530515154516285 4365708915198943182943607)
            ·
              refine ⟨6548563372798414774415411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365708915198943182943607 6548563372798414774415411)
              ·
                refine ⟨9822845059197622161623117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548563372798414774415411 9822845059197622161623117)
                ·
                  refine ⟨3683566897199108310608669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9822845059197622161623117 3683566897199108310608669)
                  ·
                    refine ⟨1381337586449665616478251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683566897199108310608669 1381337586449665616478251)
                    ·
                      rfl

theorem cell22_4035218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_4035218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035218 prefixEnd_4035218 := by exact prefixLift 4035218
  have htrace : WordTrace (prefixWord ++ tailWord_4035218) baseStart_4035218 baseEnd_4035218 := by
    simpa [prefixWord, tailWord_4035218, baseEnd_4035218] using wordTrace_append hprefix tailTrace_4035218
  have hstable : (prefixWord ++ tailWord_4035218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035218).length < 2 ^ (prefixWord ++ tailWord_4035218).sum := by decide
  have hdescent : baseEnd_4035218 < baseStart_4035218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035319 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 7, 3]
def baseStart_4035319 : Nat := 118140960795 + 4035319 * 2 ^ 59
def prefixEnd_4035319 : Nat := 4983230072969 + 3 ^ 40 * 4035319 * 2
def baseEnd_4035319 : Nat := 1381372160813735019702941

theorem tailTrace_4035319 : CollatzResearch.WordTrace tailWord_4035319 prefixEnd_4035319 1381372160813735019702941 := by
  unfold tailWord_4035319
  simp only [CollatzResearch.WordTrace]
  refine ⟨147180175267735915462077011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98120116845157276974718007 147180175267735915462077011)
  ·
    refine ⟨220770262901603873193115517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147180175267735915462077011 220770262901603873193115517)
    ·
      refine ⟨82788848588101452447418319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220770262901603873193115517 82788848588101452447418319)
      ·
        refine ⟨124183272882152178671127479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82788848588101452447418319 124183272882152178671127479)
        ·
          refine ⟨186274909323228268006691219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124183272882152178671127479 186274909323228268006691219)
          ·
            refine ⟨279412363984842402010036829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186274909323228268006691219 279412363984842402010036829)
            ·
              refine ⟨104779636494315900753763811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279412363984842402010036829 104779636494315900753763811)
              ·
                refine ⟨157169454741473851130645717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104779636494315900753763811 157169454741473851130645717)
                ·
                  refine ⟨3683659095503293385874509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 157169454741473851130645717 3683659095503293385874509)
                  ·
                    refine ⟨1381372160813735019702941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683659095503293385874509 1381372160813735019702941)
                    ·
                      rfl

theorem cell22_4035319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_4035319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035319 prefixEnd_4035319 := by exact prefixLift 4035319
  have htrace : WordTrace (prefixWord ++ tailWord_4035319) baseStart_4035319 baseEnd_4035319 := by
    simpa [prefixWord, tailWord_4035319, baseEnd_4035319] using wordTrace_append hprefix tailTrace_4035319
  have hstable : (prefixWord ++ tailWord_4035319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035319).length < 2 ^ (prefixWord ++ tailWord_4035319).sum := by decide
  have hdescent : baseEnd_4035319 < baseStart_4035319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035336 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 3, 3]
def baseStart_4035336 : Nat := 118140960795 + 4035336 * 2 ^ 59
def prefixEnd_4035336 : Nat := 4983230072969 + 3 ^ 40 * 4035336 * 2
def baseEnd_4035336 : Nat := 1381377980261152642027889

theorem tailTrace_4035336 : CollatzResearch.WordTrace tailWord_4035336 prefixEnd_4035336 1381377980261152642027889 := by
  unfold tailWord_4035336
  simp only [CollatzResearch.WordTrace]
  refine ⟨73590397654337163682722931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98120530205782884910297241 73590397654337163682722931)
  ·
    refine ⟨110385596481505745524084397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73590397654337163682722931 110385596481505745524084397)
    ·
      refine ⟨41394598680564654571531649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110385596481505745524084397 41394598680564654571531649)
      ·
        refine ⟨31045949010423490928648737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41394598680564654571531649 31045949010423490928648737)
        ·
          refine ⟨23284461757817618196486553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31045949010423490928648737 23284461757817618196486553)
          ·
            refine ⟨17463346318363213647364915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23284461757817618196486553 17463346318363213647364915)
            ·
              refine ⟨26195019477544820471047373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17463346318363213647364915 26195019477544820471047373)
              ·
                refine ⟨9823132304079307676642765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26195019477544820471047373 9823132304079307676642765)
                ·
                  refine ⟨3683674614029740378741037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9823132304079307676642765 3683674614029740378741037)
                  ·
                    refine ⟨1381377980261152642027889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683674614029740378741037 1381377980261152642027889)
                    ·
                      rfl

theorem cell22_4035336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_4035336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035336 prefixEnd_4035336 := by exact prefixLift 4035336
  have htrace : WordTrace (prefixWord ++ tailWord_4035336) baseStart_4035336 baseEnd_4035336 := by
    simpa [prefixWord, tailWord_4035336, baseEnd_4035336] using wordTrace_append hprefix tailTrace_4035336
  have hstable : (prefixWord ++ tailWord_4035336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035336).length < 2 ^ (prefixWord ++ tailWord_4035336).sum := by decide
  have hdescent : baseEnd_4035336 < baseStart_4035336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035441 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_4035441 : Nat := 118140960795 + 4035441 * 2 ^ 59
def prefixEnd_4035441 : Nat := 4983230072969 + 3 ^ 40 * 4035441 * 2
def baseEnd_4035441 : Nat := 1381413923906967368152567

theorem tailTrace_4035441 : CollatzResearch.WordTrace tailWord_4035441 prefixEnd_4035441 1381413923906967368152567 := by
  unfold tailWord_4035441
  simp only [CollatzResearch.WordTrace]
  refine ⟨147184624973293930298018177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98123083315529286865345451 147184624973293930298018177)
  ·
    refine ⟨110388468729970447723513633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147184624973293930298018177 110388468729970447723513633)
    ·
      refine ⟨82791351547477835792635225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110388468729970447723513633 82791351547477835792635225)
      ·
        refine ⟨62093513660608376844476419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82791351547477835792635225 62093513660608376844476419)
        ·
          refine ⟨93140270490912565266714629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62093513660608376844476419 93140270490912565266714629)
          ·
            refine ⟨17463800717046105987508993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93140270490912565266714629 17463800717046105987508993)
            ·
              refine ⟨13097850537784579490631745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17463800717046105987508993 13097850537784579490631745)
              ·
                refine ⟨9823387903338434617973809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13097850537784579490631745 9823387903338434617973809)
                ·
                  refine ⟨7367540927503825963480357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9823387903338434617973809 7367540927503825963480357)
                  ·
                    refine ⟨1381413923906967368152567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7367540927503825963480357 1381413923906967368152567)
                    ·
                      rfl

theorem cell22_4035441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_4035441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035441 prefixEnd_4035441 := by exact prefixLift 4035441
  have htrace : WordTrace (prefixWord ++ tailWord_4035441) baseStart_4035441 baseEnd_4035441 := by
    simpa [prefixWord, tailWord_4035441, baseEnd_4035441] using wordTrace_append hprefix tailTrace_4035441
  have hstable : (prefixWord ++ tailWord_4035441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035441).length < 2 ^ (prefixWord ++ tailWord_4035441).sum := by decide
  have hdescent : baseEnd_4035441 < baseStart_4035441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035445 : List Nat := [1, 3, 4, 1, 1, 2, 4, 2, 4]
def baseStart_4035445 : Nat := 118140960795 + 4035445 * 2 ^ 59
def prefixEnd_4035445 : Nat := 4983230072969 + 3 ^ 40 * 4035445 * 2
def baseEnd_4035445 : Nat := 460471764396237563684185

theorem tailTrace_4035445 : CollatzResearch.WordTrace tailWord_4035445 prefixEnd_4035445 460471764396237563684185 := by
  unfold tailWord_4035445
  simp only [CollatzResearch.WordTrace]
  refine ⟨147184770865279438981163789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98123180576852959320775859 147184770865279438981163789)
  ·
    refine ⟨55194289074479789617936421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147184770865279438981163789 55194289074479789617936421)
    ·
      refine ⟨10348929201464960553363079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55194289074479789617936421 10348929201464960553363079)
      ·
        refine ⟨15523393802197440830044619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10348929201464960553363079 15523393802197440830044619)
        ·
          refine ⟨23285090703296161245066929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15523393802197440830044619 23285090703296161245066929)
          ·
            refine ⟨17463818027472120933800197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23285090703296161245066929 17463818027472120933800197)
            ·
              refine ⟨3274465880151022675087537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17463818027472120933800197 3274465880151022675087537)
              ·
                refine ⟨2455849410113267006315653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274465880151022675087537 2455849410113267006315653)
                ·
                  refine ⟨460471764396237563684185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2455849410113267006315653 460471764396237563684185)
                  ·
                    rfl

theorem cell22_4035445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_4035445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035445 prefixEnd_4035445 := by exact prefixLift 4035445
  have htrace : WordTrace (prefixWord ++ tailWord_4035445) baseStart_4035445 baseEnd_4035445 := by
    simpa [prefixWord, tailWord_4035445, baseEnd_4035445] using wordTrace_append hprefix tailTrace_4035445
  have hstable : (prefixWord ++ tailWord_4035445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035445).length < 2 ^ (prefixWord ++ tailWord_4035445).sum := by decide
  have hdescent : baseEnd_4035445 < baseStart_4035445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035499 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 3, 7]
def baseStart_4035499 : Nat := 118140960795 + 4035499 * 2 ^ 59
def prefixEnd_4035499 : Nat := 4983230072969 + 3 ^ 40 * 4035499 * 2
def baseEnd_4035499 : Nat := 1381433778492274550202389

theorem tailTrace_4035499 : CollatzResearch.WordTrace tailWord_4035499 prefixEnd_4035499 1381433778492274550202389 := by
  unfold tailWord_4035499
  simp only [CollatzResearch.WordTrace]
  refine ⟨147186740407083806203629551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98124493604722537469086367 147186740407083806203629551)
  ·
    refine ⟨220780110610625709305444327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147186740407083806203629551 220780110610625709305444327)
    ·
      refine ⟨331170165915938563958166491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220780110610625709305444327 331170165915938563958166491)
      ·
        refine ⟨496755248873907845937249737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331170165915938563958166491 496755248873907845937249737)
        ·
          refine ⟨372566436655430884452937303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496755248873907845937249737 372566436655430884452937303)
          ·
            refine ⟨558849654983146326679405955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372566436655430884452937303 558849654983146326679405955)
            ·
              refine ⟨838274482474719490019108933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558849654983146326679405955 838274482474719490019108933)
              ·
                refine ⟨157176465464009904378582925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 838274482474719490019108933 157176465464009904378582925)
                ·
                  refine ⟨58941174549003714141968597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157176465464009904378582925 58941174549003714141968597)
                  ·
                    refine ⟨1381433778492274550202389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58941174549003714141968597 1381433778492274550202389)
                    ·
                      rfl

theorem cell22_4035499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_4035499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035499 prefixEnd_4035499 := by exact prefixLift 4035499
  have htrace : WordTrace (prefixWord ++ tailWord_4035499) baseStart_4035499 baseEnd_4035499 := by
    simpa [prefixWord, tailWord_4035499, baseEnd_4035499] using wordTrace_append hprefix tailTrace_4035499
  have hstable : (prefixWord ++ tailWord_4035499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035499).length < 2 ^ (prefixWord ++ tailWord_4035499).sum := by decide
  have hdescent : baseEnd_4035499 < baseStart_4035499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035505 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 3, 3]
def baseStart_4035505 : Nat := 118140960795 + 4035505 * 2 ^ 59
def prefixEnd_4035505 : Nat := 4983230072969 + 3 ^ 40 * 4035505 * 2
def baseEnd_4035505 : Nat := 1381435832414892534552371

theorem tailTrace_4035505 : CollatzResearch.WordTrace tailWord_4035505 prefixEnd_4035505 1381435832414892534552371 := by
  unfold tailWord_4035505
  simp only [CollatzResearch.WordTrace]
  refine ⟨147186959245062069228347969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98124639496708046152231979 147186959245062069228347969)
  ·
    refine ⟨110390219433796551921260977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147186959245062069228347969 110390219433796551921260977)
    ·
      refine ⟨82792664575347413940945733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110390219433796551921260977 82792664575347413940945733)
      ·
        refine ⟨15523624607877640113927325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82792664575347413940945733 15523624607877640113927325)
        ·
          refine ⟨5821359227954115042722747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15523624607877640113927325 5821359227954115042722747)
          ·
            refine ⟨8732038841931172564084121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5821359227954115042722747 8732038841931172564084121)
            ·
              refine ⟨6549029131448379423063091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8732038841931172564084121 6549029131448379423063091)
              ·
                refine ⟨9823543697172569134594637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6549029131448379423063091 9823543697172569134594637)
                ·
                  refine ⟨3683828886439713425472989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9823543697172569134594637 3683828886439713425472989)
                  ·
                    refine ⟨1381435832414892534552371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683828886439713425472989 1381435832414892534552371)
                    ·
                      rfl

theorem cell22_4035505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_4035505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035505 prefixEnd_4035505 := by exact prefixLift 4035505
  have htrace : WordTrace (prefixWord ++ tailWord_4035505) baseStart_4035505 baseEnd_4035505 := by
    simpa [prefixWord, tailWord_4035505, baseEnd_4035505] using wordTrace_append hprefix tailTrace_4035505
  have hstable : (prefixWord ++ tailWord_4035505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035505).length < 2 ^ (prefixWord ++ tailWord_4035505).sum := by decide
  have hdescent : baseEnd_4035505 < baseStart_4035505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035576 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_4035576 : Nat := 118140960795 + 4035576 * 2 ^ 59
def prefixEnd_4035576 : Nat := 4983230072969 + 3 ^ 40 * 4035576 * 2
def baseEnd_4035576 : Nat := 1381460137165872016027153

theorem tailTrace_4035576 : CollatzResearch.WordTrace tailWord_4035576 prefixEnd_4035576 1381460137165872016027153 := by
  unfold tailWord_4035576
  simp only [CollatzResearch.WordTrace]
  refine ⟨73594774413902424177091291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98126365885203232236121721 73594774413902424177091291)
  ·
    refine ⟨110392161620853636265636937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73594774413902424177091291 110392161620853636265636937)
    ·
      refine ⟨82794121215640227199227703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110392161620853636265636937 82794121215640227199227703)
      ·
        refine ⟨124191181823460340798841555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82794121215640227199227703 124191181823460340798841555)
        ·
          refine ⟨186286772735190511198262333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124191181823460340798841555 186286772735190511198262333)
          ·
            refine ⟨69857539775696441699348375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186286772735190511198262333 69857539775696441699348375)
            ·
              refine ⟨104786309663544662549022563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69857539775696441699348375 104786309663544662549022563)
              ·
                refine ⟨157179464495316993823533845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104786309663544662549022563 157179464495316993823533845)
                ·
                  refine ⟨7367787398217984085478149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157179464495316993823533845 7367787398217984085478149)
                  ·
                    refine ⟨1381460137165872016027153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7367787398217984085478149 1381460137165872016027153)
                    ·
                      rfl

theorem cell22_4035576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_4035576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035576 prefixEnd_4035576 := by exact prefixLift 4035576
  have htrace : WordTrace (prefixWord ++ tailWord_4035576) baseStart_4035576 baseEnd_4035576 := by
    simpa [prefixWord, tailWord_4035576, baseEnd_4035576] using wordTrace_append hprefix tailTrace_4035576
  have hstable : (prefixWord ++ tailWord_4035576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035576).length < 2 ^ (prefixWord ++ tailWord_4035576).sum := by decide
  have hdescent : baseEnd_4035576 < baseStart_4035576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035591 : List Nat := [1, 1, 4, 3, 1, 1, 1, 10]
def baseStart_4035591 : Nat := 118140960795 + 4035591 * 2 ^ 59
def prefixEnd_4035591 : Nat := 4983230072969 + 3 ^ 40 * 4035591 * 2
def baseEnd_4035591 : Nat := 153496141330268552989123

theorem tailTrace_4035591 : CollatzResearch.WordTrace tailWord_4035591 prefixEnd_4035591 153496141330268552989123 := by
  unfold tailWord_4035591
  simp only [CollatzResearch.WordTrace]
  refine ⟨147190095922750505915978627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98126730615167003943985751 147190095922750505915978627)
  ·
    refine ⟨220785143884125758873967941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147190095922750505915978627 220785143884125758873967941)
    ·
      refine ⟨41397214478273579788868989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220785143884125758873967941 41397214478273579788868989)
      ·
        refine ⟨15523955429352592420825871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41397214478273579788868989 15523955429352592420825871)
        ·
          refine ⟨23285933144028888631238807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15523955429352592420825871 23285933144028888631238807)
          ·
            refine ⟨34928899716043332946858211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23285933144028888631238807 34928899716043332946858211)
            ·
              refine ⟨52393349574064999420287317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34928899716043332946858211 52393349574064999420287317)
              ·
                refine ⟨153496141330268552989123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52393349574064999420287317 153496141330268552989123)
                ·
                  rfl

theorem cell22_4035591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 10].length) (baseStart_4035591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035591 prefixEnd_4035591 := by exact prefixLift 4035591
  have htrace : WordTrace (prefixWord ++ tailWord_4035591) baseStart_4035591 baseEnd_4035591 := by
    simpa [prefixWord, tailWord_4035591, baseEnd_4035591] using wordTrace_append hprefix tailTrace_4035591
  have hstable : (prefixWord ++ tailWord_4035591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035591).length < 2 ^ (prefixWord ++ tailWord_4035591).sum := by decide
  have hdescent : baseEnd_4035591 < baseStart_4035591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035612 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 2, 3]
def baseStart_4035612 : Nat := 118140960795 + 4035612 * 2 ^ 59
def prefixEnd_4035612 : Nat := 4983230072969 + 3 ^ 40 * 4035612 * 2
def baseEnd_4035612 : Nat := 1381472460701579922127043

theorem tailTrace_4035612 : CollatzResearch.WordTrace tailWord_4035612 prefixEnd_4035612 1381472460701579922127043 := by
  unfold tailWord_4035612
  simp only [CollatzResearch.WordTrace]
  refine ⟨73595430927837213251246545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98127241237116284334995393 73595430927837213251246545)
  ·
    refine ⟨55196573195877909938434909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73595430927837213251246545 55196573195877909938434909)
    ·
      refine ⟨20698714948454216226913091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55196573195877909938434909 20698714948454216226913091)
      ·
        refine ⟨31048072422681324340369637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20698714948454216226913091 31048072422681324340369637)
        ·
          refine ⟨5821513579252748313819307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31048072422681324340369637 5821513579252748313819307)
          ·
            refine ⟨8732270368879122470728961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5821513579252748313819307 8732270368879122470728961)
            ·
              refine ⟨6549202776659341853046721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8732270368879122470728961 6549202776659341853046721)
              ·
                refine ⟨4911902082494506389785041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6549202776659341853046721 4911902082494506389785041)
                ·
                  refine ⟨3683926561870879792338781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4911902082494506389785041 3683926561870879792338781)
                  ·
                    refine ⟨1381472460701579922127043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683926561870879792338781 1381472460701579922127043)
                    ·
                      rfl

theorem cell22_4035612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_4035612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035612 prefixEnd_4035612 := by exact prefixLift 4035612
  have htrace : WordTrace (prefixWord ++ tailWord_4035612) baseStart_4035612 baseEnd_4035612 := by
    simpa [prefixWord, tailWord_4035612, baseEnd_4035612] using wordTrace_append hprefix tailTrace_4035612
  have hstable : (prefixWord ++ tailWord_4035612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035612).length < 2 ^ (prefixWord ++ tailWord_4035612).sum := by decide
  have hdescent : baseEnd_4035612 < baseStart_4035612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035621 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_4035621 : Nat := 118140960795 + 4035621 * 2 ^ 59
def prefixEnd_4035621 : Nat := 4983230072969 + 3 ^ 40 * 4035621 * 2
def baseEnd_4035621 : Nat := 1381475541585506898652015

theorem tailTrace_4035621 : CollatzResearch.WordTrace tailWord_4035621 prefixEnd_4035621 1381475541585506898652015 := by
  unfold tailWord_4035621
  simp only [CollatzResearch.WordTrace]
  refine ⟨147191190112641821039570717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98127460075094547359713811 147191190112641821039570717)
  ·
    refine ⟨55196696292240682889839019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147191190112641821039570717 55196696292240682889839019)
    ·
      refine ⟨82795044438361024334758529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55196696292240682889839019 82795044438361024334758529)
      ·
        refine ⟨62096283328770768251068897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82795044438361024334758529 62096283328770768251068897)
        ·
          refine ⟨46572212496578076188301673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62096283328770768251068897 46572212496578076188301673)
          ·
            refine ⟨34929159372433557141226255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46572212496578076188301673 34929159372433557141226255)
            ·
              refine ⟨52393739058650335711839383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34929159372433557141226255 52393739058650335711839383)
              ·
                refine ⟨78590608587975503567759075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52393739058650335711839383 78590608587975503567759075)
                ·
                  refine ⟨117885912881963255351638613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78590608587975503567759075 117885912881963255351638613)
                  ·
                    refine ⟨1381475541585506898652015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117885912881963255351638613 1381475541585506898652015)
                    ·
                      rfl

theorem cell22_4035621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_4035621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035621 prefixEnd_4035621 := by exact prefixLift 4035621
  have htrace : WordTrace (prefixWord ++ tailWord_4035621) baseStart_4035621 baseEnd_4035621 := by
    simpa [prefixWord, tailWord_4035621, baseEnd_4035621] using wordTrace_append hprefix tailTrace_4035621
  have hstable : (prefixWord ++ tailWord_4035621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035621).length < 2 ^ (prefixWord ++ tailWord_4035621).sum := by decide
  have hdescent : baseEnd_4035621 < baseStart_4035621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035640 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 3, 3]
def baseStart_4035640 : Nat := 118140960795 + 4035640 * 2 ^ 59
def prefixEnd_4035640 : Nat := 4983230072969 + 3 ^ 40 * 4035640 * 2
def baseEnd_4035640 : Nat := 1381482045673797182426957

theorem tailTrace_4035640 : CollatzResearch.WordTrace tailWord_4035640 prefixEnd_4035640 1381482045673797182426957 := by
  unfold tailWord_4035640
  simp only [CollatzResearch.WordTrace]
  refine ⟨73595941549786493642256187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98127922066381991523008249 73595941549786493642256187)
  ·
    refine ⟨110393912324679740463384281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73595941549786493642256187 110393912324679740463384281)
    ·
      refine ⟨82795434243509805347538211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110393912324679740463384281 82795434243509805347538211)
      ·
        refine ⟨124193151365264708021307317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82795434243509805347538211 124193151365264708021307317)
        ·
          refine ⟨11643107940493566376997561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124193151365264708021307317 11643107940493566376997561)
          ·
            refine ⟨8732330955370174782748171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11643107940493566376997561 8732330955370174782748171)
            ·
              refine ⟨13098496433055262174122257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8732330955370174782748171 13098496433055262174122257)
              ·
                refine ⟨9823872324791446630591693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13098496433055262174122257 9823872324791446630591693)
                ·
                  refine ⟨3683952121796792486471885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9823872324791446630591693 3683952121796792486471885)
                  ·
                    refine ⟨1381482045673797182426957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683952121796792486471885 1381482045673797182426957)
                    ·
                      rfl

theorem cell22_4035640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_4035640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035640 prefixEnd_4035640 := by exact prefixLift 4035640
  have htrace : WordTrace (prefixWord ++ tailWord_4035640) baseStart_4035640 baseEnd_4035640 := by
    simpa [prefixWord, tailWord_4035640, baseEnd_4035640] using wordTrace_append hprefix tailTrace_4035640
  have hstable : (prefixWord ++ tailWord_4035640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035640).length < 2 ^ (prefixWord ++ tailWord_4035640).sum := by decide
  have hdescent : baseEnd_4035640 < baseStart_4035640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035651 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 1, 7]
def baseStart_4035651 : Nat := 118140960795 + 4035651 * 2 ^ 59
def prefixEnd_4035651 : Nat := 4983230072969 + 3 ^ 40 * 4035651 * 2
def baseEnd_4035651 : Nat := 1381485811198596820401923

theorem tailTrace_4035651 : CollatzResearch.WordTrace tailWord_4035651 prefixEnd_4035651 1381485811198596820401923 := by
  unfold tailWord_4035651
  simp only [CollatzResearch.WordTrace]
  refine ⟨147192284302533136163162807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98128189535022090775441871 147192284302533136163162807)
  ·
    refine ⟨220788426453799704244744211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147192284302533136163162807 220788426453799704244744211)
    ·
      refine ⟨331182639680699556367116317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220788426453799704244744211 331182639680699556367116317)
      ·
        refine ⟨124193489880262333637668619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331182639680699556367116317 124193489880262333637668619)
        ·
          refine ⟨186290234820393500456502929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124193489880262333637668619 186290234820393500456502929)
          ·
            refine ⟨139717676115295125342377197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186290234820393500456502929 139717676115295125342377197)
            ·
              refine ⟨52394128543235672003391449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139717676115295125342377197 52394128543235672003391449)
              ·
                refine ⟨39295596407426754002543587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52394128543235672003391449 39295596407426754002543587)
                ·
                  refine ⟨58943394611140131003815381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39295596407426754002543587 58943394611140131003815381)
                  ·
                    refine ⟨1381485811198596820401923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58943394611140131003815381 1381485811198596820401923)
                    ·
                      rfl

theorem cell22_4035651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_4035651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035651 prefixEnd_4035651 := by exact prefixLift 4035651
  have htrace : WordTrace (prefixWord ++ tailWord_4035651) baseStart_4035651 baseEnd_4035651 := by
    simpa [prefixWord, tailWord_4035651, baseEnd_4035651] using wordTrace_append hprefix tailTrace_4035651
  have hstable : (prefixWord ++ tailWord_4035651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035651).length < 2 ^ (prefixWord ++ tailWord_4035651).sum := by decide
  have hdescent : baseEnd_4035651 < baseStart_4035651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035668 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_4035668 : Nat := 118140960795 + 4035668 * 2 ^ 59
def prefixEnd_4035668 : Nat := 4983230072969 + 3 ^ 40 * 4035668 * 2
def baseEnd_4035668 : Nat := 1381491630646014442726871

theorem tailTrace_4035668 : CollatzResearch.WordTrace tailWord_4035668 prefixEnd_4035668 1381491630646014442726871 := by
  unfold tailWord_4035668
  simp only [CollatzResearch.WordTrace]
  refine ⟨73596452171735774033265829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98128602895647698711021105 73596452171735774033265829)
  ·
    refine ⟨13799334782200457631237343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73596452171735774033265829 13799334782200457631237343)
    ·
      refine ⟨20699002173300686446856015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13799334782200457631237343 20699002173300686446856015)
      ·
        refine ⟨31048503259951029670284023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20699002173300686446856015 31048503259951029670284023)
        ·
          refine ⟨46572754889926544505426035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31048503259951029670284023 46572754889926544505426035)
          ·
            refine ⟨69859132334889816758139053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46572754889926544505426035 69859132334889816758139053)
            ·
              refine ⟨26197174625583681284302145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69859132334889816758139053 26197174625583681284302145)
              ·
                refine ⟨19647880969187760963226609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26197174625583681284302145 19647880969187760963226609)
                ·
                  refine ⟨14735910726890820722419957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19647880969187760963226609 14735910726890820722419957)
                  ·
                    refine ⟨1381491630646014442726871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14735910726890820722419957 1381491630646014442726871)
                    ·
                      rfl

theorem cell22_4035668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_4035668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035668 prefixEnd_4035668 := by exact prefixLift 4035668
  have htrace : WordTrace (prefixWord ++ tailWord_4035668) baseStart_4035668 baseEnd_4035668 := by
    simpa [prefixWord, tailWord_4035668, baseEnd_4035668] using wordTrace_append hprefix tailTrace_4035668
  have hstable : (prefixWord ++ tailWord_4035668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035668).length < 2 ^ (prefixWord ++ tailWord_4035668).sum := by decide
  have hdescent : baseEnd_4035668 < baseStart_4035668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035698 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_4035698 : Nat := 118140960795 + 4035698 * 2 ^ 59
def prefixEnd_4035698 : Nat := 4983230072969 + 3 ^ 40 * 4035698 * 2
def baseEnd_4035698 : Nat := 460500633419701454825593

theorem tailTrace_4035698 : CollatzResearch.WordTrace tailWord_4035698 prefixEnd_4035698 460500633419701454825593 := by
  unfold tailWord_4035698
  simp only [CollatzResearch.WordTrace]
  refine ⟨36798499633340715797530937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98129332355575242126749165 36798499633340715797530937)
  ·
    refine ⟨27598874725005536848148203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36798499633340715797530937 27598874725005536848148203)
    ·
      refine ⟨41398312087508305272222305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27598874725005536848148203 41398312087508305272222305)
      ·
        refine ⟨31048734065631228954166729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41398312087508305272222305 31048734065631228954166729)
        ·
          refine ⟨23286550549223421715625047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31048734065631228954166729 23286550549223421715625047)
          ·
            refine ⟨34929825823835132573437571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23286550549223421715625047 34929825823835132573437571)
            ·
              refine ⟨52394738735752698860156357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34929825823835132573437571 52394738735752698860156357)
              ·
                refine ⟨9824013512953631036279317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52394738735752698860156357 9824013512953631036279317)
                ·
                  refine ⟨460500633419701454825593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9824013512953631036279317 460500633419701454825593)
                  ·
                    rfl

theorem cell22_4035698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_4035698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035698 prefixEnd_4035698 := by exact prefixLift 4035698
  have htrace : WordTrace (prefixWord ++ tailWord_4035698) baseStart_4035698 baseEnd_4035698 := by
    simpa [prefixWord, tailWord_4035698, baseEnd_4035698] using wordTrace_append hprefix tailTrace_4035698
  have hstable : (prefixWord ++ tailWord_4035698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035698).length < 2 ^ (prefixWord ++ tailWord_4035698).sum := by decide
  have hdescent : baseEnd_4035698 < baseStart_4035698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035826 : List Nat := [3, 2, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_4035826 : Nat := 118140960795 + 4035826 * 2 ^ 59
def prefixEnd_4035826 : Nat := 4983230072969 + 3 ^ 40 * 4035826 * 2
def baseEnd_4035826 : Nat := 1381545717274954697276387

theorem tailTrace_4035826 : CollatzResearch.WordTrace tailWord_4035826 prefixEnd_4035826 1381545717274954697276387 := by
  unfold tailWord_4035826
  simp only [CollatzResearch.WordTrace]
  refine ⟨36799666769224785262695833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98132444717932760700522221 36799666769224785262695833)
  ·
    refine ⟨27599750076918588947021875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36799666769224785262695833 27599750076918588947021875)
    ·
      refine ⟨41399625115377883420532813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27599750076918588947021875 41399625115377883420532813)
      ·
        refine ⟨15524859418266706282699805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41399625115377883420532813 15524859418266706282699805)
        ·
          refine ⟨5821822281850014856012427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15524859418266706282699805 5821822281850014856012427)
          ·
            refine ⟨8732733422775022284018641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5821822281850014856012427 8732733422775022284018641)
            ·
              refine ⟨6549550067081266713013981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8732733422775022284018641 6549550067081266713013981)
              ·
                refine ⟨2456081275155475017380243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6549550067081266713013981 2456081275155475017380243)
                ·
                  refine ⟨3684121912733212526070365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456081275155475017380243 3684121912733212526070365)
                  ·
                    refine ⟨1381545717274954697276387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684121912733212526070365 1381545717274954697276387)
                    ·
                      rfl

theorem cell22_4035826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_4035826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035826 prefixEnd_4035826 := by exact prefixLift 4035826
  have htrace : WordTrace (prefixWord ++ tailWord_4035826) baseStart_4035826 baseEnd_4035826 := by
    simpa [prefixWord, tailWord_4035826, baseEnd_4035826] using wordTrace_append hprefix tailTrace_4035826
  have hstable : (prefixWord ++ tailWord_4035826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035826).length < 2 ^ (prefixWord ++ tailWord_4035826).sum := by decide
  have hdescent : baseEnd_4035826 < baseStart_4035826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035833 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 8]
def baseStart_4035833 : Nat := 118140960795 + 4035833 * 2 ^ 59
def prefixEnd_4035833 : Nat := 4983230072969 + 3 ^ 40 * 4035833 * 2
def baseEnd_4035833 : Nat := 460516037839336337450455

theorem tailTrace_4035833 : CollatzResearch.WordTrace tailWord_4035833 prefixEnd_4035833 460516037839336337450455 := by
  unfold tailWord_4035833
  simp only [CollatzResearch.WordTrace]
  refine ⟨147198922387873781246288153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98132614925249187497525435 147198922387873781246288153)
  ·
    refine ⟨110399191790905335934716115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147198922387873781246288153 110399191790905335934716115)
    ·
      refine ⟨165598787686358003902074173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110399191790905335934716115 165598787686358003902074173)
      ·
        refine ⟨62099545382384251463277815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165598787686358003902074173 62099545382384251463277815)
        ·
          refine ⟨93149318073576377194916723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62099545382384251463277815 93149318073576377194916723)
          ·
            refine ⟨139723977110364565792375085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93149318073576377194916723 139723977110364565792375085)
            ·
              refine ⟨52396491416386712172140657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139723977110364565792375085 52396491416386712172140657)
              ·
                refine ⟨39297368562290034129105493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52396491416386712172140657 39297368562290034129105493)
                ·
                  refine ⟨460516037839336337450455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39297368562290034129105493 460516037839336337450455)
                  ·
                    rfl

theorem cell22_4035833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_4035833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035833 prefixEnd_4035833 := by exact prefixLift 4035833
  have htrace : WordTrace (prefixWord ++ tailWord_4035833) baseStart_4035833 baseEnd_4035833 := by
    simpa [prefixWord, tailWord_4035833, baseEnd_4035833] using wordTrace_append hprefix tailTrace_4035833
  have hstable : (prefixWord ++ tailWord_4035833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035833).length < 2 ^ (prefixWord ++ tailWord_4035833).sum := by decide
  have hdescent : baseEnd_4035833 < baseStart_4035833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035869 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_4035869 : Nat := 118140960795 + 4035869 * 2 ^ 59
def prefixEnd_4035869 : Nat := 4983230072969 + 3 ^ 40 * 4035869 * 2
def baseEnd_4035869 : Nat := 1381560437053716918451255

theorem tailTrace_4035869 : CollatzResearch.WordTrace tailWord_4035869 prefixEnd_4035869 1381560437053716918451255 := by
  unfold tailWord_4035869
  simp only [CollatzResearch.WordTrace]
  refine ⟨147200235415743359394598661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98133490277162239596399107 147200235415743359394598661)
  ·
    refine ⟨27600044140451879886487249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147200235415743359394598661 27600044140451879886487249)
    ·
      refine ⟨20700033105338909914865437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27600044140451879886487249 20700033105338909914865437)
      ·
        refine ⟨7762512414502091218074539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20700033105338909914865437 7762512414502091218074539)
        ·
          refine ⟨11643768621753136827111809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7762512414502091218074539 11643768621753136827111809)
          ·
            refine ⟨8732826466314852620333857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11643768621753136827111809 8732826466314852620333857)
            ·
              refine ⟨6549619849736139465250393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8732826466314852620333857 6549619849736139465250393)
              ·
                refine ⟨4912214887302104598937795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6549619849736139465250393 4912214887302104598937795)
                ·
                  refine ⟨7368322330953156898406693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912214887302104598937795 7368322330953156898406693)
                  ·
                    refine ⟨1381560437053716918451255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7368322330953156898406693 1381560437053716918451255)
                    ·
                      rfl

theorem cell22_4035869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_4035869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035869 prefixEnd_4035869 := by exact prefixLift 4035869
  have htrace : WordTrace (prefixWord ++ tailWord_4035869) baseStart_4035869 baseEnd_4035869 := by
    simpa [prefixWord, tailWord_4035869, baseEnd_4035869] using wordTrace_append hprefix tailTrace_4035869
  have hstable : (prefixWord ++ tailWord_4035869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035869).length < 2 ^ (prefixWord ++ tailWord_4035869).sum := by decide
  have hdescent : baseEnd_4035869 < baseStart_4035869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035901 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 6]
def baseStart_4035901 : Nat := 118140960795 + 4035901 * 2 ^ 59
def prefixEnd_4035901 : Nat := 4983230072969 + 3 ^ 40 * 4035901 * 2
def baseEnd_4035901 : Nat := 460523797102559833883719

theorem tailTrace_4035901 : CollatzResearch.WordTrace tailWord_4035901 prefixEnd_4035901 460523797102559833883719 := by
  unfold tailWord_4035901
  simp only [CollatzResearch.WordTrace]
  refine ⟨147201402551627428859763557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98134268367751619239842371 147201402551627428859763557)
  ·
    refine ⟨27600262978430142911205667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147201402551627428859763557 27600262978430142911205667)
    ·
      refine ⟨41400394467645214366808501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27600262978430142911205667 41400394467645214366808501)
      ·
        refine ⟨3881286981341738846888297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41400394467645214366808501 3881286981341738846888297)
        ·
          refine ⟨2910965236006304135166223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3881286981341738846888297 2910965236006304135166223)
          ·
            refine ⟨4366447854009456202749335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910965236006304135166223 4366447854009456202749335)
            ·
              refine ⟨6549671781014184304124003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4366447854009456202749335 6549671781014184304124003)
              ·
                refine ⟨9824507671521276456186005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6549671781014184304124003 9824507671521276456186005)
                ·
                  refine ⟨460523797102559833883719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9824507671521276456186005 460523797102559833883719)
                  ·
                    rfl

theorem cell22_4035901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_4035901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035901 prefixEnd_4035901 := by exact prefixLift 4035901
  have htrace : WordTrace (prefixWord ++ tailWord_4035901) baseStart_4035901 baseEnd_4035901 := by
    simpa [prefixWord, tailWord_4035901, baseEnd_4035901] using wordTrace_append hprefix tailTrace_4035901
  have hstable : (prefixWord ++ tailWord_4035901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035901).length < 2 ^ (prefixWord ++ tailWord_4035901).sum := by decide
  have hdescent : baseEnd_4035901 < baseStart_4035901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035916 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 2, 3]
def baseStart_4035916 : Nat := 118140960795 + 4035916 * 2 ^ 59
def prefixEnd_4035916 : Nat := 4983230072969 + 3 ^ 40 * 4035916 * 2
def baseEnd_4035916 : Nat := 1381576526114224462526111

theorem tailTrace_4035916 : CollatzResearch.WordTrace tailWord_4035916 prefixEnd_4035916 1381576526114224462526111 := by
  unfold tailWord_4035916
  simp only [CollatzResearch.WordTrace]
  refine ⟨73600974823286543210779801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98134633097715390947706401 73600974823286543210779801)
  ·
    refine ⟨55200731117464907408084851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73600974823286543210779801 55200731117464907408084851)
    ·
      refine ⟨82801096676197361112127277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55200731117464907408084851 82801096676197361112127277)
      ·
        refine ⟨31050411253574010417047729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82801096676197361112127277 31050411253574010417047729)
        ·
          refine ⟨23287808440180507812785797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31050411253574010417047729 23287808440180507812785797)
          ·
            refine ⟨4366464082533845214897337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23287808440180507812785797 4366464082533845214897337)
            ·
              refine ⟨3274848061900383911173003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4366464082533845214897337 3274848061900383911173003)
              ·
                refine ⟨4912272092850575866759505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274848061900383911173003 4912272092850575866759505)
                ·
                  refine ⟨3684204069637931900069629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4912272092850575866759505 3684204069637931900069629)
                  ·
                    refine ⟨1381576526114224462526111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684204069637931900069629 1381576526114224462526111)
                    ·
                      rfl

theorem cell22_4035916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_4035916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035916 prefixEnd_4035916 := by exact prefixLift 4035916
  have htrace : WordTrace (prefixWord ++ tailWord_4035916) baseStart_4035916 baseEnd_4035916 := by
    simpa [prefixWord, tailWord_4035916, baseEnd_4035916] using wordTrace_append hprefix tailTrace_4035916
  have hstable : (prefixWord ++ tailWord_4035916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035916).length < 2 ^ (prefixWord ++ tailWord_4035916).sum := by decide
  have hdescent : baseEnd_4035916 < baseStart_4035916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035961 : List Nat := [1, 2, 1, 3, 2, 1, 6, 2, 1, 3]
def baseStart_4035961 : Nat := 118140960795 + 4035961 * 2 ^ 59
def prefixEnd_4035961 : Nat := 4983230072969 + 3 ^ 40 * 4035961 * 2
def baseEnd_4035961 : Nat := 1381591930533859345150973

theorem tailTrace_4035961 : CollatzResearch.WordTrace tailWord_4035961 prefixEnd_4035961 1381591930533859345150973 := by
  unfold tailWord_4035961
  simp only [CollatzResearch.WordTrace]
  refine ⟨147203590931410059106947737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98135727287606706071298491 147203590931410059106947737)
  ·
    refine ⟨110402693198557544330210803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147203590931410059106947737 110402693198557544330210803)
    ·
      refine ⟨165604039797836316495316205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110402693198557544330210803 165604039797836316495316205)
      ·
        refine ⟨62101514924188618685743577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165604039797836316495316205 62101514924188618685743577)
        ·
          refine ⟨46576136193141464014307683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62101514924188618685743577 46576136193141464014307683)
          ·
            refine ⟨69864204289712196021461525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46576136193141464014307683 69864204289712196021461525)
            ·
              refine ⟨3274884576080259188506009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69864204289712196021461525 3274884576080259188506009)
              ·
                refine ⟨2456163432060194391379507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274884576080259188506009 2456163432060194391379507)
                ·
                  refine ⟨3684245148090291587069261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456163432060194391379507 3684245148090291587069261)
                  ·
                    refine ⟨1381591930533859345150973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684245148090291587069261 1381591930533859345150973)
                    ·
                      rfl

theorem cell22_4035961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 1, 3].length) (baseStart_4035961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035961 prefixEnd_4035961 := by exact prefixLift 4035961
  have htrace : WordTrace (prefixWord ++ tailWord_4035961) baseStart_4035961 baseEnd_4035961 := by
    simpa [prefixWord, tailWord_4035961, baseEnd_4035961] using wordTrace_append hprefix tailTrace_4035961
  have hstable : (prefixWord ++ tailWord_4035961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035961).length < 2 ^ (prefixWord ++ tailWord_4035961).sum := by decide
  have hdescent : baseEnd_4035961 < baseStart_4035961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035972 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_4035972 : Nat := 118140960795 + 4035972 * 2 ^ 59
def prefixEnd_4035972 : Nat := 4983230072969 + 3 ^ 40 * 4035972 * 2
def baseEnd_4035972 : Nat := 1381595696058658983125939

theorem tailTrace_4035972 : CollatzResearch.WordTrace tailWord_4035972 prefixEnd_4035972 1381595696058658983125939 := by
  unfold tailWord_4035972
  simp only [CollatzResearch.WordTrace]
  refine ⟨73601996067185103992799085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98135994756246805323732113 73601996067185103992799085)
  ·
    refine ⟨27600748525194413997299657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73601996067185103992799085 27600748525194413997299657)
    ·
      refine ⟨20700561393895810497974743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27600748525194413997299657 20700561393895810497974743)
      ·
        refine ⟨31050842090843715746962115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20700561393895810497974743 31050842090843715746962115)
        ·
          refine ⟨46576263136265573620443173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31050842090843715746962115 46576263136265573620443173)
          ·
            refine ⟨8733049338049795053833095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46576263136265573620443173 8733049338049795053833095)
            ·
              refine ⟨13099574007074692580749643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8733049338049795053833095 13099574007074692580749643)
              ·
                refine ⟨19649361010612038871124465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13099574007074692580749643 19649361010612038871124465)
                ·
                  refine ⟨14737020757959029153343349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19649361010612038871124465 14737020757959029153343349)
                  ·
                    refine ⟨1381595696058658983125939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14737020757959029153343349 1381595696058658983125939)
                    ·
                      rfl

theorem cell22_4035972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_4035972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035972 prefixEnd_4035972 := by exact prefixLift 4035972
  have htrace : WordTrace (prefixWord ++ tailWord_4035972) baseStart_4035972 baseEnd_4035972 := by
    simpa [prefixWord, tailWord_4035972, baseEnd_4035972] using wordTrace_append hprefix tailTrace_4035972
  have hstable : (prefixWord ++ tailWord_4035972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035972).length < 2 ^ (prefixWord ++ tailWord_4035972).sum := by decide
  have hdescent : baseEnd_4035972 < baseStart_4035972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035985 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 6]
def baseStart_4035985 : Nat := 118140960795 + 4035985 * 2 ^ 59
def prefixEnd_4035985 : Nat := 4983230072969 + 3 ^ 40 * 4035985 * 2
def baseEnd_4035985 : Nat := 460533382074777094183633

theorem tailTrace_4035985 : CollatzResearch.WordTrace tailWord_4035985 prefixEnd_4035985 460533382074777094183633 := by
  unfold tailWord_4035985
  simp only [CollatzResearch.WordTrace]
  refine ⟨147204466283323111205821409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98136310855548740803880939 147204466283323111205821409)
  ·
    refine ⟨110403349712492333404366057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147204466283323111205821409 110403349712492333404366057)
    ·
      refine ⟨82802512284369250053274543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110403349712492333404366057 82802512284369250053274543)
      ·
        refine ⟨124203768426553875079911815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82802512284369250053274543 124203768426553875079911815)
        ·
          refine ⟨186305652639830812619867723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124203768426553875079911815 186305652639830812619867723)
          ·
            refine ⟨279458478959746218929801585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186305652639830812619867723 279458478959746218929801585)
            ·
              refine ⟨209593859219809664197351189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279458478959746218929801585 209593859219809664197351189)
              ·
                refine ⟨9824712150928578009250837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209593859219809664197351189 9824712150928578009250837)
                ·
                  refine ⟨460533382074777094183633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9824712150928578009250837 460533382074777094183633)
                  ·
                    rfl

theorem cell22_4035985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_4035985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4035985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4035985 prefixEnd_4035985 := by exact prefixLift 4035985
  have htrace : WordTrace (prefixWord ++ tailWord_4035985) baseStart_4035985 baseEnd_4035985 := by
    simpa [prefixWord, tailWord_4035985, baseEnd_4035985] using wordTrace_append hprefix tailTrace_4035985
  have hstable : (prefixWord ++ tailWord_4035985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035985).length < 2 ^ (prefixWord ++ tailWord_4035985).sum := by decide
  have hdescent : baseEnd_4035985 < baseStart_4035985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036008 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 5]
def baseStart_4036008 : Nat := 118140960795 + 4036008 * 2 ^ 59
def prefixEnd_4036008 : Nat := 4983230072969 + 3 ^ 40 * 4036008 * 2
def baseEnd_4036008 : Nat := 460536006531455629741943

theorem tailTrace_4036008 : CollatzResearch.WordTrace tailWord_4036008 prefixEnd_4036008 460536006531455629741943 := by
  unfold tailWord_4036008
  simp only [CollatzResearch.WordTrace]
  refine ⟨73602652581119893066954339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98136870108159857422605785 73602652581119893066954339)
  ·
    refine ⟨110403978871679839600431509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73602652581119893066954339 110403978871679839600431509)
    ·
      refine ⟨5175186509609992481270227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110403978871679839600431509 5175186509609992481270227)
      ·
        refine ⟨7762779764414988721905341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5175186509609992481270227 7762779764414988721905341)
        ·
          refine ⟨2911042411655620770714503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7762779764414988721905341 2911042411655620770714503)
          ·
            refine ⟨4366563617483431156071755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911042411655620770714503 4366563617483431156071755)
            ·
              refine ⟨6549845426225146734107633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4366563617483431156071755 6549845426225146734107633)
              ·
                refine ⟨4912384069668860050580725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6549845426225146734107633 4912384069668860050580725)
                ·
                  refine ⟨460536006531455629741943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4912384069668860050580725 460536006531455629741943)
                  ·
                    rfl

theorem cell22_4036008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 5].length) (baseStart_4036008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036008 prefixEnd_4036008 := by exact prefixLift 4036008
  have htrace : WordTrace (prefixWord ++ tailWord_4036008) baseStart_4036008 baseEnd_4036008 := by
    simpa [prefixWord, tailWord_4036008, baseEnd_4036008] using wordTrace_append hprefix tailTrace_4036008
  have hstable : (prefixWord ++ tailWord_4036008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036008).length < 2 ^ (prefixWord ++ tailWord_4036008).sum := by decide
  have hdescent : baseEnd_4036008 < baseStart_4036008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036047 : List Nat := [1, 1, 2, 1, 1, 4, 6, 6]
def baseStart_4036047 : Nat := 118140960795 + 4036047 * 2 ^ 59
def prefixEnd_4036047 : Nat := 4983230072969 + 3 ^ 40 * 4036047 * 2
def baseEnd_4036047 : Nat := 153513485565709309722301

theorem tailTrace_4036047 : CollatzResearch.WordTrace tailWord_4036047 prefixEnd_4036047 153513485565709309722301 := by
  unfold tailWord_4036047
  simp only [CollatzResearch.WordTrace]
  refine ⟨147206727609098495794578395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98137818406065663863052263 147206727609098495794578395)
  ·
    refine ⟨220810091413647743691867593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147206727609098495794578395 220810091413647743691867593)
    ·
      refine ⟨165607568560235807768900695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220810091413647743691867593 165607568560235807768900695)
      ·
        refine ⟨248411352840353711653351043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165607568560235807768900695 248411352840353711653351043)
        ·
          refine ⟨372617029260530567480026565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248411352840353711653351043 372617029260530567480026565)
          ·
            refine ⟨69865692986349481402504981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372617029260530567480026565 69865692986349481402504981)
            ·
              refine ⟨3274954358735131940742421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69865692986349481402504981 3274954358735131940742421)
              ·
                refine ⟨153513485565709309722301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3274954358735131940742421 153513485565709309722301)
                ·
                  rfl

theorem cell22_4036047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 6].length) (baseStart_4036047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036047 prefixEnd_4036047 := by exact prefixLift 4036047
  have htrace : WordTrace (prefixWord ++ tailWord_4036047) baseStart_4036047 baseEnd_4036047 := by
    simpa [prefixWord, tailWord_4036047, baseEnd_4036047] using wordTrace_append hprefix tailTrace_4036047
  have hstable : (prefixWord ++ tailWord_4036047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036047).length < 2 ^ (prefixWord ++ tailWord_4036047).sum := by decide
  have hdescent : baseEnd_4036047 < baseStart_4036047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036079 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 3, 3]
def baseStart_4036079 : Nat := 118140960795 + 4036079 * 2 ^ 59
def prefixEnd_4036079 : Nat := 4983230072969 + 3 ^ 40 * 4036079 * 2
def baseEnd_4036079 : Nat := 1381632324345346370700611

theorem tailTrace_4036079 : CollatzResearch.WordTrace tailWord_4036079 prefixEnd_4036079 1381632324345346370700611 := by
  unfold tailWord_4036079
  simp only [CollatzResearch.WordTrace]
  refine ⟨147207894744982565259743291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98138596496655043506495527 147207894744982565259743291)
  ·
    refine ⟨220811842117473847889614937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147207894744982565259743291 220811842117473847889614937)
    ·
      refine ⟨165608881588105385917211203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220811842117473847889614937 165608881588105385917211203)
      ·
        refine ⟨248413322382158078875816805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165608881588105385917211203 248413322382158078875816805)
        ·
          refine ⟨46577497946654639789215651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248413322382158078875816805 46577497946654639789215651)
          ·
            refine ⟨69866246919981959683823477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46577497946654639789215651 69866246919981959683823477)
            ·
              refine ⟨6549960648748308720358451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69866246919981959683823477 6549960648748308720358451)
              ·
                refine ⟨9824940973122463080537677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6549960648748308720358451 9824940973122463080537677)
                ·
                  refine ⟨3684352864920923655201629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9824940973122463080537677 3684352864920923655201629)
                  ·
                    refine ⟨1381632324345346370700611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684352864920923655201629 1381632324345346370700611)
                    ·
                      rfl

theorem cell22_4036079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 3].length) (baseStart_4036079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036079 prefixEnd_4036079 := by exact prefixLift 4036079
  have htrace : WordTrace (prefixWord ++ tailWord_4036079) baseStart_4036079 baseEnd_4036079 := by
    simpa [prefixWord, tailWord_4036079, baseEnd_4036079] using wordTrace_append hprefix tailTrace_4036079
  have hstable : (prefixWord ++ tailWord_4036079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036079).length < 2 ^ (prefixWord ++ tailWord_4036079).sum := by decide
  have hdescent : baseEnd_4036079 < baseStart_4036079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036085 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 2, 3]
def baseStart_4036085 : Nat := 118140960795 + 4036085 * 2 ^ 59
def prefixEnd_4036085 : Nat := 4983230072969 + 3 ^ 40 * 4036085 * 2
def baseEnd_4036085 : Nat := 1381634378267964355050593

theorem tailTrace_4036085 : CollatzResearch.WordTrace tailWord_4036085 prefixEnd_4036085 1381634378267964355050593 := by
  unfold tailWord_4036085
  simp only [CollatzResearch.WordTrace]
  refine ⟨147208113582960828284461709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98138742388640552189641139 147208113582960828284461709)
  ·
    refine ⟨55203042593610310606673141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147208113582960828284461709 55203042593610310606673141)
    ·
      refine ⟨5175285243150966619375607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55203042593610310606673141 5175285243150966619375607)
      ·
        refine ⟨7762927864726449929063411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5175285243150966619375607 7762927864726449929063411)
        ·
          refine ⟨11644391797089674893595117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7762927864726449929063411 11644391797089674893595117)
          ·
            refine ⟨4366646923908628085098169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11644391797089674893595117 4366646923908628085098169)
            ·
              refine ⟨3274985192931471063823627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4366646923908628085098169 3274985192931471063823627)
              ·
                refine ⟨4912477789397206595735441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274985192931471063823627 4912477789397206595735441)
                ·
                  refine ⟨3684358342047904946801581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4912477789397206595735441 3684358342047904946801581)
                  ·
                    refine ⟨1381634378267964355050593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684358342047904946801581 1381634378267964355050593)
                    ·
                      rfl

theorem cell22_4036085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_4036085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036085 prefixEnd_4036085 := by exact prefixLift 4036085
  have htrace : WordTrace (prefixWord ++ tailWord_4036085) baseStart_4036085 baseEnd_4036085 := by
    simpa [prefixWord, tailWord_4036085, baseEnd_4036085] using wordTrace_append hprefix tailTrace_4036085
  have hstable : (prefixWord ++ tailWord_4036085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036085).length < 2 ^ (prefixWord ++ tailWord_4036085).sum := by decide
  have hdescent : baseEnd_4036085 < baseStart_4036085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036173 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_4036173 : Nat := 118140960795 + 4036173 * 2 ^ 59
def prefixEnd_4036173 : Nat := 4983230072969 + 3 ^ 40 * 4036173 * 2
def baseEnd_4036173 : Nat := 1381664502466361458850323

theorem tailTrace_4036173 : CollatzResearch.WordTrace tailWord_4036173 prefixEnd_4036173 1381664502466361458850323 := by
  unfold tailWord_4036173
  simp only [CollatzResearch.WordTrace]
  refine ⟨147211323206642019313665173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98140882137761346209110115 147211323206642019313665173)
  ·
    refine ⟨6900530775311344655328055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 147211323206642019313665173 6900530775311344655328055)
    ·
      refine ⟨10350796162967016982992083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6900530775311344655328055 10350796162967016982992083)
      ·
        refine ⟨15526194244450525474488125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10350796162967016982992083 15526194244450525474488125)
        ·
          refine ⟨5822322841668947052933047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15526194244450525474488125 5822322841668947052933047)
          ·
            refine ⟨8733484262503420579399571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5822322841668947052933047 8733484262503420579399571)
            ·
              refine ⟨13100226393755130869099357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8733484262503420579399571 13100226393755130869099357)
              ·
                refine ⟨4912584897658174075912259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13100226393755130869099357 4912584897658174075912259)
                ·
                  refine ⟨7368877346487261113868389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912584897658174075912259 7368877346487261113868389)
                  ·
                    refine ⟨1381664502466361458850323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7368877346487261113868389 1381664502466361458850323)
                    ·
                      rfl

theorem cell22_4036173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_4036173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036173 prefixEnd_4036173 := by exact prefixLift 4036173
  have htrace : WordTrace (prefixWord ++ tailWord_4036173) baseStart_4036173 baseEnd_4036173 := by
    simpa [prefixWord, tailWord_4036173, baseEnd_4036173] using wordTrace_append hprefix tailTrace_4036173
  have hstable : (prefixWord ++ tailWord_4036173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036173).length < 2 ^ (prefixWord ++ tailWord_4036173).sum := by decide
  have hdescent : baseEnd_4036173 < baseStart_4036173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036248 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 3, 3]
def baseStart_4036248 : Nat := 118140960795 + 4036248 * 2 ^ 59
def prefixEnd_4036248 : Nat := 4983230072969 + 3 ^ 40 * 4036248 * 2
def baseEnd_4036248 : Nat := 1381690176499086263225093

theorem tailTrace_4036248 : CollatzResearch.WordTrace tailWord_4036248 prefixEnd_4036248 1381690176499086263225093 := by
  unfold tailWord_4036248
  simp only [CollatzResearch.WordTrace]
  refine ⟨73607029340685153561322699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98142705787580204748430265 73607029340685153561322699)
  ·
    refine ⟨110410544011027730341984049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73607029340685153561322699 110410544011027730341984049)
    ·
      refine ⟨82807908008270797756488037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110410544011027730341984049 82807908008270797756488037)
      ·
        refine ⟨15526482751550774579341507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82807908008270797756488037 15526482751550774579341507)
        ·
          refine ⟨23289724127326161869012261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15526482751550774579341507 23289724127326161869012261)
          ·
            refine ⟨4366823273873655350439799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23289724127326161869012261 4366823273873655350439799)
            ·
              refine ⟨6550234910810483025659699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4366823273873655350439799 6550234910810483025659699)
              ·
                refine ⟨9825352366215724538489549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6550234910810483025659699 9825352366215724538489549)
                ·
                  refine ⟨3684507137330896701933581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9825352366215724538489549 3684507137330896701933581)
                  ·
                    refine ⟨1381690176499086263225093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684507137330896701933581 1381690176499086263225093)
                    ·
                      rfl

theorem cell22_4036248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_4036248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036248 prefixEnd_4036248 := by exact prefixLift 4036248
  have htrace : WordTrace (prefixWord ++ tailWord_4036248) baseStart_4036248 baseEnd_4036248 := by
    simpa [prefixWord, tailWord_4036248, baseEnd_4036248] using wordTrace_append hprefix tailTrace_4036248
  have hstable : (prefixWord ++ tailWord_4036248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036248).length < 2 ^ (prefixWord ++ tailWord_4036248).sum := by decide
  have hdescent : baseEnd_4036248 < baseStart_4036248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036261 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 5]
def baseStart_4036261 : Nat := 118140960795 + 4036261 * 2 ^ 59
def prefixEnd_4036261 : Nat := 4983230072969 + 3 ^ 40 * 4036261 * 2
def baseEnd_4036261 : Nat := 460564875554919520883351

theorem tailTrace_4036261 : CollatzResearch.WordTrace tailWord_4036261 prefixEnd_4036261 460564875554919520883351 := by
  unfold tailWord_4036261
  simp only [CollatzResearch.WordTrace]
  refine ⟨147214532830323210342868637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98143021886882140228579091 147214532830323210342868637)
  ·
    refine ⟨55205449811371203878575739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147214532830323210342868637 55205449811371203878575739)
    ·
      refine ⟨82808174717056805817863609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55205449811371203878575739 82808174717056805817863609)
      ·
        refine ⟨62106131037792604363397707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82808174717056805817863609 62106131037792604363397707)
        ·
          refine ⟨93159196556688906545096561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62106131037792604363397707 93159196556688906545096561)
          ·
            refine ⟨69869397417516679908822421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93159196556688906545096561 69869397417516679908822421)
            ·
              refine ⟨3275128003946094370726051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69869397417516679908822421 3275128003946094370726051)
              ·
                refine ⟨4912692005919141556089077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275128003946094370726051 4912692005919141556089077)
                ·
                  refine ⟨460564875554919520883351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4912692005919141556089077 460564875554919520883351)
                  ·
                    rfl

theorem cell22_4036261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_4036261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036261 prefixEnd_4036261 := by exact prefixLift 4036261
  have htrace : WordTrace (prefixWord ++ tailWord_4036261) baseStart_4036261 baseEnd_4036261 := by
    simpa [prefixWord, tailWord_4036261, baseEnd_4036261] using wordTrace_append hprefix tailTrace_4036261
  have hstable : (prefixWord ++ tailWord_4036261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036261).length < 2 ^ (prefixWord ++ tailWord_4036261).sum := by decide
  have hdescent : baseEnd_4036261 < baseStart_4036261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036310 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_4036310 : Nat := 118140960795 + 4036310 * 2 ^ 59
def prefixEnd_4036310 : Nat := 4983230072969 + 3 ^ 40 * 4036310 * 2
def baseEnd_4036310 : Nat := 1381711400366138768174903

theorem tailTrace_4036310 : CollatzResearch.WordTrace tailWord_4036310 prefixEnd_4036310 1381711400366138768174903 := by
  unfold tailWord_4036310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9201020000446605731962649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98144213338097127807601589 9201020000446605731962649)
  ·
    refine ⟨6900765000334954298971987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9201020000446605731962649 6900765000334954298971987)
    ·
      refine ⟨10351147500502431448457981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6900765000334954298971987 10351147500502431448457981)
      ·
        refine ⟨3881680312688411793171743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10351147500502431448457981 3881680312688411793171743)
        ·
          refine ⟨5822520469032617689757615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3881680312688411793171743 5822520469032617689757615)
          ·
            refine ⟨8733780703548926534636423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5822520469032617689757615 8733780703548926534636423)
            ·
              refine ⟨13100671055323389801954635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8733780703548926534636423 13100671055323389801954635)
              ·
                refine ⟨19651006582985084702931953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13100671055323389801954635 19651006582985084702931953)
                ·
                  refine ⟨14738254937238813527198965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19651006582985084702931953 14738254937238813527198965)
                  ·
                    refine ⟨1381711400366138768174903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14738254937238813527198965 1381711400366138768174903)
                    ·
                      rfl

theorem cell22_4036310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_4036310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036310 prefixEnd_4036310 := by exact prefixLift 4036310
  have htrace : WordTrace (prefixWord ++ tailWord_4036310) baseStart_4036310 baseEnd_4036310 := by
    simpa [prefixWord, tailWord_4036310, baseEnd_4036310] using wordTrace_append hprefix tailTrace_4036310
  have hstable : (prefixWord ++ tailWord_4036310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036310).length < 2 ^ (prefixWord ++ tailWord_4036310).sum := by decide
  have hdescent : baseEnd_4036310 < baseStart_4036310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036319 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 1, 6]
def baseStart_4036319 : Nat := 118140960795 + 4036319 * 2 ^ 59
def prefixEnd_4036319 : Nat := 4983230072969 + 3 ^ 40 * 4036319 * 2
def baseEnd_4036319 : Nat := 1381714481250065744699875

theorem tailTrace_4036319 : CollatzResearch.WordTrace tailWord_4036319 prefixEnd_4036319 1381714481250065744699875 := by
  unfold tailWord_4036319
  simp only [CollatzResearch.WordTrace]
  refine ⟨147216648264113086248480011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98144432176075390832320007 147216648264113086248480011)
  ·
    refine ⟨220824972396169629372720017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147216648264113086248480011 220824972396169629372720017)
    ·
      refine ⟨165618729297127222029540013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220824972396169629372720017 165618729297127222029540013)
      ·
        refine ⟨62107023486422708261077505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165618729297127222029540013 62107023486422708261077505)
        ·
          refine ⟨46580267614817031195808129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62107023486422708261077505 46580267614817031195808129)
          ·
            refine ⟨34935200711112773396856097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46580267614817031195808129 34935200711112773396856097)
            ·
              refine ⟨26201400533334580047642073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34935200711112773396856097 26201400533334580047642073)
              ·
                refine ⟨19651050400000935035731555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26201400533334580047642073 19651050400000935035731555)
                ·
                  refine ⟨29476575600001402553597333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19651050400000935035731555 29476575600001402553597333)
                  ·
                    refine ⟨1381714481250065744699875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29476575600001402553597333 1381714481250065744699875)
                    ·
                      rfl

theorem cell22_4036319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_4036319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036319 prefixEnd_4036319 := by exact prefixLift 4036319
  have htrace : WordTrace (prefixWord ++ tailWord_4036319) baseStart_4036319 baseEnd_4036319 := by
    simpa [prefixWord, tailWord_4036319, baseEnd_4036319] using wordTrace_append hprefix tailTrace_4036319
  have hstable : (prefixWord ++ tailWord_4036319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036319).length < 2 ^ (prefixWord ++ tailWord_4036319).sum := by decide
  have hdescent : baseEnd_4036319 < baseStart_4036319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036364 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_4036364 : Nat := 118140960795 + 4036364 * 2 ^ 59
def prefixEnd_4036364 : Nat := 4983230072969 + 3 ^ 40 * 4036364 * 2
def baseEnd_4036364 : Nat := 1381729885669700627324737

theorem tailTrace_4036364 : CollatzResearch.WordTrace tailWord_4036364 prefixEnd_4036364 1381729885669700627324737 := by
  unfold tailWord_4036364
  simp only [CollatzResearch.WordTrace]
  refine ⟨73609144774475029466934073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98145526365966705955912097 73609144774475029466934073)
  ·
    refine ⟨55206858580856272100200555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73609144774475029466934073 55206858580856272100200555)
    ·
      refine ⟨82810287871284408150300833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55206858580856272100200555 82810287871284408150300833)
      ·
        refine ⟨62107715903463306112725625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82810287871284408150300833 62107715903463306112725625)
        ·
          refine ⟨46580786927597479584544219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62107715903463306112725625 46580786927597479584544219)
          ·
            refine ⟨69871180391396219376816329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46580786927597479584544219 69871180391396219376816329)
            ·
              refine ⟨52403385293547164532612247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69871180391396219376816329 52403385293547164532612247)
              ·
                refine ⟨78605077940320746798918371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52403385293547164532612247 78605077940320746798918371)
                ·
                  refine ⟨117907616910481120198377557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78605077940320746798918371 117907616910481120198377557)
                  ·
                    refine ⟨1381729885669700627324737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117907616910481120198377557 1381729885669700627324737)
                    ·
                      rfl

theorem cell22_4036364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_4036364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036364 prefixEnd_4036364 := by exact prefixLift 4036364
  have htrace : WordTrace (prefixWord ++ tailWord_4036364) baseStart_4036364 baseEnd_4036364 := by
    simpa [prefixWord, tailWord_4036364, baseEnd_4036364] using wordTrace_append hprefix tailTrace_4036364
  have hstable : (prefixWord ++ tailWord_4036364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036364).length < 2 ^ (prefixWord ++ tailWord_4036364).sum := by decide
  have hdescent : baseEnd_4036364 < baseStart_4036364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036426 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_4036426 : Nat := 118140960795 + 4036426 * 2 ^ 59
def prefixEnd_4036426 : Nat := 4983230072969 + 3 ^ 40 * 4036426 * 2
def baseEnd_4036426 : Nat := 1381751109536753132274547

theorem tailTrace_4036426 : CollatzResearch.WordTrace tailWord_4036426 prefixEnd_4036426 1381751109536753132274547 := by
  unfold tailWord_4036426
  simp only [CollatzResearch.WordTrace]
  refine ⟨36805137718681360880656283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98147033916483629015083421 36805137718681360880656283)
  ·
    refine ⟨55207706578022041320984425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36805137718681360880656283 55207706578022041320984425)
    ·
      refine ⟨41405779933516530990738319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55207706578022041320984425 41405779933516530990738319)
      ·
        refine ⟨62108669900274796486107479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41405779933516530990738319 62108669900274796486107479)
        ·
          refine ⟨93163004850412194729161219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62108669900274796486107479 93163004850412194729161219)
          ·
            refine ⟨139744507275618292093741829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93163004850412194729161219 139744507275618292093741829)
            ·
              refine ⟨26202095114178429767576593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139744507275618292093741829 26202095114178429767576593)
              ·
                refine ⟨19651571335633822325682445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26202095114178429767576593 19651571335633822325682445)
                ·
                  refine ⟨7369339250862683372130917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19651571335633822325682445 7369339250862683372130917)
                  ·
                    refine ⟨1381751109536753132274547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7369339250862683372130917 1381751109536753132274547)
                    ·
                      rfl

theorem cell22_4036426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_4036426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036426 prefixEnd_4036426 := by exact prefixLift 4036426
  have htrace : WordTrace (prefixWord ++ tailWord_4036426) baseStart_4036426 baseEnd_4036426 := by
    simpa [prefixWord, tailWord_4036426, baseEnd_4036426] using wordTrace_append hprefix tailTrace_4036426
  have hstable : (prefixWord ++ tailWord_4036426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036426).length < 2 ^ (prefixWord ++ tailWord_4036426).sum := by decide
  have hdescent : baseEnd_4036426 < baseStart_4036426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036460 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 1, 4]
def baseStart_4036460 : Nat := 118140960795 + 4036460 * 2 ^ 59
def prefixEnd_4036460 : Nat := 4983230072969 + 3 ^ 40 * 4036460 * 2
def baseEnd_4036460 : Nat := 1381762748431588376924443

theorem tailTrace_4036460 : CollatzResearch.WordTrace tailWord_4036460 prefixEnd_4036460 1381762748431588376924443 := by
  unfold tailWord_4036460
  simp only [CollatzResearch.WordTrace]
  refine ⟨73610895478301133664681417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98147860637734844886241889 73610895478301133664681417)
  ·
    refine ⟨55208171608725850248511063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73610895478301133664681417 55208171608725850248511063)
    ·
      refine ⟨82812257413088775372766595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55208171608725850248511063 82812257413088775372766595)
      ·
        refine ⟨124218386119633163059149893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82812257413088775372766595 124218386119633163059149893)
        ·
          refine ⟨23290947397431218073590605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124218386119633163059149893 23290947397431218073590605)
          ·
            refine ⟨8734105274036706777596477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23290947397431218073590605 8734105274036706777596477)
            ·
              refine ⟨3275289477763765041598679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8734105274036706777596477 3275289477763765041598679)
              ·
                refine ⟨4912934216645647562398019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275289477763765041598679 4912934216645647562398019)
                ·
                  refine ⟨7369401324968471343597029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912934216645647562398019 7369401324968471343597029)
                  ·
                    refine ⟨1381762748431588376924443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7369401324968471343597029 1381762748431588376924443)
                    ·
                      rfl

theorem cell22_4036460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_4036460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036460 prefixEnd_4036460 := by exact prefixLift 4036460
  have htrace : WordTrace (prefixWord ++ tailWord_4036460) baseStart_4036460 baseEnd_4036460 := by
    simpa [prefixWord, tailWord_4036460, baseEnd_4036460] using wordTrace_append hprefix tailTrace_4036460
  have hstable : (prefixWord ++ tailWord_4036460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036460).length < 2 ^ (prefixWord ++ tailWord_4036460).sum := by decide
  have hdescent : baseEnd_4036460 < baseStart_4036460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036490 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_4036490 : Nat := 118140960795 + 4036490 * 2 ^ 59
def prefixEnd_4036490 : Nat := 4983230072969 + 3 ^ 40 * 4036490 * 2
def baseEnd_4036490 : Nat := 1381773018044678298674351

theorem tailTrace_4036490 : CollatzResearch.WordTrace tailWord_4036490 prefixEnd_4036490 1381773018044678298674351 := by
  unfold tailWord_4036490
  simp only [CollatzResearch.WordTrace]
  refine ⟨36805721286623395613238731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98148590097662388301969949 36805721286623395613238731)
  ·
    refine ⟨55208581929935093419858097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36805721286623395613238731 55208581929935093419858097)
    ·
      refine ⟨41406436447451320064893573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55208581929935093419858097 41406436447451320064893573)
      ·
        refine ⟨7763706833897122512167545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41406436447451320064893573 7763706833897122512167545)
        ·
          refine ⟨5822780125422841884125659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7763706833897122512167545 5822780125422841884125659)
          ·
            refine ⟨8734170188134262826188489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5822780125422841884125659 8734170188134262826188489)
            ·
              refine ⟨6550627641100697119641367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8734170188134262826188489 6550627641100697119641367)
              ·
                refine ⟨9825941461651045679462051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6550627641100697119641367 9825941461651045679462051)
                ·
                  refine ⟨14738912192476568519193077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9825941461651045679462051 14738912192476568519193077)
                  ·
                    refine ⟨1381773018044678298674351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14738912192476568519193077 1381773018044678298674351)
                    ·
                      rfl

theorem cell22_4036490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_4036490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036490 prefixEnd_4036490 := by exact prefixLift 4036490
  have htrace : WordTrace (prefixWord ++ tailWord_4036490) baseStart_4036490 baseEnd_4036490 := by
    simpa [prefixWord, tailWord_4036490, baseEnd_4036490] using wordTrace_append hprefix tailTrace_4036490
  have hstable : (prefixWord ++ tailWord_4036490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036490).length < 2 ^ (prefixWord ++ tailWord_4036490).sum := by decide
  have hdescent : baseEnd_4036490 < baseStart_4036490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036503 : List Nat := [1, 1, 3, 3, 1, 4, 3, 6]
def baseStart_4036503 : Nat := 118140960795 + 4036503 * 2 ^ 59
def prefixEnd_4036503 : Nat := 4983230072969 + 3 ^ 40 * 4036503 * 2
def baseEnd_4036503 : Nat := 153530829801150066455479

theorem tailTrace_4036503 : CollatzResearch.WordTrace tailWord_4036503 prefixEnd_4036503 153530829801150066455479 := by
  unfold tailWord_4036503
  simp only [CollatzResearch.WordTrace]
  refine ⟨147223359295446485673178163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98148906196964323782118775 147223359295446485673178163)
  ·
    refine ⟨220835038943169728509767245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147223359295446485673178163 220835038943169728509767245)
    ·
      refine ⟨82813139603688648191162717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220835038943169728509767245 82813139603688648191162717)
      ·
        refine ⟨31054927351383243071686019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82813139603688648191162717 31054927351383243071686019)
        ·
          refine ⟨46582391027074864607529029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31054927351383243071686019 46582391027074864607529029)
          ·
            refine ⟨8734198317576537113911693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46582391027074864607529029 8734198317576537113911693)
            ·
              refine ⟨3275324369091201417716885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8734198317576537113911693 3275324369091201417716885)
              ·
                refine ⟨153530829801150066455479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3275324369091201417716885 153530829801150066455479)
                ·
                  rfl

theorem cell22_4036503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 6].length) (baseStart_4036503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036503 prefixEnd_4036503 := by exact prefixLift 4036503
  have htrace : WordTrace (prefixWord ++ tailWord_4036503) baseStart_4036503 baseEnd_4036503 := by
    simpa [prefixWord, tailWord_4036503, baseEnd_4036503] using wordTrace_append hprefix tailTrace_4036503
  have hstable : (prefixWord ++ tailWord_4036503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036503).length < 2 ^ (prefixWord ++ tailWord_4036503).sum := by decide
  have hdescent : baseEnd_4036503 < baseStart_4036503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036520 : List Nat := [2, 1, 6, 2, 1, 1, 9]
def baseStart_4036520 : Nat := 118140960795 + 4036520 * 2 ^ 59
def prefixEnd_4036520 : Nat := 4983230072969 + 3 ^ 40 * 4036520 * 2
def baseEnd_4036520 : Nat := 51177158802139563719417

theorem tailTrace_4036520 : CollatzResearch.WordTrace tailWord_4036520 prefixEnd_4036520 51177158802139563719417 := by
  unfold tailWord_4036520
  simp only [CollatzResearch.WordTrace]
  refine ⟨73611989668192448788273507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98149319557589931717698009 73611989668192448788273507)
  ·
    refine ⟨110417984502288673182410261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73611989668192448788273507 110417984502288673182410261)
    ·
      refine ⟨5175843023544781555425481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110417984502288673182410261 5175843023544781555425481)
      ·
        refine ⟨3881882267658586166569111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5175843023544781555425481 3881882267658586166569111)
        ·
          refine ⟨5822823401487879249853667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3881882267658586166569111 5822823401487879249853667)
          ·
            refine ⟨8734235102231818874780501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5822823401487879249853667 8734235102231818874780501)
            ·
              refine ⟨51177158802139563719417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8734235102231818874780501 51177158802139563719417)
              ·
                rfl

theorem cell22_4036520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 9].length) (baseStart_4036520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036520 prefixEnd_4036520 := by exact prefixLift 4036520
  have htrace : WordTrace (prefixWord ++ tailWord_4036520) baseStart_4036520 baseEnd_4036520 := by
    simpa [prefixWord, tailWord_4036520, baseEnd_4036520] using wordTrace_append hprefix tailTrace_4036520
  have hstable : (prefixWord ++ tailWord_4036520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036520).length < 2 ^ (prefixWord ++ tailWord_4036520).sum := by decide
  have hdescent : baseEnd_4036520 < baseStart_4036520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036531 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 7]
def baseStart_4036531 : Nat := 118140960795 + 4036531 * 2 ^ 59
def prefixEnd_4036531 : Nat := 4983230072969 + 3 ^ 40 * 4036531 * 2
def baseEnd_4036531 : Nat := 460595684394189286133075

theorem tailTrace_4036531 : CollatzResearch.WordTrace tailWord_4036531 prefixEnd_4036531 460595684394189286133075 := by
  unfold tailWord_4036531
  simp only [CollatzResearch.WordTrace]
  refine ⟨147224380539345046455197447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98149587026230030970131631 147224380539345046455197447)
  ·
    refine ⟨220836570809017569682796171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147224380539345046455197447 220836570809017569682796171)
    ·
      refine ⟨331254856213526354524194257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220836570809017569682796171 331254856213526354524194257)
      ·
        refine ⟨248441142160144765893145693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331254856213526354524194257 248441142160144765893145693)
        ·
          refine ⟨93165428310054287209929635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248441142160144765893145693 93165428310054287209929635)
          ·
            refine ⟨139748142465081430814894453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93165428310054287209929635 139748142465081430814894453)
            ·
              refine ⟨13101388356101384138896355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139748142465081430814894453 13101388356101384138896355)
              ·
                refine ⟨19652082534152076208344533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13101388356101384138896355 19652082534152076208344533)
                ·
                  refine ⟨460595684394189286133075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19652082534152076208344533 460595684394189286133075)
                  ·
                    rfl

theorem cell22_4036531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 7].length) (baseStart_4036531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036531 prefixEnd_4036531 := by exact prefixLift 4036531
  have htrace : WordTrace (prefixWord ++ tailWord_4036531) baseStart_4036531 baseEnd_4036531 := by
    simpa [prefixWord, tailWord_4036531, baseEnd_4036531] using wordTrace_append hprefix tailTrace_4036531
  have hstable : (prefixWord ++ tailWord_4036531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036531).length < 2 ^ (prefixWord ++ tailWord_4036531).sum := by decide
  have hdescent : baseEnd_4036531 < baseStart_4036531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036569 : List Nat := [1, 2, 1, 2, 6, 2, 1, 3, 1, 3]
def baseStart_4036569 : Nat := 118140960795 + 4036569 * 2 ^ 59
def prefixEnd_4036569 : Nat := 4983230072969 + 3 ^ 40 * 4036569 * 2
def baseEnd_4036569 : Nat := 1381800061359148425949109

theorem tailTrace_4036569 : CollatzResearch.WordTrace tailWord_4036569 prefixEnd_4036569 1381800061359148425949109 := by
  unfold tailWord_4036569
  simp only [CollatzResearch.WordTrace]
  refine ⟨147225766513207378945080761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98150511008804919296720507 147225766513207378945080761)
  ·
    refine ⟨110419324884905534208810571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147225766513207378945080761 110419324884905534208810571)
    ·
      refine ⟨165628987327358301313215857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110419324884905534208810571 165628987327358301313215857)
      ·
        refine ⟨124221740495518725984911893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165628987327358301313215857 124221740495518725984911893)
        ·
          refine ⟨5822894085727440280542745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124221740495518725984911893 5822894085727440280542745)
          ·
            refine ⟨4367170564295580210407059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5822894085727440280542745 4367170564295580210407059)
            ·
              refine ⟨6550755846443370315610589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4367170564295580210407059 6550755846443370315610589)
              ·
                refine ⟨2456533442416263868353971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6550755846443370315610589 2456533442416263868353971)
                ·
                  refine ⟨3684800163624395802530957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456533442416263868353971 3684800163624395802530957)
                  ·
                    refine ⟨1381800061359148425949109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684800163624395802530957 1381800061359148425949109)
                    ·
                      rfl

theorem cell22_4036569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 1, 3].length) (baseStart_4036569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036569 prefixEnd_4036569 := by exact prefixLift 4036569
  have htrace : WordTrace (prefixWord ++ tailWord_4036569) baseStart_4036569 baseEnd_4036569 := by
    simpa [prefixWord, tailWord_4036569, baseEnd_4036569] using wordTrace_append hprefix tailTrace_4036569
  have hstable : (prefixWord ++ tailWord_4036569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036569).length < 2 ^ (prefixWord ++ tailWord_4036569).sum := by decide
  have hdescent : baseEnd_4036569 < baseStart_4036569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036576 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 8]
def baseStart_4036576 : Nat := 118140960795 + 4036576 * 2 ^ 59
def prefixEnd_4036576 : Nat := 4983230072969 + 3 ^ 40 * 4036576 * 2
def baseEnd_4036576 : Nat := 460600819200734247008029

theorem tailTrace_4036576 : CollatzResearch.WordTrace tailWord_4036576 prefixEnd_4036576 460600819200734247008029 := by
  unfold tailWord_4036576
  simp only [CollatzResearch.WordTrace]
  refine ⟨73613010912091009570292791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98150681216121346093723721 73613010912091009570292791)
  ·
    refine ⟨110419516368136514355439187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73613010912091009570292791 110419516368136514355439187)
    ·
      refine ⟨165629274552204771533158781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110419516368136514355439187 165629274552204771533158781)
      ·
        refine ⟨62110977957076789324934543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165629274552204771533158781 62110977957076789324934543)
        ·
          refine ⟨93166466935615183987401815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62110977957076789324934543 93166466935615183987401815)
          ·
            refine ⟨139749700403422775981102723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93166466935615183987401815 139749700403422775981102723)
            ·
              refine ⟨209624550605134163971654085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139749700403422775981102723 209624550605134163971654085)
              ·
                refine ⟨39304603238462655744685141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209624550605134163971654085 39304603238462655744685141)
                ·
                  refine ⟨460600819200734247008029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39304603238462655744685141 460600819200734247008029)
                  ·
                    rfl

theorem cell22_4036576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_4036576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036576 prefixEnd_4036576 := by exact prefixLift 4036576
  have htrace : WordTrace (prefixWord ++ tailWord_4036576) baseStart_4036576 baseEnd_4036576 := by
    simpa [prefixWord, tailWord_4036576, baseEnd_4036576] using wordTrace_append hprefix tailTrace_4036576
  have hstable : (prefixWord ++ tailWord_4036576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036576).length < 2 ^ (prefixWord ++ tailWord_4036576).sum := by decide
  have hdescent : baseEnd_4036576 < baseStart_4036576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036608 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 6, 3]
def baseStart_4036608 : Nat := 118140960795 + 4036608 * 2 ^ 59
def prefixEnd_4036608 : Nat := 4983230072969 + 3 ^ 40 * 4036608 * 2
def baseEnd_4036608 : Nat := 1381813411856165324223989

theorem tailTrace_4036608 : CollatzResearch.WordTrace tailWord_4036608 prefixEnd_4036608 1381813411856165324223989 := by
  unfold tailWord_4036608
  simp only [CollatzResearch.WordTrace]
  refine ⟨73613594480033044302875239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98151459306710725737166985 73613594480033044302875239)
  ·
    refine ⟨110420391720049566454312859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73613594480033044302875239 110420391720049566454312859)
    ·
      refine ⟨165630587580074349681469289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110420391720049566454312859 165630587580074349681469289)
      ·
        refine ⟨124222940685055762261101967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165630587580074349681469289 124222940685055762261101967)
        ·
          refine ⟨186334411027583643391652951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124222940685055762261101967 186334411027583643391652951)
          ·
            refine ⟨279501616541375465087479427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186334411027583643391652951 279501616541375465087479427)
            ·
              refine ⟨419252424812063197631219141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279501616541375465087479427 419252424812063197631219141)
              ·
                refine ⟨78609829652261849555853589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419252424812063197631219141 78609829652261849555853589)
                ·
                  refine ⟨3684835764949774197930637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78609829652261849555853589 3684835764949774197930637)
                  ·
                    refine ⟨1381813411856165324223989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684835764949774197930637 1381813411856165324223989)
                    ·
                      rfl

theorem cell22_4036608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6, 3].length) (baseStart_4036608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036608 prefixEnd_4036608 := by exact prefixLift 4036608
  have htrace : WordTrace (prefixWord ++ tailWord_4036608) baseStart_4036608 baseEnd_4036608 := by
    simpa [prefixWord, tailWord_4036608, baseEnd_4036608] using wordTrace_append hprefix tailTrace_4036608
  have hstable : (prefixWord ++ tailWord_4036608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036608).length < 2 ^ (prefixWord ++ tailWord_4036608).sum := by decide
  have hdescent : baseEnd_4036608 < baseStart_4036608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036612 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_4036612 : Nat := 118140960795 + 4036612 * 2 ^ 59
def prefixEnd_4036612 : Nat := 4983230072969 + 3 ^ 40 * 4036612 * 2
def baseEnd_4036612 : Nat := 1381814781137910647123977

theorem tailTrace_4036612 : CollatzResearch.WordTrace tailWord_4036612 prefixEnd_4036612 1381814781137910647123977 := by
  unfold tailWord_4036612
  simp only [CollatzResearch.WordTrace]
  refine ⟨73613667426025798644448045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98151556568034398192597393 73613667426025798644448045)
  ·
    refine ⟨27605125284759674491668017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73613667426025798644448045 27605125284759674491668017)
    ·
      refine ⟨20703843963569755868751013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27605125284759674491668017 20703843963569755868751013)
      ·
        refine ⟨3881970743169329225390815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20703843963569755868751013 3881970743169329225390815)
        ·
          refine ⟨5822956114753993838086223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3881970743169329225390815 5822956114753993838086223)
          ·
            refine ⟨8734434172130990757129335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5822956114753993838086223 8734434172130990757129335)
            ·
              refine ⟨13101651258196486135694003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8734434172130990757129335 13101651258196486135694003)
              ·
                refine ⟨19652476887294729203541005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13101651258196486135694003 19652476887294729203541005)
                ·
                  refine ⟨7369678832735523451327877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19652476887294729203541005 7369678832735523451327877)
                  ·
                    refine ⟨1381814781137910647123977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7369678832735523451327877 1381814781137910647123977)
                    ·
                      rfl

theorem cell22_4036612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_4036612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036612 prefixEnd_4036612 := by exact prefixLift 4036612
  have htrace : WordTrace (prefixWord ++ tailWord_4036612) baseStart_4036612 baseEnd_4036612 := by
    simpa [prefixWord, tailWord_4036612, baseEnd_4036612] using wordTrace_append hprefix tailTrace_4036612
  have hstable : (prefixWord ++ tailWord_4036612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036612).length < 2 ^ (prefixWord ++ tailWord_4036612).sum := by decide
  have hdescent : baseEnd_4036612 < baseStart_4036612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036642 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_4036642 : Nat := 118140960795 + 4036642 * 2 ^ 59
def prefixEnd_4036642 : Nat := 4983230072969 + 3 ^ 40 * 4036642 * 2
def baseEnd_4036642 : Nat := 1381825050751000568873885

theorem tailTrace_4036642 : CollatzResearch.WordTrace tailWord_4036642 prefixEnd_4036642 1381825050751000568873885 := by
  unfold tailWord_4036642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36807107260485728103122045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98152286027961941608325453 36807107260485728103122045)
  ·
    refine ⟨13802665222682148038670767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36807107260485728103122045 13802665222682148038670767)
    ·
      refine ⟨20703997834023222058006151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13802665222682148038670767 20703997834023222058006151)
      ·
        refine ⟨31055996751034833087009227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20703997834023222058006151 31055996751034833087009227)
        ·
          refine ⟨46583995126552249630513841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31055996751034833087009227 46583995126552249630513841)
          ·
            refine ⟨34937996344914187222885381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46583995126552249630513841 34937996344914187222885381)
            ·
              refine ⟨6550874314671410104291009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34937996344914187222885381 6550874314671410104291009)
              ·
                refine ⟨4913155736003557578218257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6550874314671410104291009 4913155736003557578218257)
                ·
                  refine ⟨3684866802002668183663693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4913155736003557578218257 3684866802002668183663693)
                  ·
                    refine ⟨1381825050751000568873885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684866802002668183663693 1381825050751000568873885)
                    ·
                      rfl

theorem cell22_4036642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_4036642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036642 prefixEnd_4036642 := by exact prefixLift 4036642
  have htrace : WordTrace (prefixWord ++ tailWord_4036642) baseStart_4036642 baseEnd_4036642 := by
    simpa [prefixWord, tailWord_4036642, baseEnd_4036642] using wordTrace_append hprefix tailTrace_4036642
  have hstable : (prefixWord ++ tailWord_4036642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036642).length < 2 ^ (prefixWord ++ tailWord_4036642).sum := by decide
  have hdescent : baseEnd_4036642 < baseStart_4036642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036668 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_4036668 : Nat := 118140960795 + 4036668 * 2 ^ 59
def prefixEnd_4036668 : Nat := 4983230072969 + 3 ^ 40 * 4036668 * 2
def baseEnd_4036668 : Nat := 1381833951082345167723805

theorem tailTrace_4036668 : CollatzResearch.WordTrace tailWord_4036668 prefixEnd_4036668 1381833951082345167723805 := by
  unfold tailWord_4036668
  simp only [CollatzResearch.WordTrace]
  refine ⟨73614688669924359426467329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98152918226565812568623105 73614688669924359426467329)
  ·
    refine ⟨55211016502443269569850497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73614688669924359426467329 55211016502443269569850497)
    ·
      refine ⟨41408262376832452177387873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55211016502443269569850497 41408262376832452177387873)
      ·
        refine ⟨31056196782624339133040905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41408262376832452177387873 31056196782624339133040905)
        ·
          refine ⟨23292147586968254349780679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31056196782624339133040905 23292147586968254349780679)
          ·
            refine ⟨34938221380452381524671019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23292147586968254349780679 34938221380452381524671019)
            ·
              refine ⟨52407332070678572287006529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34938221380452381524671019 52407332070678572287006529)
              ·
                refine ⟨39305499053008929215254897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52407332070678572287006529 39305499053008929215254897)
                ·
                  refine ⟨29479124289756696911441173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39305499053008929215254897 29479124289756696911441173)
                  ·
                    refine ⟨1381833951082345167723805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29479124289756696911441173 1381833951082345167723805)
                    ·
                      rfl

theorem cell22_4036668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_4036668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036668 prefixEnd_4036668 := by exact prefixLift 4036668
  have htrace : WordTrace (prefixWord ++ tailWord_4036668) baseStart_4036668 baseEnd_4036668 := by
    simpa [prefixWord, tailWord_4036668, baseEnd_4036668] using wordTrace_append hprefix tailTrace_4036668
  have hstable : (prefixWord ++ tailWord_4036668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036668).length < 2 ^ (prefixWord ++ tailWord_4036668).sum := by decide
  have hdescent : baseEnd_4036668 < baseStart_4036668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036698 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_4036698 : Nat := 118140960795 + 4036698 * 2 ^ 59
def prefixEnd_4036698 : Nat := 4983230072969 + 3 ^ 40 * 4036698 * 2
def baseEnd_4036698 : Nat := 1381844220695435089473713

theorem tailTrace_4036698 : CollatzResearch.WordTrace tailWord_4036698 prefixEnd_4036698 1381844220695435089473713 := by
  unfold tailWord_4036698
  simp only [CollatzResearch.WordTrace]
  refine ⟨36807617882435008494131687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98153647686493355984351165 36807617882435008494131687)
  ·
    refine ⟨55211426823652512741197531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36807617882435008494131687 55211426823652512741197531)
    ·
      refine ⟨82817140235478769111796297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55211426823652512741197531 82817140235478769111796297)
      ·
        refine ⟨62112855176609076833847223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82817140235478769111796297 62112855176609076833847223)
        ·
          refine ⟨93169282764913615250770835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62112855176609076833847223 93169282764913615250770835)
          ·
            refine ⟨139753924147370422876156253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93169282764913615250770835 139753924147370422876156253)
            ·
              refine ⟨52407721555263908578558595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139753924147370422876156253 52407721555263908578558595)
              ·
                refine ⟨78611582332895862867837893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52407721555263908578558595 78611582332895862867837893)
                ·
                  refine ⟨14739671687417974287719605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78611582332895862867837893 14739671687417974287719605)
                  ·
                    refine ⟨1381844220695435089473713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14739671687417974287719605 1381844220695435089473713)
                    ·
                      rfl

theorem cell22_4036698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_4036698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036698 prefixEnd_4036698 := by exact prefixLift 4036698
  have htrace : WordTrace (prefixWord ++ tailWord_4036698) baseStart_4036698 baseEnd_4036698 := by
    simpa [prefixWord, tailWord_4036698, baseEnd_4036698] using wordTrace_append hprefix tailTrace_4036698
  have hstable : (prefixWord ++ tailWord_4036698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036698).length < 2 ^ (prefixWord ++ tailWord_4036698).sum := by decide
  have hdescent : baseEnd_4036698 < baseStart_4036698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036700 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 7]
def baseStart_4036700 : Nat := 118140960795 + 4036700 * 2 ^ 59
def prefixEnd_4036700 : Nat := 4983230072969 + 3 ^ 40 * 4036700 * 2
def baseEnd_4036700 : Nat := 460614968445435916974569

theorem tailTrace_4036700 : CollatzResearch.WordTrace tailWord_4036700 prefixEnd_4036700 460614968445435916974569 := by
  unfold tailWord_4036700
  simp only [CollatzResearch.WordTrace]
  refine ⟨73615272237866394159049777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98153696317155192212066369 73615272237866394159049777)
  ·
    refine ⟨55211454178399795619287333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73615272237866394159049777 55211454178399795619287333)
    ·
      refine ⟨10352147658449961678616375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55211454178399795619287333 10352147658449961678616375)
      ·
        refine ⟨15528221487674942517924563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10352147658449961678616375 15528221487674942517924563)
        ·
          refine ⟨23292332231512413776886845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15528221487674942517924563 23292332231512413776886845)
          ·
            refine ⟨8734624586817155166332567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23292332231512413776886845 8734624586817155166332567)
            ·
              refine ⟨13101936880225732749498851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8734624586817155166332567 13101936880225732749498851)
              ·
                refine ⟨19652905320338599124248277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13101936880225732749498851 19652905320338599124248277)
                ·
                  refine ⟨460614968445435916974569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19652905320338599124248277 460614968445435916974569)
                  ·
                    rfl

theorem cell22_4036700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_4036700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036700 prefixEnd_4036700 := by exact prefixLift 4036700
  have htrace : WordTrace (prefixWord ++ tailWord_4036700) baseStart_4036700 baseEnd_4036700 := by
    simpa [prefixWord, tailWord_4036700, baseEnd_4036700] using wordTrace_append hprefix tailTrace_4036700
  have hstable : (prefixWord ++ tailWord_4036700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036700).length < 2 ^ (prefixWord ++ tailWord_4036700).sum := by decide
  have hdescent : baseEnd_4036700 < baseStart_4036700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036717 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 5]
def baseStart_4036717 : Nat := 118140960795 + 4036717 * 2 ^ 59
def prefixEnd_4036717 : Nat := 4983230072969 + 3 ^ 40 * 4036717 * 2
def baseEnd_4036717 : Nat := 460616908261241791082885

theorem tailTrace_4036717 : CollatzResearch.WordTrace tailWord_4036717 prefixEnd_4036717 460616908261241791082885 := by
  unfold tailWord_4036717
  simp only [CollatzResearch.WordTrace]
  refine ⟨147231164516671200221468405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98154109677780800147645603 147231164516671200221468405)
  ·
    refine ⟨13802921673437925020762663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147231164516671200221468405 13802921673437925020762663)
    ·
      refine ⟨20704382510156887531143995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13802921673437925020762663 20704382510156887531143995)
      ·
        refine ⟨31056573765235331296715993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20704382510156887531143995 31056573765235331296715993)
        ·
          refine ⟨23292430323926498472536995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31056573765235331296715993 23292430323926498472536995)
          ·
            refine ⟨34938645485889747708805493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23292430323926498472536995 34938645485889747708805493)
            ·
              refine ⟨3275498014302163847700515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34938645485889747708805493 3275498014302163847700515)
              ·
                refine ⟨4913247021453245771550773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275498014302163847700515 4913247021453245771550773)
                ·
                  refine ⟨460616908261241791082885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4913247021453245771550773 460616908261241791082885)
                  ·
                    rfl

theorem cell22_4036717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_4036717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036717 prefixEnd_4036717 := by exact prefixLift 4036717
  have htrace : WordTrace (prefixWord ++ tailWord_4036717) baseStart_4036717 baseEnd_4036717 := by
    simpa [prefixWord, tailWord_4036717, baseEnd_4036717] using wordTrace_append hprefix tailTrace_4036717
  have hstable : (prefixWord ++ tailWord_4036717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036717).length < 2 ^ (prefixWord ++ tailWord_4036717).sum := by decide
  have hdescent : baseEnd_4036717 < baseStart_4036717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036839 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 3, 3]
def baseStart_4036839 : Nat := 118140960795 + 4036839 * 2 ^ 59
def prefixEnd_4036839 : Nat := 4983230072969 + 3 ^ 40 * 4036839 * 2
def baseEnd_4036839 : Nat := 1381892487876957721698281

theorem tailTrace_4036839 : CollatzResearch.WordTrace tailWord_4036839 prefixEnd_4036839 1381892487876957721698281 := by
  unfold tailWord_4036839
  simp only [CollatzResearch.WordTrace]
  refine ⟨147235614222229215057409571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98157076148152810038273047 147235614222229215057409571)
  ·
    refine ⟨220853421333343822586114357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147235614222229215057409571 220853421333343822586114357)
    ·
      refine ⟨20705008250000983367448221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220853421333343822586114357 20705008250000983367448221)
      ·
        refine ⟨7764378093750368762793083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20705008250000983367448221 7764378093750368762793083)
        ·
          refine ⟨11646567140625553144189625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7764378093750368762793083 11646567140625553144189625)
          ·
            refine ⟨8734925355469164858142219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11646567140625553144189625 8734925355469164858142219)
            ·
              refine ⟨13102388033203747287213329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8734925355469164858142219 13102388033203747287213329)
              ·
                refine ⟨9826791024902810465409997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13102388033203747287213329 9826791024902810465409997)
                ·
                  refine ⟨3685046634338553924528749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9826791024902810465409997 3685046634338553924528749)
                  ·
                    refine ⟨1381892487876957721698281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3685046634338553924528749 1381892487876957721698281)
                    ·
                      rfl

theorem cell22_4036839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_4036839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036839 prefixEnd_4036839 := by exact prefixLift 4036839
  have htrace : WordTrace (prefixWord ++ tailWord_4036839) baseStart_4036839 baseEnd_4036839 := by
    simpa [prefixWord, tailWord_4036839, baseEnd_4036839] using wordTrace_append hprefix tailTrace_4036839
  have hstable : (prefixWord ++ tailWord_4036839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036839).length < 2 ^ (prefixWord ++ tailWord_4036839).sum := by decide
  have hdescent : baseEnd_4036839 < baseStart_4036839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036927 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 2, 4]
def baseStart_4036927 : Nat := 118140960795 + 4036927 * 2 ^ 59
def prefixEnd_4036927 : Nat := 4983230072969 + 3 ^ 40 * 4036927 * 2
def baseEnd_4036927 : Nat := 1381922612075354825498011

theorem tailTrace_4036927 : CollatzResearch.WordTrace tailWord_4036927 prefixEnd_4036927 1381922612075354825498011 := by
  unfold tailWord_4036927
  simp only [CollatzResearch.WordTrace]
  refine ⟨147238823845910406086613035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98159215897273604057742023 147238823845910406086613035)
  ·
    refine ⟨220858235768865609129919553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147238823845910406086613035 220858235768865609129919553)
    ·
      refine ⟨165643676826649206847439665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220858235768865609129919553 165643676826649206847439665)
      ·
        refine ⟨124232757619986905135579749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165643676826649206847439665 124232757619986905135579749)
        ·
          refine ⟨23293642053747544712921203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124232757619986905135579749 23293642053747544712921203)
          ·
            refine ⟨34940463080621317069381805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23293642053747544712921203 34940463080621317069381805)
            ·
              refine ⟨13102673655232993901018177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34940463080621317069381805 13102673655232993901018177)
              ·
                refine ⟨9827005241424745425763633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13102673655232993901018177 9827005241424745425763633)
                ·
                  refine ⟨7370253931068559069322725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9827005241424745425763633 7370253931068559069322725)
                  ·
                    refine ⟨1381922612075354825498011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7370253931068559069322725 1381922612075354825498011)
                    ·
                      rfl

theorem cell22_4036927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_4036927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036927 prefixEnd_4036927 := by exact prefixLift 4036927
  have htrace : WordTrace (prefixWord ++ tailWord_4036927) baseStart_4036927 baseEnd_4036927 := by
    simpa [prefixWord, tailWord_4036927, baseEnd_4036927] using wordTrace_append hprefix tailTrace_4036927
  have hstable : (prefixWord ++ tailWord_4036927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036927).length < 2 ^ (prefixWord ++ tailWord_4036927).sum := by decide
  have hdescent : baseEnd_4036927 < baseStart_4036927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036946 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_4036946 : Nat := 118140960795 + 4036946 * 2 ^ 59
def prefixEnd_4036946 : Nat := 4983230072969 + 3 ^ 40 * 4036946 * 2
def baseEnd_4036946 : Nat := 1381929116163645109272953

theorem tailTrace_4036946 : CollatzResearch.WordTrace tailWord_4036946 prefixEnd_4036946 1381929116163645109272953 := by
  unfold tailWord_4036946
  simp only [CollatzResearch.WordTrace]
  refine ⟨36809879208210393082888673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98159677888561048221036461 36809879208210393082888673)
  ·
    refine ⟨27607409406157794812166505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36809879208210393082888673 27607409406157794812166505)
    ·
      refine ⟨20705557054618346109124879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27607409406157794812166505 20705557054618346109124879)
      ·
        refine ⟨31058335581927519163687319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20705557054618346109124879 31058335581927519163687319)
        ·
          refine ⟨46587503372891278745530979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31058335581927519163687319 46587503372891278745530979)
          ·
            refine ⟨69881255059336918118296469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46587503372891278745530979 69881255059336918118296469)
            ·
              refine ⟨3275683830906418036795147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69881255059336918118296469 3275683830906418036795147)
              ·
                refine ⟨4913525746359627055192721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275683830906418036795147 4913525746359627055192721)
                ·
                  refine ⟨3685144309769720291394541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4913525746359627055192721 3685144309769720291394541)
                  ·
                    refine ⟨1381929116163645109272953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3685144309769720291394541 1381929116163645109272953)
                    ·
                      rfl

theorem cell22_4036946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_4036946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036946 prefixEnd_4036946 := by exact prefixLift 4036946
  have htrace : WordTrace (prefixWord ++ tailWord_4036946) baseStart_4036946 baseEnd_4036946 := by
    simpa [prefixWord, tailWord_4036946, baseEnd_4036946] using wordTrace_append hprefix tailTrace_4036946
  have hstable : (prefixWord ++ tailWord_4036946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036946).length < 2 ^ (prefixWord ++ tailWord_4036946).sum := by decide
  have hdescent : baseEnd_4036946 < baseStart_4036946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036982 : List Nat := [5, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_4036982 : Nat := 118140960795 + 4036982 * 2 ^ 59
def prefixEnd_4036982 : Nat := 4983230072969 + 3 ^ 40 * 4036982 * 2
def baseEnd_4036982 : Nat := 460647146566451005124281

theorem tailTrace_4036982 : CollatzResearch.WordTrace tailWord_4036982 prefixEnd_4036982 460647146566451005124281 := by
  unfold tailWord_4036982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9202551866294446904991575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98160553240474100319910133 9202551866294446904991575)
  ·
    refine ⟨13803827799441670357487363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9202551866294446904991575 13803827799441670357487363)
    ·
      refine ⟨20705741699162505536231045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13803827799441670357487363 20705741699162505536231045)
      ·
        refine ⟨3882326568592969788043321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20705741699162505536231045 3882326568592969788043321)
        ·
          refine ⟨2911744926444727341032491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3882326568592969788043321 2911744926444727341032491)
          ·
            refine ⟨4367617389667091011548737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911744926444727341032491 4367617389667091011548737)
            ·
              refine ⟨3275713042250318258661553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4367617389667091011548737 3275713042250318258661553)
              ·
                refine ⟨2456784781687738693996165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3275713042250318258661553 2456784781687738693996165)
                ·
                  refine ⟨460647146566451005124281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2456784781687738693996165 460647146566451005124281)
                  ·
                    rfl

theorem cell22_4036982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_4036982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036982 prefixEnd_4036982 := by exact prefixLift 4036982
  have htrace : WordTrace (prefixWord ++ tailWord_4036982) baseStart_4036982 baseEnd_4036982 := by
    simpa [prefixWord, tailWord_4036982, baseEnd_4036982] using wordTrace_append hprefix tailTrace_4036982
  have hstable : (prefixWord ++ tailWord_4036982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036982).length < 2 ^ (prefixWord ++ tailWord_4036982).sum := by decide
  have hdescent : baseEnd_4036982 < baseStart_4036982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036987 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 5]
def baseStart_4036987 : Nat := 118140960795 + 4036987 * 2 ^ 59
def prefixEnd_4036987 : Nat := 4983230072969 + 3 ^ 40 * 4036987 * 2
def baseEnd_4036987 : Nat := 460647717100511556332609

theorem tailTrace_4036987 : CollatzResearch.WordTrace tailWord_4036987 prefixEnd_4036987 460647717100511556332609 := by
  unfold tailWord_4036987
  simp only [CollatzResearch.WordTrace]
  refine ⟨147241012225693036333797215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98160674817128690889198143 147241012225693036333797215)
  ·
    refine ⟨220861518338539554500695823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147241012225693036333797215 220861518338539554500695823)
    ·
      refine ⟨331292277507809331751043735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220861518338539554500695823 331292277507809331751043735)
      ·
        refine ⟨496938416261713997626565603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331292277507809331751043735 496938416261713997626565603)
        ·
          refine ⟨745407624392570996439848405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496938416261713997626565603 745407624392570996439848405)
          ·
            refine ⟨17470491196700882729058947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 745407624392570996439848405 17470491196700882729058947)
            ·
              refine ⟨26205736795051324093588421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17470491196700882729058947 26205736795051324093588421)
              ·
                refine ⟨4913575649072123267547829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26205736795051324093588421 4913575649072123267547829)
                ·
                  refine ⟨460647717100511556332609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4913575649072123267547829 460647717100511556332609)
                  ·
                    rfl

theorem cell22_4036987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 5].length) (baseStart_4036987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4036987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4036987 prefixEnd_4036987 := by exact prefixLift 4036987
  have htrace : WordTrace (prefixWord ++ tailWord_4036987) baseStart_4036987 baseEnd_4036987 := by
    simpa [prefixWord, tailWord_4036987, baseEnd_4036987] using wordTrace_append hprefix tailTrace_4036987
  have hstable : (prefixWord ++ tailWord_4036987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036987).length < 2 ^ (prefixWord ++ tailWord_4036987).sum := by decide
  have hdescent : baseEnd_4036987 < baseStart_4036987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037017 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_4037017 : Nat := 118140960795 + 4037017 * 2 ^ 59
def prefixEnd_4037017 : Nat := 4983230072969 + 3 ^ 40 * 4037017 * 2
def baseEnd_4037017 : Nat := 1381953420914624590747735

theorem tailTrace_4037017 : CollatzResearch.WordTrace tailWord_4037017 prefixEnd_4037017 1381953420914624590747735 := by
  unfold tailWord_4037017
  simp only [CollatzResearch.WordTrace]
  refine ⟨147242106415584351457389305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98161404277056234304926203 147242106415584351457389305)
  ·
    refine ⟨110431579811688263593041979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147242106415584351457389305 110431579811688263593041979)
    ·
      refine ⟨165647369717532395389562969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110431579811688263593041979 165647369717532395389562969)
      ·
        refine ⟨124235527288149296542172227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165647369717532395389562969 124235527288149296542172227)
        ·
          refine ⟨186353290932223944813258341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124235527288149296542172227 186353290932223944813258341)
          ·
            refine ⟨34941242049791989652485939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186353290932223944813258341 34941242049791989652485939)
            ·
              refine ⟨52411863074687984478728909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34941242049791989652485939 52411863074687984478728909)
              ·
                refine ⟨19654448653007994179523341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52411863074687984478728909 19654448653007994179523341)
                ·
                  refine ⟨7370418244877997817321253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19654448653007994179523341 7370418244877997817321253)
                  ·
                    refine ⟨1381953420914624590747735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7370418244877997817321253 1381953420914624590747735)
                    ·
                      rfl

theorem cell22_4037017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_4037017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037017 prefixEnd_4037017 := by exact prefixLift 4037017
  have htrace : WordTrace (prefixWord ++ tailWord_4037017) baseStart_4037017 baseEnd_4037017 := by
    simpa [prefixWord, tailWord_4037017, baseEnd_4037017] using wordTrace_append hprefix tailTrace_4037017
  have hstable : (prefixWord ++ tailWord_4037017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037017).length < 2 ^ (prefixWord ++ tailWord_4037017).sum := by decide
  have hdescent : baseEnd_4037017 < baseStart_4037017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037025 : List Nat := [1, 2, 3, 5, 1, 1, 2, 3, 1, 3]
def baseStart_4037025 : Nat := 118140960795 + 4037025 * 2 ^ 59
def prefixEnd_4037025 : Nat := 4983230072969 + 3 ^ 40 * 4037025 * 2
def baseEnd_4037025 : Nat := 1381956159478115236547711

theorem tailTrace_4037025 : CollatzResearch.WordTrace tailWord_4037025 prefixEnd_4037025 1381956159478115236547711 := by
  unfold tailWord_4037025
  simp only [CollatzResearch.WordTrace]
  refine ⟨147242398199555368823680529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98161598799703579215787019 147242398199555368823680529)
  ·
    refine ⟨110431798649666526617760397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147242398199555368823680529 110431798649666526617760397)
    ·
      refine ⟨41411924493624947481660149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110431798649666526617760397 41411924493624947481660149)
      ·
        refine ⟨3882367921277338826405639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41411924493624947481660149 3882367921277338826405639)
        ·
          refine ⟨5823551881916008239608459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882367921277338826405639 5823551881916008239608459)
          ·
            refine ⟨8735327822874012359412689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5823551881916008239608459 8735327822874012359412689)
            ·
              refine ⟨6551495867155509269559517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8735327822874012359412689 6551495867155509269559517)
              ·
                refine ⟨2456810950183315976084819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6551495867155509269559517 2456810950183315976084819)
                ·
                  refine ⟨3685216425274973964127229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456810950183315976084819 3685216425274973964127229)
                  ·
                    refine ⟨1381956159478115236547711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3685216425274973964127229 1381956159478115236547711)
                    ·
                      rfl

theorem cell22_4037025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_4037025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037025 prefixEnd_4037025 := by exact prefixLift 4037025
  have htrace : WordTrace (prefixWord ++ tailWord_4037025) baseStart_4037025 baseEnd_4037025 := by
    simpa [prefixWord, tailWord_4037025, baseEnd_4037025] using wordTrace_append hprefix tailTrace_4037025
  have hstable : (prefixWord ++ tailWord_4037025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037025).length < 2 ^ (prefixWord ++ tailWord_4037025).sum := by decide
  have hdescent : baseEnd_4037025 < baseStart_4037025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037049 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 6]
def baseStart_4037049 : Nat := 118140960795 + 4037049 * 2 ^ 59
def prefixEnd_4037049 : Nat := 4983230072969 + 3 ^ 40 * 4037049 * 2
def baseEnd_4037049 : Nat := 460654791722862391315879

theorem tailTrace_4037049 : CollatzResearch.WordTrace tailWord_4037049 prefixEnd_4037049 460654791722862391315879 := by
  unfold tailWord_4037049
  simp only [CollatzResearch.WordTrace]
  refine ⟨147243273551468420922554201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98162182367645613948369467 147243273551468420922554201)
  ·
    refine ⟨110432455163601315691915651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147243273551468420922554201 110432455163601315691915651)
    ·
      refine ⟨165648682745401973537873477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110432455163601315691915651 165648682745401973537873477)
      ·
        refine ⟨31059128014762870038351277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165648682745401973537873477 31059128014762870038351277)
        ·
          refine ⟨11647173005536076264381729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31059128014762870038351277 11647173005536076264381729)
          ·
            refine ⟨8735379754152057198286297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11647173005536076264381729 8735379754152057198286297)
            ·
              refine ⟨6551534815614042898714723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8735379754152057198286297 6551534815614042898714723)
              ·
                refine ⟨9827302223421064348072085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6551534815614042898714723 9827302223421064348072085)
                ·
                  refine ⟨460654791722862391315879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9827302223421064348072085 460654791722862391315879)
                  ·
                    rfl

theorem cell22_4037049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_4037049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037049 prefixEnd_4037049 := by exact prefixLift 4037049
  have htrace : WordTrace (prefixWord ++ tailWord_4037049) baseStart_4037049 baseEnd_4037049 := by
    simpa [prefixWord, tailWord_4037049, baseEnd_4037049] using wordTrace_append hprefix tailTrace_4037049
  have hstable : (prefixWord ++ tailWord_4037049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037049).length < 2 ^ (prefixWord ++ tailWord_4037049).sum := by decide
  have hdescent : baseEnd_4037049 < baseStart_4037049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037064 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 1, 5]
def baseStart_4037064 : Nat := 118140960795 + 4037064 * 2 ^ 59
def prefixEnd_4037064 : Nat := 4983230072969 + 3 ^ 40 * 4037064 * 2
def baseEnd_4037064 : Nat := 1381969509975132134822591

theorem tailTrace_4037064 : CollatzResearch.WordTrace tailWord_4037064 prefixEnd_4037064 1381969509975132134822591 := by
  unfold tailWord_4037064
  simp only [CollatzResearch.WordTrace]
  refine ⟨73621910323207039242175123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98162547097609385656233497 73621910323207039242175123)
  ·
    refine ⟨110432865484810558863262685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73621910323207039242175123 110432865484810558863262685)
    ·
      refine ⟨41412324556803959573723507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110432865484810558863262685 41412324556803959573723507)
      ·
        refine ⟨62118486835205939360585261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41412324556803959573723507 62118486835205939360585261)
        ·
          refine ⟨23294432563202227260219473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62118486835205939360585261 23294432563202227260219473)
          ·
            refine ⟨17470824422401670445164605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23294432563202227260219473 17470824422401670445164605)
            ·
              refine ⟨6551559158400626416936727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17470824422401670445164605 6551559158400626416936727)
              ·
                refine ⟨9827338737600939625405091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6551559158400626416936727 9827338737600939625405091)
                ·
                  refine ⟨14741008106401409438107637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9827338737600939625405091 14741008106401409438107637)
                  ·
                    refine ⟨1381969509975132134822591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14741008106401409438107637 1381969509975132134822591)
                    ·
                      rfl

theorem cell22_4037064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_4037064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037064 prefixEnd_4037064 := by exact prefixLift 4037064
  have htrace : WordTrace (prefixWord ++ tailWord_4037064) baseStart_4037064 baseEnd_4037064 := by
    simpa [prefixWord, tailWord_4037064, baseEnd_4037064] using wordTrace_append hprefix tailTrace_4037064
  have hstable : (prefixWord ++ tailWord_4037064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037064).length < 2 ^ (prefixWord ++ tailWord_4037064).sum := by decide
  have hdescent : baseEnd_4037064 < baseStart_4037064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037107 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 2, 6]
def baseStart_4037107 : Nat := 118140960795 + 4037107 * 2 ^ 59
def prefixEnd_4037107 : Nat := 4983230072969 + 3 ^ 40 * 4037107 * 2
def baseEnd_4037107 : Nat := 1381984229753894355997459

theorem tailTrace_4037107 : CollatzResearch.WordTrace tailWord_4037107 prefixEnd_4037107 1381984229753894355997459 := by
  unfold tailWord_4037107
  simp only [CollatzResearch.WordTrace]
  refine ⟨147245388985258296828165575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98163592656838864552110383 147245388985258296828165575)
  ·
    refine ⟨220868083477887445242248363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147245388985258296828165575 220868083477887445242248363)
    ·
      refine ⟨331302125216831167863372545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220868083477887445242248363 331302125216831167863372545)
      ·
        refine ⟨248476593912623375897529409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331302125216831167863372545 248476593912623375897529409)
        ·
          refine ⟨186357445434467531923147057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248476593912623375897529409 186357445434467531923147057)
          ·
            refine ⟨139768084075850648942360293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186357445434467531923147057 139768084075850648942360293)
            ·
              refine ⟨26206515764221996676692555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139768084075850648942360293 26206515764221996676692555)
              ·
                refine ⟨39309773646332995015038833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26206515764221996676692555 39309773646332995015038833)
                ·
                  refine ⟨29482330234749746261279125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39309773646332995015038833 29482330234749746261279125)
                  ·
                    refine ⟨1381984229753894355997459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29482330234749746261279125 1381984229753894355997459)
                    ·
                      rfl

theorem cell22_4037107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_4037107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037107 prefixEnd_4037107 := by exact prefixLift 4037107
  have htrace : WordTrace (prefixWord ++ tailWord_4037107) baseStart_4037107 baseEnd_4037107 := by
    simpa [prefixWord, tailWord_4037107, baseEnd_4037107] using wordTrace_append hprefix tailTrace_4037107
  have hstable : (prefixWord ++ tailWord_4037107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037107).length < 2 ^ (prefixWord ++ tailWord_4037107).sum := by decide
  have hdescent : baseEnd_4037107 < baseStart_4037107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037137 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_4037137 : Nat := 118140960795 + 4037137 * 2 ^ 59
def prefixEnd_4037137 : Nat := 4983230072969 + 3 ^ 40 * 4037137 * 2
def baseEnd_4037137 : Nat := 1381994499366984277747367

theorem tailTrace_4037137 : CollatzResearch.WordTrace tailWord_4037137 prefixEnd_4037137 1381994499366984277747367 := by
  unfold tailWord_4037137
  simp only [CollatzResearch.WordTrace]
  refine ⟨147246483175149611951757665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98164322116766407967838443 147246483175149611951757665)
  ·
    refine ⟨110434862381362208963818249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147246483175149611951757665 110434862381362208963818249)
    ·
      refine ⟨82826146786021656722863687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110434862381362208963818249 82826146786021656722863687)
      ·
        refine ⟨124239220179032485084295531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82826146786021656722863687 124239220179032485084295531)
        ·
          refine ⟨186358830268548727626443297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124239220179032485084295531 186358830268548727626443297)
          ·
            refine ⟨139769122701411545719832473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186358830268548727626443297 139769122701411545719832473)
            ·
              refine ⟨104826842026058659289874355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139769122701411545719832473 104826842026058659289874355)
              ·
                refine ⟨157240263039087988934811533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104826842026058659289874355 157240263039087988934811533)
                ·
                  refine ⟨58965098639657995850554325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157240263039087988934811533 58965098639657995850554325)
                  ·
                    refine ⟨1381994499366984277747367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58965098639657995850554325 1381994499366984277747367)
                    ·
                      rfl

theorem cell22_4037137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_4037137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037137 prefixEnd_4037137 := by exact prefixLift 4037137
  have htrace : WordTrace (prefixWord ++ tailWord_4037137) baseStart_4037137 baseEnd_4037137 := by
    simpa [prefixWord, tailWord_4037137, baseEnd_4037137] using wordTrace_append hprefix tailTrace_4037137
  have hstable : (prefixWord ++ tailWord_4037137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037137).length < 2 ^ (prefixWord ++ tailWord_4037137).sum := by decide
  have hdescent : baseEnd_4037137 < baseStart_4037137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037154 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_4037154 : Nat := 118140960795 + 4037154 * 2 ^ 59
def prefixEnd_4037154 : Nat := 4983230072969 + 3 ^ 40 * 4037154 * 2
def baseEnd_4037154 : Nat := 1382000318814401900072315

theorem tailTrace_4037154 : CollatzResearch.WordTrace tailWord_4037154 prefixEnd_4037154 1382000318814401900072315 := by
  unfold tailWord_4037154
  simp only [CollatzResearch.WordTrace]
  refine ⟨36811775804022005963781629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98164735477392015903417677 36811775804022005963781629)
  ·
    refine ⟨13804415926508252236418111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36811775804022005963781629 13804415926508252236418111)
    ·
      refine ⟨20706623889762378354627167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13804415926508252236418111 20706623889762378354627167)
      ·
        refine ⟨31059935834643567531940751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20706623889762378354627167 31059935834643567531940751)
        ·
          refine ⟨46589903751965351297911127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31059935834643567531940751 46589903751965351297911127)
          ·
            refine ⟨69884855627948026946866691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46589903751965351297911127 69884855627948026946866691)
            ·
              refine ⟨104827283441922040420300037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69884855627948026946866691 104827283441922040420300037)
              ·
                refine ⟨19655115645360382578806257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104827283441922040420300037 19655115645360382578806257)
                ·
                  refine ⟨14741336734020286934104693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19655115645360382578806257 14741336734020286934104693)
                  ·
                    refine ⟨1382000318814401900072315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14741336734020286934104693 1382000318814401900072315)
                    ·
                      rfl

theorem cell22_4037154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_4037154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037154 prefixEnd_4037154 := by exact prefixLift 4037154
  have htrace : WordTrace (prefixWord ++ tailWord_4037154) baseStart_4037154 baseEnd_4037154 := by
    simpa [prefixWord, tailWord_4037154, baseEnd_4037154] using wordTrace_append hprefix tailTrace_4037154
  have hstable : (prefixWord ++ tailWord_4037154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037154).length < 2 ^ (prefixWord ++ tailWord_4037154).sum := by decide
  have hdescent : baseEnd_4037154 < baseStart_4037154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037160 : List Nat := [2, 1, 5, 2, 1, 2, 1, 4, 1, 3]
def baseStart_4037160 : Nat := 118140960795 + 4037160 * 2 ^ 59
def prefixEnd_4037160 : Nat := 4983230072969 + 3 ^ 40 * 4037160 * 2
def baseEnd_4037160 : Nat := 1382002372737019884422297

theorem tailTrace_4037160 : CollatzResearch.WordTrace tailWord_4037160 prefixEnd_4037160 1382002372737019884422297 := by
  unfold tailWord_4037160
  simp only [CollatzResearch.WordTrace]
  refine ⟨73623661027033143439922467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98164881369377524586563289 73623661027033143439922467)
  ·
    refine ⟨110435491540549715159883701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73623661027033143439922467 110435491540549715159883701)
    ·
      refine ⟨10353327331926535796239097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110435491540549715159883701 10353327331926535796239097)
      ·
        refine ⟨7764995498944901847179323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10353327331926535796239097 7764995498944901847179323)
        ·
          refine ⟨11647493248417352770768985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7764995498944901847179323 11647493248417352770768985)
          ·
            refine ⟨8735619936313014578076739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11647493248417352770768985 8735619936313014578076739)
            ·
              refine ⟨13103429904469521867115109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8735619936313014578076739 13103429904469521867115109)
              ·
                refine ⟨2456893107088035350084083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13103429904469521867115109 2456893107088035350084083)
                ·
                  refine ⟨3685339660632053025126125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456893107088035350084083 3685339660632053025126125)
                  ·
                    refine ⟨1382002372737019884422297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3685339660632053025126125 1382002372737019884422297)
                    ·
                      rfl

theorem cell22_4037160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_4037160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037160 prefixEnd_4037160 := by exact prefixLift 4037160
  have htrace : WordTrace (prefixWord ++ tailWord_4037160) baseStart_4037160 baseEnd_4037160 := by
    simpa [prefixWord, tailWord_4037160, baseEnd_4037160] using wordTrace_append hprefix tailTrace_4037160
  have hstable : (prefixWord ++ tailWord_4037160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037160).length < 2 ^ (prefixWord ++ tailWord_4037160).sum := by decide
  have hdescent : baseEnd_4037160 < baseStart_4037160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037167 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 12]
def baseStart_4037167 : Nat := 118140960795 + 4037167 * 2 ^ 59
def prefixEnd_4037167 : Nat := 4983230072969 + 3 ^ 40 * 4037167 * 2
def baseEnd_4037167 : Nat := 460668256326691399832425

theorem tailTrace_4037167 : CollatzResearch.WordTrace tailWord_4037167 prefixEnd_4037167 460668256326691399832425 := by
  unfold tailWord_4037167
  simp only [CollatzResearch.WordTrace]
  refine ⟨147247577365040927075349755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98165051576693951383566503 147247577365040927075349755)
  ·
    refine ⟨220871366047561390613024633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147247577365040927075349755 220871366047561390613024633)
    ·
      refine ⟨165653524535671042959768475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220871366047561390613024633 165653524535671042959768475)
      ·
        refine ⟨248480286803506564439652713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165653524535671042959768475 248480286803506564439652713)
        ·
          refine ⟨186360215102629923329739535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248480286803506564439652713 186360215102629923329739535)
          ·
            refine ⟨279540322653944884994609303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186360215102629923329739535 279540322653944884994609303)
            ·
              refine ⟨419310483980917327491913955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279540322653944884994609303 419310483980917327491913955)
              ·
                refine ⟨628965725971375991237870933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419310483980917327491913955 628965725971375991237870933)
                ·
                  refine ⟨460668256326691399832425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 628965725971375991237870933 460668256326691399832425)
                  ·
                    rfl

theorem cell22_4037167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 12].length) (baseStart_4037167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037167 prefixEnd_4037167 := by exact prefixLift 4037167
  have htrace : WordTrace (prefixWord ++ tailWord_4037167) baseStart_4037167 baseEnd_4037167 := by
    simpa [prefixWord, tailWord_4037167, baseEnd_4037167] using wordTrace_append hprefix tailTrace_4037167
  have hstable : (prefixWord ++ tailWord_4037167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037167).length < 2 ^ (prefixWord ++ tailWord_4037167).sum := by decide
  have hdescent : baseEnd_4037167 < baseStart_4037167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037169 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_4037169 : Nat := 118140960795 + 4037169 * 2 ^ 59
def prefixEnd_4037169 : Nat := 4983230072969 + 3 ^ 40 * 4037169 * 2
def baseEnd_4037169 : Nat := 1382005453620946860947269

theorem tailTrace_4037169 : CollatzResearch.WordTrace tailWord_4037169 prefixEnd_4037169 1382005453620946860947269 := by
  unfold tailWord_4037169
  simp only [CollatzResearch.WordTrace]
  refine ⟨147247650311033681416922561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98165100207355787611281707 147247650311033681416922561)
  ·
    refine ⟨110435737733275261062691921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147247650311033681416922561 110435737733275261062691921)
    ·
      refine ⟨82826803299956445797018941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110435737733275261062691921 82826803299956445797018941)
      ·
        refine ⟨31060051237483667173882103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82826803299956445797018941 31060051237483667173882103)
        ·
          refine ⟨46590076856225500760823155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31060051237483667173882103 46590076856225500760823155)
          ·
            refine ⟨69885115284338251141234733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46590076856225500760823155 69885115284338251141234733)
            ·
              refine ⟨26206918231626844177963025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69885115284338251141234733 26206918231626844177963025)
              ·
                refine ⟨19655188673720133133472269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26206918231626844177963025 19655188673720133133472269)
                ·
                  refine ⟨7370695752645049925052101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19655188673720133133472269 7370695752645049925052101)
                  ·
                    refine ⟨1382005453620946860947269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7370695752645049925052101 1382005453620946860947269)
                    ·
                      rfl

theorem cell22_4037169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_4037169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037169 prefixEnd_4037169 := by exact prefixLift 4037169
  have htrace : WordTrace (prefixWord ++ tailWord_4037169) baseStart_4037169 baseEnd_4037169 := by
    simpa [prefixWord, tailWord_4037169, baseEnd_4037169] using wordTrace_append hprefix tailTrace_4037169
  have hstable : (prefixWord ++ tailWord_4037169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037169).length < 2 ^ (prefixWord ++ tailWord_4037169).sum := by decide
  have hdescent : baseEnd_4037169 < baseStart_4037169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037199 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 1, 5]
def baseStart_4037199 : Nat := 118140960795 + 4037199 * 2 ^ 59
def prefixEnd_4037199 : Nat := 4983230072969 + 3 ^ 40 * 4037199 * 2
def baseEnd_4037199 : Nat := 1382015723234036782697177

theorem tailTrace_4037199 : CollatzResearch.WordTrace tailWord_4037199 prefixEnd_4037199 1382015723234036782697177 := by
  unfold tailWord_4037199
  simp only [CollatzResearch.WordTrace]
  refine ⟨147248744500924996540514651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98165829667283331027009767 147248744500924996540514651)
  ·
    refine ⟨220873116751387494810771977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147248744500924996540514651 220873116751387494810771977)
    ·
      refine ⟨165654837563540621108078983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220873116751387494810771977 165654837563540621108078983)
      ·
        refine ⟨248482256345310931662118475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165654837563540621108078983 248482256345310931662118475)
        ·
          refine ⟨372723384517966397493177713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248482256345310931662118475 372723384517966397493177713)
          ·
            refine ⟨279542538388474798119883285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372723384517966397493177713 279542538388474798119883285)
            ·
              refine ⟨13103556486959756161869529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 279542538388474798119883285 13103556486959756161869529)
              ·
                refine ⟨9827667365219817121402147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13103556486959756161869529 9827667365219817121402147)
                ·
                  refine ⟨14741501047829725682103221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9827667365219817121402147 14741501047829725682103221)
                  ·
                    refine ⟨1382015723234036782697177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14741501047829725682103221 1382015723234036782697177)
                    ·
                      rfl

theorem cell22_4037199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_4037199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037199 prefixEnd_4037199 := by exact prefixLift 4037199
  have htrace : WordTrace (prefixWord ++ tailWord_4037199) baseStart_4037199 baseEnd_4037199 := by
    simpa [prefixWord, tailWord_4037199, baseEnd_4037199] using wordTrace_append hprefix tailTrace_4037199
  have hstable : (prefixWord ++ tailWord_4037199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037199).length < 2 ^ (prefixWord ++ tailWord_4037199).sum := by decide
  have hdescent : baseEnd_4037199 < baseStart_4037199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037201 : List Nat := [1, 2, 2, 1, 3, 3, 1, 5, 4]
def baseStart_4037201 : Nat := 118140960795 + 4037201 * 2 ^ 59
def prefixEnd_4037201 : Nat := 4983230072969 + 3 ^ 40 * 4037201 * 2
def baseEnd_4037201 : Nat := 460672135958303148049057

theorem tailTrace_4037201 : CollatzResearch.WordTrace tailWord_4037201 prefixEnd_4037201 460672135958303148049057 := by
  unfold tailWord_4037201
  simp only [CollatzResearch.WordTrace]
  refine ⟨147248817446917750882087457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98165878297945167254724971 147248817446917750882087457)
  ·
    refine ⟨110436613085188313161565593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147248817446917750882087457 110436613085188313161565593)
    ·
      refine ⟨82827459813891234871174195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110436613085188313161565593 82827459813891234871174195)
      ·
        refine ⟨124241189720836852306761293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82827459813891234871174195 124241189720836852306761293)
        ·
          refine ⟨46590446145313819615035485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124241189720836852306761293 46590446145313819615035485)
          ·
            refine ⟨17471417304492682355638307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46590446145313819615035485 17471417304492682355638307)
            ·
              refine ⟨26207125956739023533457461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17471417304492682355638307 26207125956739023533457461)
              ·
                refine ⟨2456918058444283456261637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26207125956739023533457461 2456918058444283456261637)
                ·
                  refine ⟨460672135958303148049057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2456918058444283456261637 460672135958303148049057)
                  ·
                    rfl

theorem cell22_4037201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 4].length) (baseStart_4037201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037201 prefixEnd_4037201 := by exact prefixLift 4037201
  have htrace : WordTrace (prefixWord ++ tailWord_4037201) baseStart_4037201 baseEnd_4037201 := by
    simpa [prefixWord, tailWord_4037201, baseEnd_4037201] using wordTrace_append hprefix tailTrace_4037201
  have hstable : (prefixWord ++ tailWord_4037201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037201).length < 2 ^ (prefixWord ++ tailWord_4037201).sum := by decide
  have hdescent : baseEnd_4037201 < baseStart_4037201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037319 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 10]
def baseStart_4037319 : Nat := 118140960795 + 4037319 * 2 ^ 59
def prefixEnd_4037319 : Nat := 4983230072969 + 3 ^ 40 * 4037319 * 2
def baseEnd_4037319 : Nat := 460685600562132156565603

theorem tailTrace_4037319 : CollatzResearch.WordTrace tailWord_4037319 prefixEnd_4037319 460685600562132156565603 := by
  unfold tailWord_4037319
  simp only [CollatzResearch.WordTrace]
  refine ⟨147253121260490257034883011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98168747506993504689922007 147253121260490257034883011)
  ·
    refine ⟨220879681890735385552324517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147253121260490257034883011 220879681890735385552324517)
    ·
      refine ⟨41414940354512884791060847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220879681890735385552324517 41414940354512884791060847)
      ·
        refine ⟨62122410531769327186591271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41414940354512884791060847 62122410531769327186591271)
        ·
          refine ⟨93183615797653990779886907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62122410531769327186591271 93183615797653990779886907)
          ·
            refine ⟨139775423696480986169830361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93183615797653990779886907 139775423696480986169830361)
            ·
              refine ⟨104831567772360739627372771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139775423696480986169830361 104831567772360739627372771)
              ·
                refine ⟨157247351658541109441059157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104831567772360739627372771 157247351658541109441059157)
                ·
                  refine ⟨460685600562132156565603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 157247351658541109441059157 460685600562132156565603)
                  ·
                    rfl

theorem cell22_4037319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 10].length) (baseStart_4037319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037319 prefixEnd_4037319 := by exact prefixLift 4037319
  have htrace : WordTrace (prefixWord ++ tailWord_4037319) baseStart_4037319 baseEnd_4037319 := by
    simpa [prefixWord, tailWord_4037319, baseEnd_4037319] using wordTrace_append hprefix tailTrace_4037319
  have hstable : (prefixWord ++ tailWord_4037319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037319).length < 2 ^ (prefixWord ++ tailWord_4037319).sum := by decide
  have hdescent : baseEnd_4037319 < baseStart_4037319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037413 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 3, 3]
def baseStart_4037413 : Nat := 118140960795 + 4037413 * 2 ^ 59
def prefixEnd_4037413 : Nat := 4983230072969 + 3 ^ 40 * 4037413 * 2
def baseEnd_4037413 : Nat := 1382088979807411557846521

theorem tailTrace_4037413 : CollatzResearch.WordTrace tailWord_4037413 prefixEnd_4037413 1382088979807411557846521 := by
  unfold tailWord_4037413
  simp only [CollatzResearch.WordTrace]
  refine ⟨147256549722149711088804893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98171033148099807392536595 147256549722149711088804893)
  ·
    refine ⟨55221206145806141658301835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147256549722149711088804893 55221206145806141658301835)
    ·
      refine ⟨82831809218709212487452753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55221206145806141658301835 82831809218709212487452753)
      ·
        refine ⟨62123856914031909365589565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82831809218709212487452753 62123856914031909365589565)
        ·
          refine ⟨23296446342761966012096087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62123856914031909365589565 23296446342761966012096087)
          ·
            refine ⟨34944669514142949018144131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23296446342761966012096087 34944669514142949018144131)
            ·
              refine ⟨52417004271214423527216197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34944669514142949018144131 52417004271214423527216197)
              ·
                refine ⟨9828188300852704411353037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52417004271214423527216197 9828188300852704411353037)
                ·
                  refine ⟨3685570612819764154257389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9828188300852704411353037 3685570612819764154257389)
                  ·
                    refine ⟨1382088979807411557846521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3685570612819764154257389 1382088979807411557846521)
                    ·
                      rfl

theorem cell22_4037413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_4037413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037413 prefixEnd_4037413 := by exact prefixLift 4037413
  have htrace : WordTrace (prefixWord ++ tailWord_4037413) baseStart_4037413 baseEnd_4037413 := by
    simpa [prefixWord, tailWord_4037413, baseEnd_4037413] using wordTrace_append hprefix tailTrace_4037413
  have hstable : (prefixWord ++ tailWord_4037413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037413).length < 2 ^ (prefixWord ++ tailWord_4037413).sum := by decide
  have hdescent : baseEnd_4037413 < baseStart_4037413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037421 : List Nat := [1, 5, 3, 2, 2, 1, 1, 3, 4]
def baseStart_4037421 : Nat := 118140960795 + 4037421 * 2 ^ 59
def prefixEnd_4037421 : Nat := 4983230072969 + 3 ^ 40 * 4037421 * 2
def baseEnd_4037421 : Nat := 460697239456967401215499

theorem tailTrace_4037421 : CollatzResearch.WordTrace tailWord_4037421 prefixEnd_4037421 460697239456967401215499 := by
  unfold tailWord_4037421
  simp only [CollatzResearch.WordTrace]
  refine ⟨147256841506120728455096117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98171227670747152303397411 147256841506120728455096117)
  ·
    refine ⟨13805328891198818292665261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147256841506120728455096117 13805328891198818292665261)
    ·
      refine ⟨5176998334199556859749473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13805328891198818292665261 5176998334199556859749473)
      ·
        refine ⟨3882748750649667644812105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5176998334199556859749473 3882748750649667644812105)
        ·
          refine ⟨2912061562987250733609079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3882748750649667644812105 2912061562987250733609079)
          ·
            refine ⟨4368092344480876100413619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912061562987250733609079 4368092344480876100413619)
            ·
              refine ⟨6552138516721314150620429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368092344480876100413619 6552138516721314150620429)
              ·
                refine ⟨2457051943770492806482661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6552138516721314150620429 2457051943770492806482661)
                ·
                  refine ⟨460697239456967401215499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457051943770492806482661 460697239456967401215499)
                  ·
                    rfl

theorem cell22_4037421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_4037421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037421 prefixEnd_4037421 := by exact prefixLift 4037421
  have htrace : WordTrace (prefixWord ++ tailWord_4037421) baseStart_4037421 baseEnd_4037421 := by
    simpa [prefixWord, tailWord_4037421, baseEnd_4037421] using wordTrace_append hprefix tailTrace_4037421
  have hstable : (prefixWord ++ tailWord_4037421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037421).length < 2 ^ (prefixWord ++ tailWord_4037421).sum := by decide
  have hdescent : baseEnd_4037421 < baseStart_4037421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037426 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_4037426 : Nat := 118140960795 + 4037426 * 2 ^ 59
def prefixEnd_4037426 : Nat := 4983230072969 + 3 ^ 40 * 4037426 * 2
def baseEnd_4037426 : Nat := 460697809991027952423827

theorem tailTrace_4037426 : CollatzResearch.WordTrace tailWord_4037426 prefixEnd_4037426 460697809991027952423827 := by
  unfold tailWord_4037426
  simp only [CollatzResearch.WordTrace]
  refine ⟨36814255967775653577257033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98171349247401742872685421 36814255967775653577257033)
  ·
    refine ⟨27610691975831740182942775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36814255967775653577257033 27610691975831740182942775)
    ·
      refine ⟨41416037963747610274414163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27610691975831740182942775 41416037963747610274414163)
      ·
        refine ⟨62124056945621415411621245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41416037963747610274414163 62124056945621415411621245)
        ·
          refine ⟨23296521354608030779357967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62124056945621415411621245 23296521354608030779357967)
          ·
            refine ⟨34944782031912046169036951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23296521354608030779357967 34944782031912046169036951)
            ·
              refine ⟨52417173047868069253555427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34944782031912046169036951 52417173047868069253555427)
              ·
                refine ⟨78625759571802103880333141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52417173047868069253555427 78625759571802103880333141)
                ·
                  refine ⟨460697809991027952423827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78625759571802103880333141 460697809991027952423827)
                  ·
                    rfl

theorem cell22_4037426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_4037426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037426 prefixEnd_4037426 := by exact prefixLift 4037426
  have htrace : WordTrace (prefixWord ++ tailWord_4037426) baseStart_4037426 baseEnd_4037426 := by
    simpa [prefixWord, tailWord_4037426, baseEnd_4037426] using wordTrace_append hprefix tailTrace_4037426
  have hstable : (prefixWord ++ tailWord_4037426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037426).length < 2 ^ (prefixWord ++ tailWord_4037426).sum := by decide
  have hdescent : baseEnd_4037426 < baseStart_4037426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037460 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 5]
def baseStart_4037460 : Nat := 118140960795 + 4037460 * 2 ^ 59
def prefixEnd_4037460 : Nat := 4983230072969 + 3 ^ 40 * 4037460 * 2
def baseEnd_4037460 : Nat := 460701689622639700640459

theorem tailTrace_4037460 : CollatzResearch.WordTrace tailWord_4037460 prefixEnd_4037460 460701689622639700640459 := by
  unfold tailWord_4037460
  simp only [CollatzResearch.WordTrace]
  refine ⟨73629131976489719057882917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98172175968652958743843889 73629131976489719057882917)
  ·
    refine ⟨13805462245591822323353047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73629131976489719057882917 13805462245591822323353047)
    ·
      refine ⟨20708193368387733485029571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13805462245591822323353047 20708193368387733485029571)
      ·
        refine ⟨31062290052581600227544357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20708193368387733485029571 31062290052581600227544357)
        ·
          refine ⟨5824179384859050042664567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31062290052581600227544357 5824179384859050042664567)
          ·
            refine ⟨8736269077288575063996851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5824179384859050042664567 8736269077288575063996851)
            ·
              refine ⟨13104403615932862595995277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8736269077288575063996851 13104403615932862595995277)
              ·
                refine ⟨4914151355974823473498229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13104403615932862595995277 4914151355974823473498229)
                ·
                  refine ⟨460701689622639700640459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4914151355974823473498229 460701689622639700640459)
                  ·
                    rfl

theorem cell22_4037460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_4037460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037460 prefixEnd_4037460 := by exact prefixLift 4037460
  have htrace : WordTrace (prefixWord ++ tailWord_4037460) baseStart_4037460 baseEnd_4037460 := by
    simpa [prefixWord, tailWord_4037460, baseEnd_4037460] using wordTrace_append hprefix tailTrace_4037460
  have hstable : (prefixWord ++ tailWord_4037460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037460).length < 2 ^ (prefixWord ++ tailWord_4037460).sum := by decide
  have hdescent : baseEnd_4037460 < baseStart_4037460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037471 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 8]
def baseStart_4037471 : Nat := 118140960795 + 4037471 * 2 ^ 59
def prefixEnd_4037471 : Nat := 4983230072969 + 3 ^ 40 * 4037471 * 2
def baseEnd_4037471 : Nat := 460702944797572913298781

theorem tailTrace_4037471 : CollatzResearch.WordTrace tailWord_4037471 prefixEnd_4037471 460702944797572913298781 := by
  unfold tailWord_4037471
  simp only [CollatzResearch.WordTrace]
  refine ⟨147258665155939586994416267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98172443437293057996277511 147258665155939586994416267)
  ·
    refine ⟨220887997733909380491624401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147258665155939586994416267 220887997733909380491624401)
    ·
      refine ⟨165665998300432035368718301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220887997733909380491624401 165665998300432035368718301)
      ·
        refine ⟨62124749362662013263269363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165665998300432035368718301 62124749362662013263269363)
        ·
          refine ⟨93187124043993019894904045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62124749362662013263269363 93187124043993019894904045)
          ·
            refine ⟨34945171516497382460589017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93187124043993019894904045 34945171516497382460589017)
            ·
              refine ⟨26208878637373036845441763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34945171516497382460589017 26208878637373036845441763)
              ·
                refine ⟨39313317956059555268162645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26208878637373036845441763 39313317956059555268162645)
                ·
                  refine ⟨460702944797572913298781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39313317956059555268162645 460702944797572913298781)
                  ·
                    rfl

theorem cell22_4037471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 8].length) (baseStart_4037471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037471 prefixEnd_4037471 := by exact prefixLift 4037471
  have htrace : WordTrace (prefixWord ++ tailWord_4037471) baseStart_4037471 baseEnd_4037471 := by
    simpa [prefixWord, tailWord_4037471, baseEnd_4037471] using wordTrace_append hprefix tailTrace_4037471
  have hstable : (prefixWord ++ tailWord_4037471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037471).length < 2 ^ (prefixWord ++ tailWord_4037471).sum := by decide
  have hdescent : baseEnd_4037471 < baseStart_4037471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037473 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 1, 4]
def baseStart_4037473 : Nat := 118140960795 + 4037473 * 2 ^ 59
def prefixEnd_4037473 : Nat := 4983230072969 + 3 ^ 40 * 4037473 * 2
def baseEnd_4037473 : Nat := 1382109519033591401346337

theorem tailTrace_4037473 : CollatzResearch.WordTrace tailWord_4037473 prefixEnd_4037473 1382109519033591401346337 := by
  unfold tailWord_4037473
  simp only [CollatzResearch.WordTrace]
  refine ⟨147258738101932341335989073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98172492067954894223992715 147258738101932341335989073)
  ·
    refine ⟨110444053576449256001991805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147258738101932341335989073 110444053576449256001991805)
    ·
      refine ⟨41416520091168471000746927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110444053576449256001991805 41416520091168471000746927)
      ·
        refine ⟨62124780136752706501120391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41416520091168471000746927 62124780136752706501120391)
        ·
          refine ⟨93187170205129059751680587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62124780136752706501120391 93187170205129059751680587)
          ·
            refine ⟨139780755307693589627520881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93187170205129059751680587 139780755307693589627520881)
            ·
              refine ⟨104835566480770192220640661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139780755307693589627520881 104835566480770192220640661)
              ·
                refine ⟨4914167178786102760342531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104835566480770192220640661 4914167178786102760342531)
                ·
                  refine ⟨7371250768179154140513797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4914167178786102760342531 7371250768179154140513797)
                  ·
                    refine ⟨1382109519033591401346337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7371250768179154140513797 1382109519033591401346337)
                    ·
                      rfl

theorem cell22_4037473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_4037473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037473 prefixEnd_4037473 := by exact prefixLift 4037473
  have htrace : WordTrace (prefixWord ++ tailWord_4037473) baseStart_4037473 baseEnd_4037473 := by
    simpa [prefixWord, tailWord_4037473, baseEnd_4037473] using wordTrace_append hprefix tailTrace_4037473
  have hstable : (prefixWord ++ tailWord_4037473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037473).length < 2 ^ (prefixWord ++ tailWord_4037473).sum := by decide
  have hdescent : baseEnd_4037473 < baseStart_4037473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037503 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 4, 3]
def baseStart_4037503 : Nat := 118140960795 + 4037503 * 2 ^ 59
def prefixEnd_4037503 : Nat := 4983230072969 + 3 ^ 40 * 4037503 * 2
def baseEnd_4037503 : Nat := 1382119788646681323096245

theorem tailTrace_4037503 : CollatzResearch.WordTrace tailWord_4037503 prefixEnd_4037503 1382119788646681323096245 := by
  unfold tailWord_4037503
  simp only [CollatzResearch.WordTrace]
  refine ⟨147259832291823656459581163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98173221527882437639720775 147259832291823656459581163)
  ·
    refine ⟨220889748437735484689371745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147259832291823656459581163 220889748437735484689371745)
    ·
      refine ⟨165667311328301613517028809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220889748437735484689371745 165667311328301613517028809)
      ·
        refine ⟨124250483496226210137771607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165667311328301613517028809 124250483496226210137771607)
        ·
          refine ⟨186375725244339315206657411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124250483496226210137771607 186375725244339315206657411)
          ·
            refine ⟨279563587866508972809986117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186375725244339315206657411 279563587866508972809986117)
            ·
              refine ⟨52418172724970432401872397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279563587866508972809986117 52418172724970432401872397)
              ·
                refine ⟨19656814771863912150702149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52418172724970432401872397 19656814771863912150702149)
                ·
                  refine ⟨3685652769724483528256653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19656814771863912150702149 3685652769724483528256653)
                  ·
                    refine ⟨1382119788646681323096245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3685652769724483528256653 1382119788646681323096245)
                    ·
                      rfl

theorem cell22_4037503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 3].length) (baseStart_4037503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037503 prefixEnd_4037503 := by exact prefixLift 4037503
  have htrace : WordTrace (prefixWord ++ tailWord_4037503) baseStart_4037503 baseEnd_4037503 := by
    simpa [prefixWord, tailWord_4037503, baseEnd_4037503] using wordTrace_append hprefix tailTrace_4037503
  have hstable : (prefixWord ++ tailWord_4037503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037503).length < 2 ^ (prefixWord ++ tailWord_4037503).sum := by decide
  have hdescent : baseEnd_4037503 < baseStart_4037503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037535 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 2, 4]
def baseStart_4037535 : Nat := 118140960795 + 4037535 * 2 ^ 59
def prefixEnd_4037535 : Nat := 4983230072969 + 3 ^ 40 * 4037535 * 2
def baseEnd_4037535 : Nat := 1382130742900643906296147

theorem tailTrace_4037535 : CollatzResearch.WordTrace tailWord_4037535 prefixEnd_4037535 1382130742900643906296147 := by
  unfold tailWord_4037535
  simp only [CollatzResearch.WordTrace]
  refine ⟨147260999427707725924746059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98173999618471817283164039 147260999427707725924746059)
  ·
    refine ⟨220891499141561588887119089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147260999427707725924746059 220891499141561588887119089)
    ·
      refine ⟨165668624356171191665339317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220891499141561588887119089 165668624356171191665339317)
      ·
        refine ⟨15531433533391049218625561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165668624356171191665339317 15531433533391049218625561)
        ·
          refine ⟨11648575150043286913969171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15531433533391049218625561 11648575150043286913969171)
          ·
            refine ⟨17472862725064930370953757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648575150043286913969171 17472862725064930370953757)
            ·
              refine ⟨6552323521899348889107659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17472862725064930370953757 6552323521899348889107659)
              ·
                refine ⟨9828485282849023333661489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6552323521899348889107659 9828485282849023333661489)
                ·
                  refine ⟨7371363962136767500246117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828485282849023333661489 7371363962136767500246117)
                  ·
                    refine ⟨1382130742900643906296147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7371363962136767500246117 1382130742900643906296147)
                    ·
                      rfl

theorem cell22_4037535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_4037535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037535 prefixEnd_4037535 := by exact prefixLift 4037535
  have htrace : WordTrace (prefixWord ++ tailWord_4037535) baseStart_4037535 baseEnd_4037535 := by
    simpa [prefixWord, tailWord_4037535, baseEnd_4037535] using wordTrace_append hprefix tailTrace_4037535
  have hstable : (prefixWord ++ tailWord_4037535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037535).length < 2 ^ (prefixWord ++ tailWord_4037535).sum := by decide
  have hdescent : baseEnd_4037535 < baseStart_4037535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037642 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_4037642 : Nat := 118140960795 + 4037642 * 2 ^ 59
def prefixEnd_4037642 : Nat := 4983230072969 + 3 ^ 40 * 4037642 * 2
def baseEnd_4037642 : Nat := 1382167371187331293870819

theorem tailTrace_4037642 : CollatzResearch.WordTrace tailWord_4037642 prefixEnd_4037642 1382167371187331293870819 := by
  unfold tailWord_4037642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36816225509580020799722795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98176601358880055465927453 36816225509580020799722795)
  ·
    refine ⟨55224338264370031199584193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36816225509580020799722795 55224338264370031199584193)
    ·
      refine ⟨41418253698277523399688145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55224338264370031199584193 41418253698277523399688145)
      ·
        refine ⟨31063690273708142549766109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41418253698277523399688145 31063690273708142549766109)
        ·
          refine ⟨11648883852640553456162291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31063690273708142549766109 11648883852640553456162291)
          ·
            refine ⟨17473325778960830184243437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648883852640553456162291 17473325778960830184243437)
            ·
              refine ⟨6552497167110311319091289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17473325778960830184243437 6552497167110311319091289)
              ·
                refine ⟨4914372875332733489318467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6552497167110311319091289 4914372875332733489318467)
                ·
                  refine ⟨7371559312999100233977701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4914372875332733489318467 7371559312999100233977701)
                  ·
                    refine ⟨1382167371187331293870819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7371559312999100233977701 1382167371187331293870819)
                    ·
                      rfl

theorem cell22_4037642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_4037642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037642 prefixEnd_4037642 := by exact prefixLift 4037642
  have htrace : WordTrace (prefixWord ++ tailWord_4037642) baseStart_4037642 baseEnd_4037642 := by
    simpa [prefixWord, tailWord_4037642, baseEnd_4037642] using wordTrace_append hprefix tailTrace_4037642
  have hstable : (prefixWord ++ tailWord_4037642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037642).length < 2 ^ (prefixWord ++ tailWord_4037642).sum := by decide
  have hdescent : baseEnd_4037642 < baseStart_4037642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037655 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 3, 5]
def baseStart_4037655 : Nat := 118140960795 + 4037655 * 2 ^ 59
def prefixEnd_4037655 : Nat := 4983230072969 + 3 ^ 40 * 4037655 * 2
def baseEnd_4037655 : Nat := 1382171821353003593295779

theorem tailTrace_4037655 : CollatzResearch.WordTrace tailWord_4037655 prefixEnd_4037655 1382171821353003593295779 := by
  unfold tailWord_4037655
  simp only [CollatzResearch.WordTrace]
  refine ⟨147265376187272986419114419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98176917458181990946076279 147265376187272986419114419)
  ·
    refine ⟨220898064280909479628671629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147265376187272986419114419 220898064280909479628671629)
    ·
      refine ⟨82836774105341054860751861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220898064280909479628671629 82836774105341054860751861)
      ·
        refine ⟨7765947572375723893195487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82836774105341054860751861 7765947572375723893195487)
        ·
          refine ⟨11648921358563585839793231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765947572375723893195487 11648921358563585839793231)
          ·
            refine ⟨17473382037845378759689847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648921358563585839793231 17473382037845378759689847)
            ·
              refine ⟨26210073056768068139534771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17473382037845378759689847 26210073056768068139534771)
              ·
                refine ⟨39315109585152102209302157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26210073056768068139534771 39315109585152102209302157)
                ·
                  refine ⟨14743166094432038328488309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39315109585152102209302157 14743166094432038328488309)
                  ·
                    refine ⟨1382171821353003593295779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14743166094432038328488309 1382171821353003593295779)
                    ·
                      rfl

theorem cell22_4037655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_4037655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037655 prefixEnd_4037655 := by exact prefixLift 4037655
  have htrace : WordTrace (prefixWord ++ tailWord_4037655) baseStart_4037655 baseEnd_4037655 := by
    simpa [prefixWord, tailWord_4037655, baseEnd_4037655] using wordTrace_append hprefix tailTrace_4037655
  have hstable : (prefixWord ++ tailWord_4037655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037655).length < 2 ^ (prefixWord ++ tailWord_4037655).sum := by decide
  have hdescent : baseEnd_4037655 < baseStart_4037655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037674 : List Nat := [3, 1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_4037674 : Nat := 118140960795 + 4037674 * 2 ^ 59
def prefixEnd_4037674 : Nat := 4983230072969 + 3 ^ 40 * 4037674 * 2
def baseEnd_4037674 : Nat := 460726108480431292356907

theorem tailTrace_4037674 : CollatzResearch.WordTrace tailWord_4037674 prefixEnd_4037674 460726108480431292356907 := by
  unfold tailWord_4037674
  simp only [CollatzResearch.WordTrace]
  refine ⟨36816517293551038166014019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98177379449469435109370717 36816517293551038166014019)
  ·
    refine ⟨55224775940326557249021029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36816517293551038166014019 55224775940326557249021029)
    ·
      refine ⟨10354645488811229484191443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55224775940326557249021029 10354645488811229484191443)
      ·
        refine ⟨15531968233216844226287165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10354645488811229484191443 15531968233216844226287165)
        ·
          refine ⟨5824488087456316584857687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15531968233216844226287165 5824488087456316584857687)
          ·
            refine ⟨8736732131184474877286531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5824488087456316584857687 8736732131184474877286531)
            ·
              refine ⟨13105098196776712315929797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8736732131184474877286531 13105098196776712315929797)
              ·
                refine ⟨2457205911895633559236837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13105098196776712315929797 2457205911895633559236837)
                ·
                  refine ⟨460726108480431292356907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457205911895633559236837 460726108480431292356907)
                  ·
                    rfl

theorem cell22_4037674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_4037674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037674 prefixEnd_4037674 := by exact prefixLift 4037674
  have htrace : WordTrace (prefixWord ++ tailWord_4037674) baseStart_4037674 baseEnd_4037674 := by
    simpa [prefixWord, tailWord_4037674, baseEnd_4037674] using wordTrace_append hprefix tailTrace_4037674
  have hstable : (prefixWord ++ tailWord_4037674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037674).length < 2 ^ (prefixWord ++ tailWord_4037674).sum := by decide
  have hdescent : baseEnd_4037674 < baseStart_4037674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037683 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 2, 7]
def baseStart_4037683 : Nat := 118140960795 + 4037683 * 2 ^ 59
def prefixEnd_4037683 : Nat := 4983230072969 + 3 ^ 40 * 4037683 * 2
def baseEnd_4037683 : Nat := 1382181406325220853595693

theorem tailTrace_4037683 : CollatzResearch.WordTrace tailWord_4037683 prefixEnd_4037683 1382181406325220853595693 := by
  unfold tailWord_4037683
  simp only [CollatzResearch.WordTrace]
  refine ⟨147266397431171547201133703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98177598287447698134089135 147266397431171547201133703)
  ·
    refine ⟨220899596146757320801700555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147266397431171547201133703 220899596146757320801700555)
    ·
      refine ⟨331349394220135981202550833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220899596146757320801700555 331349394220135981202550833)
      ·
        refine ⟨248512045665101985901913125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331349394220135981202550833 248512045665101985901913125)
        ·
          refine ⟨46596008562206622356608711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248512045665101985901913125 46596008562206622356608711)
          ·
            refine ⟨69894012843309933534913067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46596008562206622356608711 69894012843309933534913067)
            ·
              refine ⟨104841019264964900302369601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69894012843309933534913067 104841019264964900302369601)
              ·
                refine ⟨78630764448723675226777201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104841019264964900302369601 78630764448723675226777201)
                ·
                  refine ⟨58973073336542756420082901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78630764448723675226777201 58973073336542756420082901)
                  ·
                    refine ⟨1382181406325220853595693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58973073336542756420082901 1382181406325220853595693)
                    ·
                      rfl

theorem cell22_4037683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_4037683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037683 prefixEnd_4037683 := by exact prefixLift 4037683
  have htrace : WordTrace (prefixWord ++ tailWord_4037683) baseStart_4037683 baseEnd_4037683 := by
    simpa [prefixWord, tailWord_4037683, baseEnd_4037683] using wordTrace_append hprefix tailTrace_4037683
  have hstable : (prefixWord ++ tailWord_4037683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037683).length < 2 ^ (prefixWord ++ tailWord_4037683).sum := by decide
  have hdescent : baseEnd_4037683 < baseStart_4037683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037760 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_4037760 : Nat := 118140960795 + 4037760 * 2 ^ 59
def prefixEnd_4037760 : Nat := 4983230072969 + 3 ^ 40 * 4037760 * 2
def baseEnd_4037760 : Nat := 1382207764998818319420457

theorem tailTrace_4037760 : CollatzResearch.WordTrace tailWord_4037760 prefixEnd_4037760 1382207764998818319420457 := by
  unfold tailWord_4037760
  simp only [CollatzResearch.WordTrace]
  refine ⟨73634602925946294675843367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98179470567928392901124489 73634602925946294675843367)
  ·
    refine ⟨110451904388919442013765051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73634602925946294675843367 110451904388919442013765051)
    ·
      refine ⟨165677856583379163020647577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110451904388919442013765051 165677856583379163020647577)
      ·
        refine ⟨124258392437534372265485683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165677856583379163020647577 124258392437534372265485683)
        ·
          refine ⟨186387588656301558398228525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124258392437534372265485683 186387588656301558398228525)
          ·
            refine ⟨69895345746113084399335697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186387588656301558398228525 69895345746113084399335697)
            ·
              refine ⟨52421509309584813299501773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69895345746113084399335697 52421509309584813299501773)
              ·
                refine ⟨19658065991094304987313165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52421509309584813299501773 19658065991094304987313165)
                ·
                  refine ⟨7371774746660364370242437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19658065991094304987313165 7371774746660364370242437)
                  ·
                    refine ⟨1382207764998818319420457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7371774746660364370242437 1382207764998818319420457)
                    ·
                      rfl

theorem cell22_4037760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_4037760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037760 prefixEnd_4037760 := by exact prefixLift 4037760
  have htrace : WordTrace (prefixWord ++ tailWord_4037760) baseStart_4037760 baseEnd_4037760 := by
    simpa [prefixWord, tailWord_4037760, baseEnd_4037760] using wordTrace_append hprefix tailTrace_4037760
  have hstable : (prefixWord ++ tailWord_4037760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037760).length < 2 ^ (prefixWord ++ tailWord_4037760).sum := by decide
  have hdescent : baseEnd_4037760 < baseStart_4037760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037768 : List Nat := [2, 1, 3, 4, 2, 2, 1, 3, 1, 3]
def baseStart_4037768 : Nat := 118140960795 + 4037768 * 2 ^ 59
def prefixEnd_4037768 : Nat := 4983230072969 + 3 ^ 40 * 4037768 * 2
def baseEnd_4037768 : Nat := 1382210503562308965220433

theorem tailTrace_4037768 : CollatzResearch.WordTrace tailWord_4037768 prefixEnd_4037768 1382210503562308965220433 := by
  unfold tailWord_4037768
  simp only [CollatzResearch.WordTrace]
  refine ⟨73634748817931803358988979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98179665090575737811985305 73634748817931803358988979)
  ·
    refine ⟨110452123226897705038483469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73634748817931803358988979 110452123226897705038483469)
    ·
      refine ⟨41419546210086639389431301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110452123226897705038483469 41419546210086639389431301)
      ·
        refine ⟨7766164914391244885518369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41419546210086639389431301 7766164914391244885518369)
        ·
          refine ⟨5824623685793433664138777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7766164914391244885518369 5824623685793433664138777)
          ·
            refine ⟨4368467764345075248104083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5824623685793433664138777 4368467764345075248104083)
            ·
              refine ⟨6552701646517612872156125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368467764345075248104083 6552701646517612872156125)
              ·
                refine ⟨2457263117444104827058547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6552701646517612872156125 2457263117444104827058547)
                ·
                  refine ⟨3685894676166157240587821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457263117444104827058547 3685894676166157240587821)
                  ·
                    refine ⟨1382210503562308965220433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3685894676166157240587821 1382210503562308965220433)
                    ·
                      rfl

theorem cell22_4037768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_4037768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037768 prefixEnd_4037768 := by exact prefixLift 4037768
  have htrace : WordTrace (prefixWord ++ tailWord_4037768) baseStart_4037768 baseEnd_4037768 := by
    simpa [prefixWord, tailWord_4037768, baseEnd_4037768] using wordTrace_append hprefix tailTrace_4037768
  have hstable : (prefixWord ++ tailWord_4037768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037768).length < 2 ^ (prefixWord ++ tailWord_4037768).sum := by decide
  have hdescent : baseEnd_4037768 < baseStart_4037768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037869 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_4037869 : Nat := 118140960795 + 4037869 * 2 ^ 59
def prefixEnd_4037869 : Nat := 4983230072969 + 3 ^ 40 * 4037869 * 2
def baseEnd_4037869 : Nat := 1382245077926378368445123

theorem tailTrace_4037869 : CollatzResearch.WordTrace tailWord_4037869 prefixEnd_4037869 1382245077926378368445123 := by
  unfold tailWord_4037869
  simp only [CollatzResearch.WordTrace]
  refine ⟨147273181408497700967404661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98182120938998467311603107 147273181408497700967404661)
  ·
    refine ⟨13806860757046659465694187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147273181408497700967404661 13806860757046659465694187)
    ·
      refine ⟨20710291135569989198541281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13806860757046659465694187 20710291135569989198541281)
      ·
        refine ⟨15532718351677491898905961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20710291135569989198541281 15532718351677491898905961)
        ·
          refine ⟨11649538763758118924179471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15532718351677491898905961 11649538763758118924179471)
          ·
            refine ⟨17474308145637178386269207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11649538763758118924179471 17474308145637178386269207)
            ·
              refine ⟨26211462218455767579403811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17474308145637178386269207 26211462218455767579403811)
              ·
                refine ⟨39317193327683651369105717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26211462218455767579403811 39317193327683651369105717)
                ·
                  refine ⟨3685986874470342315853661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39317193327683651369105717 3685986874470342315853661)
                  ·
                    refine ⟨1382245077926378368445123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3685986874470342315853661 1382245077926378368445123)
                    ·
                      rfl

theorem cell22_4037869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_4037869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037869 prefixEnd_4037869 := by exact prefixLift 4037869
  have htrace : WordTrace (prefixWord ++ tailWord_4037869) baseStart_4037869 baseEnd_4037869 := by
    simpa [prefixWord, tailWord_4037869, baseEnd_4037869] using wordTrace_append hprefix tailTrace_4037869
  have hstable : (prefixWord ++ tailWord_4037869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037869).length < 2 ^ (prefixWord ++ tailWord_4037869).sum := by decide
  have hdescent : baseEnd_4037869 < baseStart_4037869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037899 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 5]
def baseStart_4037899 : Nat := 118140960795 + 4037899 * 2 ^ 59
def prefixEnd_4037899 : Nat := 4983230072969 + 3 ^ 40 * 4037899 * 2
def baseEnd_4037899 : Nat := 460751782513156096731677

theorem tailTrace_4037899 : CollatzResearch.WordTrace tailWord_4037899 prefixEnd_4037899 460751782513156096731677 := by
  unfold tailWord_4037899
  simp only [CollatzResearch.WordTrace]
  refine ⟨147274275598389016090996751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98182850398926010727331167 147274275598389016090996751)
  ·
    refine ⟨220911413397583524136495127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147274275598389016090996751 220911413397583524136495127)
    ·
      refine ⟨331367120096375286204742691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220911413397583524136495127 331367120096375286204742691)
      ·
        refine ⟨497050680144562929307114037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331367120096375286204742691 497050680144562929307114037)
        ·
          refine ⟨46598501263552774622541941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 497050680144562929307114037 46598501263552774622541941)
          ·
            refine ⟨4368609493458072620863307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46598501263552774622541941 4368609493458072620863307)
            ·
              refine ⟨6552914240187108931294961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368609493458072620863307 6552914240187108931294961)
              ·
                refine ⟨4914685680140331698471221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6552914240187108931294961 4914685680140331698471221)
                ·
                  refine ⟨460751782513156096731677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4914685680140331698471221 460751782513156096731677)
                  ·
                    rfl

theorem cell22_4037899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 5].length) (baseStart_4037899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037899 prefixEnd_4037899 := by exact prefixLift 4037899
  have htrace : WordTrace (prefixWord ++ tailWord_4037899) baseStart_4037899 baseEnd_4037899 := by
    simpa [prefixWord, tailWord_4037899, baseEnd_4037899] using wordTrace_append hprefix tailTrace_4037899
  have hstable : (prefixWord ++ tailWord_4037899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037899).length < 2 ^ (prefixWord ++ tailWord_4037899).sum := by decide
  have hdescent : baseEnd_4037899 < baseStart_4037899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037959 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 4, 3]
def baseStart_4037959 : Nat := 118140960795 + 4037959 * 2 ^ 59
def prefixEnd_4037959 : Nat := 4983230072969 + 3 ^ 40 * 4037959 * 2
def baseEnd_4037959 : Nat := 1382275886765648133694847

theorem tailTrace_4037959 : CollatzResearch.WordTrace tailWord_4037959 prefixEnd_4037959 1382275886765648133694847 := by
  unfold tailWord_4037959
  simp only [CollatzResearch.WordTrace]
  refine ⟨147276463978171646338180931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98184309318781097558787287 147276463978171646338180931)
  ·
    refine ⟨220914695967257469507271397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147276463978171646338180931 220914695967257469507271397)
    ·
      refine ⟨41421505493860775532613387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220914695967257469507271397 41421505493860775532613387)
      ·
        refine ⟨62132258240791163298920081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41421505493860775532613387 62132258240791163298920081)
        ·
          refine ⟨46599193680593372474190061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62132258240791163298920081 46599193680593372474190061)
          ·
            refine ⟨17474697630222514677821273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46599193680593372474190061 17474697630222514677821273)
            ·
              refine ⟨13106023222666886008365955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17474697630222514677821273 13106023222666886008365955)
              ·
                refine ⟨19659034834000329012548933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13106023222666886008365955 19659034834000329012548933)
                ·
                  refine ⟨3686069031375061689852925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19659034834000329012548933 3686069031375061689852925)
                  ·
                    refine ⟨1382275886765648133694847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3686069031375061689852925 1382275886765648133694847)
                    ·
                      rfl

theorem cell22_4037959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_4037959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037959 prefixEnd_4037959 := by exact prefixLift 4037959
  have htrace : WordTrace (prefixWord ++ tailWord_4037959) baseStart_4037959 baseEnd_4037959 := by
    simpa [prefixWord, tailWord_4037959, baseEnd_4037959] using wordTrace_append hprefix tailTrace_4037959
  have hstable : (prefixWord ++ tailWord_4037959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037959).length < 2 ^ (prefixWord ++ tailWord_4037959).sum := by decide
  have hdescent : baseEnd_4037959 < baseStart_4037959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037991 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 2, 4]
def baseStart_4037991 : Nat := 118140960795 + 4037991 * 2 ^ 59
def prefixEnd_4037991 : Nat := 4983230072969 + 3 ^ 40 * 4037991 * 2
def baseEnd_4037991 : Nat := 1382286841019610716894749

theorem tailTrace_4037991 : CollatzResearch.WordTrace tailWord_4037991 prefixEnd_4037991 1382286841019610716894749 := by
  unfold tailWord_4037991
  simp only [CollatzResearch.WordTrace]
  refine ⟨147277631114055715803345827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98185087409370477202230551 147277631114055715803345827)
  ·
    refine ⟨220916446671083573705018741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147277631114055715803345827 220916446671083573705018741)
    ·
      refine ⟨20710916875414085034845507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220916446671083573705018741 20710916875414085034845507)
      ·
        refine ⟨31066375313121127552268261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20710916875414085034845507 31066375313121127552268261)
        ·
          refine ⟨5824945371210211416050299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31066375313121127552268261 5824945371210211416050299)
          ·
            refine ⟨8737418056815317124075449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5824945371210211416050299 8737418056815317124075449)
            ·
              refine ⟨6553063542611487843056587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8737418056815317124075449 6553063542611487843056587)
              ·
                refine ⟨9829595313917231764584881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6553063542611487843056587 9829595313917231764584881)
                ·
                  refine ⟨7372196485437923823438661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9829595313917231764584881 7372196485437923823438661)
                  ·
                    refine ⟨1382286841019610716894749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7372196485437923823438661 1382286841019610716894749)
                    ·
                      rfl

theorem cell22_4037991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_4037991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4037991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4037991 prefixEnd_4037991 := by exact prefixLift 4037991
  have htrace : WordTrace (prefixWord ++ tailWord_4037991) baseStart_4037991 baseEnd_4037991 := by
    simpa [prefixWord, tailWord_4037991, baseEnd_4037991] using wordTrace_append hprefix tailTrace_4037991
  have hstable : (prefixWord ++ tailWord_4037991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037991).length < 2 ^ (prefixWord ++ tailWord_4037991).sum := by decide
  have hdescent : baseEnd_4037991 < baseStart_4037991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038113 : List Nat := [1, 2, 3, 1, 2, 5, 1, 3, 4]
def baseStart_4038113 : Nat := 118140960795 + 4038113 * 2 ^ 59
def prefixEnd_4038113 : Nat := 4983230072969 + 3 ^ 40 * 4038113 * 2
def baseEnd_4038113 : Nat := 460776201370947688448125

theorem tailTrace_4038113 : CollatzResearch.WordTrace tailWord_4038113 prefixEnd_4038113 460776201370947688448125 := by
  unfold tailWord_4038113
  simp only [CollatzResearch.WordTrace]
  refine ⟨147282080819613730639286993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98188053879742487092857995 147282080819613730639286993)
  ·
    refine ⟨110461560614710297979465245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147282080819613730639286993 110461560614710297979465245)
    ·
      refine ⟨41423085230516361742299467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110461560614710297979465245 41423085230516361742299467)
      ·
        refine ⟨62134627845774542613449201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41423085230516361742299467 62134627845774542613449201)
        ·
          refine ⟨46600970884330906960086901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62134627845774542613449201 46600970884330906960086901)
          ·
            refine ⟨4368841020406022527508147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46600970884330906960086901 4368841020406022527508147)
            ·
              refine ⟨6553261530609033791262221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368841020406022527508147 6553261530609033791262221)
              ·
                refine ⟨2457473073978387671723333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6553261530609033791262221 2457473073978387671723333)
                ·
                  refine ⟨460776201370947688448125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457473073978387671723333 460776201370947688448125)
                  ·
                    rfl

theorem cell22_4038113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 4].length) (baseStart_4038113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038113 prefixEnd_4038113 := by exact prefixLift 4038113
  have htrace : WordTrace (prefixWord ++ tailWord_4038113) baseStart_4038113 baseEnd_4038113 := by
    simpa [prefixWord, tailWord_4038113, baseEnd_4038113] using wordTrace_append hprefix tailTrace_4038113
  have hstable : (prefixWord ++ tailWord_4038113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038113).length < 2 ^ (prefixWord ++ tailWord_4038113).sum := by decide
  have hdescent : baseEnd_4038113 < baseStart_4038113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038126 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_4038126 : Nat := 118140960795 + 4038126 * 2 ^ 59
def prefixEnd_4038126 : Nat := 4983230072969 + 3 ^ 40 * 4038126 * 2
def baseEnd_4038126 : Nat := 1382333054278515364769335

theorem tailTrace_4038126 : CollatzResearch.WordTrace tailWord_4038126 prefixEnd_4038126 1382333054278515364769335 := by
  unfold tailWord_4038126
  simp only [CollatzResearch.WordTrace]
  refine ⟨18410319371070829232438779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98188369979044422573006821 18410319371070829232438779)
  ·
    refine ⟨27615479056606243848658169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18410319371070829232438779 27615479056606243848658169)
    ·
      refine ⟨20711609292454682886493627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27615479056606243848658169 20711609292454682886493627)
      ·
        refine ⟨31067413938682024329740441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20711609292454682886493627 31067413938682024329740441)
        ·
          refine ⟨23300560454011518247305331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31067413938682024329740441 23300560454011518247305331)
          ·
            refine ⟨34950840681017277370957997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23300560454011518247305331 34950840681017277370957997)
            ·
              refine ⟨13106565255381479014109249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34950840681017277370957997 13106565255381479014109249)
              ·
                refine ⟨9829923941536109260581937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13106565255381479014109249 9829923941536109260581937)
                ·
                  refine ⟨7372442956152081945436453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9829923941536109260581937 7372442956152081945436453)
                  ·
                    refine ⟨1382333054278515364769335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7372442956152081945436453 1382333054278515364769335)
                    ·
                      rfl

theorem cell22_4038126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_4038126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038126 prefixEnd_4038126 := by exact prefixLift 4038126
  have htrace : WordTrace (prefixWord ++ tailWord_4038126) baseStart_4038126 baseEnd_4038126 := by
    simpa [prefixWord, tailWord_4038126, baseEnd_4038126] using wordTrace_append hprefix tailTrace_4038126
  have hstable : (prefixWord ++ tailWord_4038126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038126).length < 2 ^ (prefixWord ++ tailWord_4038126).sum := by decide
  have hdescent : baseEnd_4038126 < baseStart_4038126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
