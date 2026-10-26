import V185TrunkScan22Chunk429

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3835027 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 2, 6]
def baseStart_3835027 : Nat := 118140960795 + 3835027 * 2 ^ 59
def prefixEnd_3835027 : Nat := 4983230072969 + 3 ^ 40 * 3835027 * 2
def baseEnd_3835027 : Nat := 1312808115980181448617025

theorem tailTrace_3835027 : CollatzResearch.WordTrace tailWord_3835027 prefixEnd_3835027 1312808115980181448617025 := by
  unfold tailWord_3835027
  simp only [CollatzResearch.WordTrace]
  refine ⟨139874925877359624311847335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93249950584906416207898223 139874925877359624311847335)
  ·
    refine ⟨209812388816039436467771003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139874925877359624311847335 209812388816039436467771003)
    ·
      refine ⟨314718583224059154701656505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209812388816039436467771003 314718583224059154701656505)
      ·
        refine ⟨236038937418044366026242379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314718583224059154701656505 236038937418044366026242379)
        ·
          refine ⟨354058406127066549039363569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236038937418044366026242379 354058406127066549039363569)
          ·
            refine ⟨265543804595299911779522677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354058406127066549039363569 265543804595299911779522677)
            ·
              refine ⟨24894731680809366729330251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265543804595299911779522677 24894731680809366729330251)
              ·
                refine ⟨37342097521214050093995377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24894731680809366729330251 37342097521214050093995377)
                ·
                  refine ⟨28006573140910537570496533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37342097521214050093995377 28006573140910537570496533)
                  ·
                    refine ⟨1312808115980181448617025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28006573140910537570496533 1312808115980181448617025)
                    ·
                      rfl

theorem cell22_3835027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_3835027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835027 prefixEnd_3835027 := by exact prefixLift 3835027
  have htrace : WordTrace (prefixWord ++ tailWord_3835027) baseStart_3835027 baseEnd_3835027 := by
    simpa [prefixWord, tailWord_3835027, baseEnd_3835027] using wordTrace_append hprefix tailTrace_3835027
  have hstable : (prefixWord ++ tailWord_3835027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835027).length < 2 ^ (prefixWord ++ tailWord_3835027).sum := by decide
  have hdescent : baseEnd_3835027 < baseStart_3835027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835063 : List Nat := [1, 1, 3, 1, 4, 1, 4, 3, 1, 3]
def baseStart_3835063 : Nat := 118140960795 + 3835063 * 2 ^ 59
def prefixEnd_3835063 : Nat := 4983230072969 + 3 ^ 40 * 3835063 * 2
def baseEnd_3835063 : Nat := 1312820439515889354716915

theorem tailTrace_3835063 : CollatzResearch.WordTrace tailWord_3835063 prefixEnd_3835063 1312820439515889354716915 := by
  unfold tailWord_3835063
  simp only [CollatzResearch.WordTrace]
  refine ⟨139876238905229202460157843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93250825936819468306771895 139876238905229202460157843)
  ·
    refine ⟨209814358357843803690236765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139876238905229202460157843 209814358357843803690236765)
    ·
      refine ⟨78680384384191426383838787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209814358357843803690236765 78680384384191426383838787)
      ·
        refine ⟨118020576576287139575758181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78680384384191426383838787 118020576576287139575758181)
        ·
          refine ⟨22128858108053838670454659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118020576576287139575758181 22128858108053838670454659)
          ·
            refine ⟨33193287162080758005681989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22128858108053838670454659 33193287162080758005681989)
            ·
              refine ⟨6223741342890142126065373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33193287162080758005681989 6223741342890142126065373)
              ·
                refine ⟨2333903003583803297274515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6223741342890142126065373 2333903003583803297274515)
                ·
                  refine ⟨3500854505375704945911773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333903003583803297274515 3500854505375704945911773)
                  ·
                    refine ⟨1312820439515889354716915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3500854505375704945911773 1312820439515889354716915)
                    ·
                      rfl

theorem cell22_3835063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_3835063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835063 prefixEnd_3835063 := by exact prefixLift 3835063
  have htrace : WordTrace (prefixWord ++ tailWord_3835063) baseStart_3835063 baseEnd_3835063 := by
    simpa [prefixWord, tailWord_3835063, baseEnd_3835063] using wordTrace_append hprefix tailTrace_3835063
  have hstable : (prefixWord ++ tailWord_3835063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835063).length < 2 ^ (prefixWord ++ tailWord_3835063).sum := by decide
  have hdescent : baseEnd_3835063 < baseStart_3835063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835076 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 7]
def baseStart_3835076 : Nat := 118140960795 + 3835076 * 2 ^ 59
def prefixEnd_3835076 : Nat := 4983230072969 + 3 ^ 40 * 3835076 * 2
def baseEnd_3835076 : Nat := 437608296560520551380625

theorem tailTrace_3835076 : CollatzResearch.WordTrace tailWord_3835076 prefixEnd_3835076 437608296560520551380625 := by
  unfold tailWord_3835076
  simp only [CollatzResearch.WordTrace]
  refine ⟨69938356527091052840190541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93251142036121403786920721 69938356527091052840190541)
  ·
    refine ⟨26226883697659144815071453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69938356527091052840190541 26226883697659144815071453)
    ·
      refine ⟨9835081386622179305651795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26226883697659144815071453 9835081386622179305651795)
      ·
        refine ⟨14752622079933268958477693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9835081386622179305651795 14752622079933268958477693)
        ·
          refine ⟨5532233279974975859429135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14752622079933268958477693 5532233279974975859429135)
          ·
            refine ⟨8298349919962463789143703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532233279974975859429135 8298349919962463789143703)
            ·
              refine ⟨12447524879943695683715555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298349919962463789143703 12447524879943695683715555)
              ·
                refine ⟨18671287319915543525573333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12447524879943695683715555 18671287319915543525573333)
                ·
                  refine ⟨437608296560520551380625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18671287319915543525573333 437608296560520551380625)
                  ·
                    rfl

theorem cell22_3835076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_3835076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835076 prefixEnd_3835076 := by exact prefixLift 3835076
  have htrace : WordTrace (prefixWord ++ tailWord_3835076) baseStart_3835076 baseEnd_3835076 := by
    simpa [prefixWord, tailWord_3835076, baseEnd_3835076] using wordTrace_append hprefix tailTrace_3835076
  have hstable : (prefixWord ++ tailWord_3835076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835076).length < 2 ^ (prefixWord ++ tailWord_3835076).sum := by decide
  have hdescent : baseEnd_3835076 < baseStart_3835076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835093 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 5]
def baseStart_3835093 : Nat := 118140960795 + 3835093 * 2 ^ 59
def prefixEnd_3835093 : Nat := 4983230072969 + 3 ^ 40 * 3835093 * 2
def baseEnd_3835093 : Nat := 437610236376326425488941

theorem tailTrace_3835093 : CollatzResearch.WordTrace tailWord_3835093 prefixEnd_3835093 437610236376326425488941 := by
  unfold tailWord_3835093
  simp only [CollatzResearch.WordTrace]
  refine ⟨139877333095120517583749933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93251555396747011722499955 139877333095120517583749933)
  ·
    refine ⟨52453999910670194093906225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139877333095120517583749933 52453999910670194093906225)
    ·
      refine ⟨39340499933002645570429669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52453999910670194093906225 39340499933002645570429669)
      ·
        refine ⟨7376343737437996044455563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39340499933002645570429669 7376343737437996044455563)
        ·
          refine ⟨11064515606156994066683345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376343737437996044455563 11064515606156994066683345)
          ·
            refine ⟨8298386704617745550012509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11064515606156994066683345 8298386704617745550012509)
            ·
              refine ⟨3111895014231654581254691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8298386704617745550012509 3111895014231654581254691)
              ·
                refine ⟨4667842521347481871882037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111895014231654581254691 4667842521347481871882037)
                ·
                  refine ⟨437610236376326425488941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4667842521347481871882037 437610236376326425488941)
                  ·
                    rfl

theorem cell22_3835093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_3835093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835093 prefixEnd_3835093 := by exact prefixLift 3835093
  have htrace : WordTrace (prefixWord ++ tailWord_3835093) baseStart_3835093 baseEnd_3835093 := by
    simpa [prefixWord, tailWord_3835093, baseEnd_3835093] using wordTrace_append hprefix tailTrace_3835093
  have hstable : (prefixWord ++ tailWord_3835093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835093).length < 2 ^ (prefixWord ++ tailWord_3835093).sum := by decide
  have hdescent : baseEnd_3835093 < baseStart_3835093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835104 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 6]
def baseStart_3835104 : Nat := 118140960795 + 3835104 * 2 ^ 59
def prefixEnd_3835104 : Nat := 4983230072969 + 3 ^ 40 * 3835104 * 2
def baseEnd_3835104 : Nat := 437611491551259638147263

theorem tailTrace_3835104 : CollatzResearch.WordTrace tailWord_3835104 prefixEnd_3835104 437611491551259638147263 := by
  unfold tailWord_3835104
  simp only [CollatzResearch.WordTrace]
  refine ⟨69938867149040333231200183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93251822865387110974933577 69938867149040333231200183)
  ·
    refine ⟨104908300723560499846800275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69938867149040333231200183 104908300723560499846800275)
    ·
      refine ⟨157362451085340749770200413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104908300723560499846800275 157362451085340749770200413)
      ·
        refine ⟨59010919157002781163825155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157362451085340749770200413 59010919157002781163825155)
        ·
          refine ⟨88516378735504171745737733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59010919157002781163825155 88516378735504171745737733)
          ·
            refine ⟨16596821012907032202325825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88516378735504171745737733 16596821012907032202325825)
            ·
              refine ⟨12447615759680274151744369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16596821012907032202325825 12447615759680274151744369)
              ·
                refine ⟨9335711819760205613808277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12447615759680274151744369 9335711819760205613808277)
                ·
                  refine ⟨437611491551259638147263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9335711819760205613808277 437611491551259638147263)
                  ·
                    rfl

theorem cell22_3835104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_3835104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835104 prefixEnd_3835104 := by exact prefixLift 3835104
  have htrace : WordTrace (prefixWord ++ tailWord_3835104) baseStart_3835104 baseEnd_3835104 := by
    simpa [prefixWord, tailWord_3835104, baseEnd_3835104] using wordTrace_append hprefix tailTrace_3835104
  have hstable : (prefixWord ++ tailWord_3835104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835104).length < 2 ^ (prefixWord ++ tailWord_3835104).sum := by decide
  have hdescent : baseEnd_3835104 < baseStart_3835104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835136 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 2, 3]
def baseStart_3835136 : Nat := 118140960795 + 3835136 * 2 ^ 59
def prefixEnd_3835136 : Nat := 4983230072969 + 3 ^ 40 * 3835136 * 2
def baseEnd_3835136 : Nat := 1312845428907741497641691

theorem tailTrace_3835136 : CollatzResearch.WordTrace tailWord_3835136 prefixEnd_3835136 1312845428907741497641691 := by
  unfold tailWord_3835136
  simp only [CollatzResearch.WordTrace]
  refine ⟨69939450716982367963782631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93252600955976490618376841 69939450716982367963782631)
  ·
    refine ⟨104909176075473551945673947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69939450716982367963782631 104909176075473551945673947)
    ·
      refine ⟨157363764113210327918510921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104909176075473551945673947 157363764113210327918510921)
      ·
        refine ⟨118022823084907745938883191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157363764113210327918510921 118022823084907745938883191)
        ·
          refine ⟨177034234627361618908324787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118022823084907745938883191 177034234627361618908324787)
          ·
            refine ⟨265551351941042428362487181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177034234627361618908324787 265551351941042428362487181)
            ·
              refine ⟨99581756977890910635932693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265551351941042428362487181 99581756977890910635932693)
              ·
                refine ⟨4667894858338636436059345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99581756977890910635932693 4667894858338636436059345)
                ·
                  refine ⟨3500921143753977327044509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4667894858338636436059345 3500921143753977327044509)
                  ·
                    refine ⟨1312845428907741497641691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3500921143753977327044509 1312845428907741497641691)
                    ·
                      rfl

theorem cell22_3835136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2, 3].length) (baseStart_3835136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835136 prefixEnd_3835136 := by exact prefixLift 3835136
  have htrace : WordTrace (prefixWord ++ tailWord_3835136) baseStart_3835136 baseEnd_3835136 := by
    simpa [prefixWord, tailWord_3835136, baseEnd_3835136] using wordTrace_append hprefix tailTrace_3835136
  have hstable : (prefixWord ++ tailWord_3835136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835136).length < 2 ^ (prefixWord ++ tailWord_3835136).sum := by decide
  have hdescent : baseEnd_3835136 < baseStart_3835136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835164 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_3835164 : Nat := 118140960795 + 3835164 * 2 ^ 59
def prefixEnd_3835164 : Nat := 4983230072969 + 3 ^ 40 * 3835164 * 2
def baseEnd_3835164 : Nat := 1312855013879958757941605

theorem tailTrace_3835164 : CollatzResearch.WordTrace tailWord_3835164 prefixEnd_3835164 1312855013879958757941605 := by
  unfold tailWord_3835164
  simp only [CollatzResearch.WordTrace]
  refine ⟨69939961338931648354792273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93253281785242197806389697 69939961338931648354792273)
  ·
    refine ⟨52454971004198736266094205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69939961338931648354792273 52454971004198736266094205)
    ·
      refine ⟨19670614126574526099785327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52454971004198736266094205 19670614126574526099785327)
      ·
        refine ⟨29505921189861789149677991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19670614126574526099785327 29505921189861789149677991)
        ·
          refine ⟨44258881784792683724516987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29505921189861789149677991 44258881784792683724516987)
          ·
            refine ⟨66388322677189025586775481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44258881784792683724516987 66388322677189025586775481)
            ·
              refine ⟨49791242007891769190081611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66388322677189025586775481 49791242007891769190081611)
              ·
                refine ⟨74686863011837653785122417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49791242007891769190081611 74686863011837653785122417)
                ·
                  refine ⟨56015147258878240338841813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74686863011837653785122417 56015147258878240338841813)
                  ·
                    refine ⟨1312855013879958757941605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56015147258878240338841813 1312855013879958757941605)
                    ·
                      rfl

theorem cell22_3835164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_3835164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835164 prefixEnd_3835164 := by exact prefixLift 3835164
  have htrace : WordTrace (prefixWord ++ tailWord_3835164) baseStart_3835164 baseEnd_3835164 := by
    simpa [prefixWord, tailWord_3835164, baseEnd_3835164] using wordTrace_append hprefix tailTrace_3835164
  have hstable : (prefixWord ++ tailWord_3835164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835164).length < 2 ^ (prefixWord ++ tailWord_3835164).sum := by decide
  have hdescent : baseEnd_3835164 < baseStart_3835164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835168 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 2, 4]
def baseStart_3835168 : Nat := 118140960795 + 3835168 * 2 ^ 59
def prefixEnd_3835168 : Nat := 4983230072969 + 3 ^ 40 * 3835168 * 2
def baseEnd_3835168 : Nat := 1312856383161704080841593

theorem tailTrace_3835168 : CollatzResearch.WordTrace tailWord_3835168 prefixEnd_3835168 1312856383161704080841593 := by
  unfold tailWord_3835168
  simp only [CollatzResearch.WordTrace]
  refine ⟨69940034284924402696365079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93253379046565870261820105 69940034284924402696365079)
  ·
    refine ⟨104910051427386604044547619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69940034284924402696365079 104910051427386604044547619)
    ·
      refine ⟨157365077141079906066821429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104910051427386604044547619 157365077141079906066821429)
      ·
        refine ⟨14752975981976241193764509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157365077141079906066821429 14752975981976241193764509)
        ·
          refine ⟨5532365993241090447661691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14752975981976241193764509 5532365993241090447661691)
          ·
            refine ⟨8298548989861635671492537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532365993241090447661691 8298548989861635671492537)
            ·
              refine ⟨6223911742396226753619403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8298548989861635671492537 6223911742396226753619403)
              ·
                refine ⟨9335867613594340130429105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223911742396226753619403 9335867613594340130429105)
                ·
                  refine ⟨7001900710195755097821829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9335867613594340130429105 7001900710195755097821829)
                  ·
                    refine ⟨1312856383161704080841593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001900710195755097821829 1312856383161704080841593)
                    ·
                      rfl

theorem cell22_3835168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_3835168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835168 prefixEnd_3835168 := by exact prefixLift 3835168
  have htrace : WordTrace (prefixWord ++ tailWord_3835168) baseStart_3835168 baseEnd_3835168 := by
    simpa [prefixWord, tailWord_3835168, baseEnd_3835168] using wordTrace_append hprefix tailTrace_3835168
  have hstable : (prefixWord ++ tailWord_3835168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835168).length < 2 ^ (prefixWord ++ tailWord_3835168).sum := by decide
  have hdescent : baseEnd_3835168 < baseStart_3835168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835198 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_3835198 : Nat := 118140960795 + 3835198 * 2 ^ 59
def prefixEnd_3835198 : Nat := 4983230072969 + 3 ^ 40 * 3835198 * 2
def baseEnd_3835198 : Nat := 1312866652774794002591501

theorem tailTrace_3835198 : CollatzResearch.WordTrace tailWord_3835198 prefixEnd_3835198 1312866652774794002591501 := by
  unfold tailWord_3835198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485145344967515064540281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93254108506493413677548165 17485145344967515064540281)
  ·
    refine ⟨13113859008725636298405211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17485145344967515064540281 13113859008725636298405211)
    ·
      refine ⟨19670788513088454447607817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13113859008725636298405211 19670788513088454447607817)
      ·
        refine ⟨14753091384816340835705863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19670788513088454447607817 14753091384816340835705863)
        ·
          refine ⟨22129637077224511253558795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14753091384816340835705863 22129637077224511253558795)
          ·
            refine ⟨33194455615836766880338193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22129637077224511253558795 33194455615836766880338193)
            ·
              refine ⟨24895841711877575160253645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33194455615836766880338193 24895841711877575160253645)
              ·
                refine ⟨9335940641954090685095117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24895841711877575160253645 9335940641954090685095117)
                ·
                  refine ⟨3500977740732784006910669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9335940641954090685095117 3500977740732784006910669)
                  ·
                    refine ⟨1312866652774794002591501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3500977740732784006910669 1312866652774794002591501)
                    ·
                      rfl

theorem cell22_3835198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_3835198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835198 prefixEnd_3835198 := by exact prefixLift 3835198
  have htrace : WordTrace (prefixWord ++ tailWord_3835198) baseStart_3835198 baseEnd_3835198 := by
    simpa [prefixWord, tailWord_3835198, baseEnd_3835198] using wordTrace_append hprefix tailTrace_3835198
  have hstable : (prefixWord ++ tailWord_3835198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835198).length < 2 ^ (prefixWord ++ tailWord_3835198).sum := by decide
  have hdescent : baseEnd_3835198 < baseStart_3835198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835209 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_3835209 : Nat := 118140960795 + 3835209 * 2 ^ 59
def prefixEnd_3835209 : Nat := 4983230072969 + 3 ^ 40 * 3835209 * 2
def baseEnd_3835209 : Nat := 1312870418299593640566467

theorem tailTrace_3835209 : CollatzResearch.WordTrace tailWord_3835209 prefixEnd_3835209 1312870418299593640566467 := by
  unfold tailWord_3835209
  simp only [CollatzResearch.WordTrace]
  refine ⟨139881563962700269394972681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93254375975133512929981787 139881563962700269394972681)
  ·
    refine ⟨104911172972025202046229511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139881563962700269394972681 104911172972025202046229511)
    ·
      refine ⟨157366759458037803069344267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104911172972025202046229511 157366759458037803069344267)
      ·
        refine ⟨236050139187056704604016401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157366759458037803069344267 236050139187056704604016401)
        ·
          refine ⟨177037604390292528453012301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236050139187056704604016401 177037604390292528453012301)
          ·
            refine ⟨66389101646359698169879613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177037604390292528453012301 66389101646359698169879613)
            ·
              refine ⟨24895913117384886813704855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66389101646359698169879613 24895913117384886813704855)
              ·
                refine ⟨37343869676077330220557283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24895913117384886813704855 37343869676077330220557283)
                ·
                  refine ⟨56015804514115995330835925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37343869676077330220557283 56015804514115995330835925)
                  ·
                    refine ⟨1312870418299593640566467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56015804514115995330835925 1312870418299593640566467)
                    ·
                      rfl

theorem cell22_3835209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_3835209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835209 prefixEnd_3835209 := by exact prefixLift 3835209
  have htrace : WordTrace (prefixWord ++ tailWord_3835209) baseStart_3835209 baseEnd_3835209 := by
    simpa [prefixWord, tailWord_3835209, baseEnd_3835209] using wordTrace_append hprefix tailTrace_3835209
  have hstable : (prefixWord ++ tailWord_3835209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835209).length < 2 ^ (prefixWord ++ tailWord_3835209).sum := by decide
  have hdescent : baseEnd_3835209 < baseStart_3835209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835303 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3835303 : Nat := 118140960795 + 3835303 * 2 ^ 59
def prefixEnd_3835303 : Nat := 4983230072969 + 3 ^ 40 * 3835303 * 2
def baseEnd_3835303 : Nat := 1312902596420608728716179

theorem tailTrace_3835303 : CollatzResearch.WordTrace tailWord_3835303 prefixEnd_3835303 1312902596420608728716179 := by
  unfold tailWord_3835303
  simp only [CollatzResearch.WordTrace]
  refine ⟨139884992424359723448894563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93256661616239815632596375 139884992424359723448894563)
  ·
    refine ⟨209827488636539585173341845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139884992424359723448894563 209827488636539585173341845)
    ·
      refine ⟨9835663529837793055000399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209827488636539585173341845 9835663529837793055000399)
      ·
        refine ⟨14753495294756689582500599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9835663529837793055000399 14753495294756689582500599)
        ·
          refine ⟨22130242942135034373750899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14753495294756689582500599 22130242942135034373750899)
          ·
            refine ⟨33195364413202551560626349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22130242942135034373750899 33195364413202551560626349)
            ·
              refine ⟨12448261654950956835234881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33195364413202551560626349 12448261654950956835234881)
              ·
                refine ⟨9336196241213217626426161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12448261654950956835234881 9336196241213217626426161)
                ·
                  refine ⟨7002147180909913219819621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9336196241213217626426161 7002147180909913219819621)
                  ·
                    refine ⟨1312902596420608728716179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7002147180909913219819621 1312902596420608728716179)
                    ·
                      rfl

theorem cell22_3835303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3835303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835303 prefixEnd_3835303 := by exact prefixLift 3835303
  have htrace : WordTrace (prefixWord ++ tailWord_3835303) baseStart_3835303 baseEnd_3835303 := by
    simpa [prefixWord, tailWord_3835303, baseEnd_3835303] using wordTrace_append hprefix tailTrace_3835303
  have hstable : (prefixWord ++ tailWord_3835303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835303).length < 2 ^ (prefixWord ++ tailWord_3835303).sum := by decide
  have hdescent : baseEnd_3835303 < baseStart_3835303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835363 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 5]
def baseStart_3835363 : Nat := 118140960795 + 3835363 * 2 ^ 59
def prefixEnd_3835363 : Nat := 4983230072969 + 3 ^ 40 * 3835363 * 2
def baseEnd_3835363 : Nat := 437641045215596190738665

theorem tailTrace_3835363 : CollatzResearch.WordTrace tailWord_3835363 prefixEnd_3835363 437641045215596190738665 := by
  unfold tailWord_3835363
  simp only [CollatzResearch.WordTrace]
  refine ⟨139887180804142353696078743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93258120536094902464052495 139887180804142353696078743)
  ·
    refine ⟨209830771206213530544118115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139887180804142353696078743 209830771206213530544118115)
    ·
      refine ⟨314746156809320295816177173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209830771206213530544118115 314746156809320295816177173)
      ·
        refine ⟨14753726100436888866383305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 314746156809320295816177173 14753726100436888866383305)
        ·
          refine ⟨11065294575327666649787479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14753726100436888866383305 11065294575327666649787479)
          ·
            refine ⟨16597941862991499974681219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11065294575327666649787479 16597941862991499974681219)
            ·
              refine ⟨24896912794487249962021829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16597941862991499974681219 24896912794487249962021829)
              ·
                refine ⟨4668171148966359367879093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24896912794487249962021829 4668171148966359367879093)
                ·
                  refine ⟨437641045215596190738665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4668171148966359367879093 437641045215596190738665)
                  ·
                    rfl

theorem cell22_3835363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 5].length) (baseStart_3835363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835363 prefixEnd_3835363 := by exact prefixLift 3835363
  have htrace : WordTrace (prefixWord ++ tailWord_3835363) baseStart_3835363 baseEnd_3835363 := by
    simpa [prefixWord, tailWord_3835363, baseEnd_3835363] using wordTrace_append hprefix tailTrace_3835363
  have hstable : (prefixWord ++ tailWord_3835363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835363).length < 2 ^ (prefixWord ++ tailWord_3835363).sum := by decide
  have hdescent : baseEnd_3835363 < baseStart_3835363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835367 : List Nat := [1, 1, 5, 2, 1, 3, 1, 4, 1, 3]
def baseStart_3835367 : Nat := 118140960795 + 3835367 * 2 ^ 59
def prefixEnd_3835367 : Nat := 4983230072969 + 3 ^ 40 * 3835367 * 2
def baseEnd_3835367 : Nat := 1312924504928533895115983

theorem tailTrace_3835367 : CollatzResearch.WordTrace tailWord_3835367 prefixEnd_3835367 1312924504928533895115983 := by
  unfold tailWord_3835367
  simp only [CollatzResearch.WordTrace]
  refine ⟨139887326696127862379224355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93258217797418574919482903 139887326696127862379224355)
  ·
    refine ⟨209830990044191793568836533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139887326696127862379224355 209830990044191793568836533)
    ·
      refine ⟨19671655316642980647078425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209830990044191793568836533 19671655316642980647078425)
      ·
        refine ⟨14753741487482235485308819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19671655316642980647078425 14753741487482235485308819)
        ·
          refine ⟨22130612231223353227963229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14753741487482235485308819 22130612231223353227963229)
          ·
            refine ⟨8298979586708757460486211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22130612231223353227963229 8298979586708757460486211)
            ·
              refine ⟨12448469380063136190729317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298979586708757460486211 12448469380063136190729317)
              ·
                refine ⟨2334088008761838035761747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12448469380063136190729317 2334088008761838035761747)
                ·
                  refine ⟨3501132013142757053642621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334088008761838035761747 3501132013142757053642621)
                  ·
                    refine ⟨1312924504928533895115983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3501132013142757053642621 1312924504928533895115983)
                    ·
                      rfl

theorem cell22_3835367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_3835367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835367 prefixEnd_3835367 := by exact prefixLift 3835367
  have htrace : WordTrace (prefixWord ++ tailWord_3835367) baseStart_3835367 baseEnd_3835367 := by
    simpa [prefixWord, tailWord_3835367, baseEnd_3835367] using wordTrace_append hprefix tailTrace_3835367
  have hstable : (prefixWord ++ tailWord_3835367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835367).length < 2 ^ (prefixWord ++ tailWord_3835367).sum := by decide
  have hdescent : baseEnd_3835367 < baseStart_3835367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835378 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_3835378 : Nat := 118140960795 + 3835378 * 2 ^ 59
def prefixEnd_3835378 : Nat := 4983230072969 + 3 ^ 40 * 3835378 * 2
def baseEnd_3835378 : Nat := 1312928270453333533090949

theorem tailTrace_3835378 : CollatzResearch.WordTrace tailWord_3835378 prefixEnd_3835378 1312928270453333533090949 := by
  unfold tailWord_3835378
  simp only [CollatzResearch.WordTrace]
  refine ⟨34971931974772002814468697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93258485266058674171916525 34971931974772002814468697)
  ·
    refine ⟨26228948981079002110851523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34971931974772002814468697 26228948981079002110851523)
    ·
      refine ⟨39343423471618503166277285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26228948981079002110851523 39343423471618503166277285)
      ·
        refine ⟨7376891900928469343676991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39343423471618503166277285 7376891900928469343676991)
        ·
          refine ⟨11065337851392704015515487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376891900928469343676991 11065337851392704015515487)
          ·
            refine ⟨16598006777089056023273231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11065337851392704015515487 16598006777089056023273231)
            ·
              refine ⟨24897010165633584034909847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16598006777089056023273231 24897010165633584034909847)
              ·
                refine ⟨37345515248450376052364771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24897010165633584034909847 37345515248450376052364771)
                ·
                  refine ⟨56018272872675564078547157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37345515248450376052364771 56018272872675564078547157)
                  ·
                    refine ⟨1312928270453333533090949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56018272872675564078547157 1312928270453333533090949)
                    ·
                      rfl

theorem cell22_3835378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_3835378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835378 prefixEnd_3835378 := by exact prefixLift 3835378
  have htrace : WordTrace (prefixWord ++ tailWord_3835378) baseStart_3835378 baseEnd_3835378 := by
    simpa [prefixWord, tailWord_3835378, baseEnd_3835378] using wordTrace_append hprefix tailTrace_3835378
  have hstable : (prefixWord ++ tailWord_3835378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835378).length < 2 ^ (prefixWord ++ tailWord_3835378).sum := by decide
  have hdescent : baseEnd_3835378 < baseStart_3835378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835425 : List Nat := [1, 2, 3, 2, 2, 2, 2, 4, 4]
def baseStart_3835425 : Nat := 118140960795 + 3835425 * 2 ^ 59
def prefixEnd_3835425 : Nat := 4983230072969 + 3 ^ 40 * 3835425 * 2
def baseEnd_3835425 : Nat := 437648119837947025721935

theorem tailTrace_3835425 : CollatzResearch.WordTrace tailWord_3835425 prefixEnd_3835425 437648119837947025721935 := by
  unfold tailWord_3835425
  simp only [CollatzResearch.WordTrace]
  refine ⟨139889442129917738284835729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93259628086611825523223819 139889442129917738284835729)
  ·
    refine ⟨104917081597438303713626797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139889442129917738284835729 104917081597438303713626797)
    ·
      refine ⟨39343905599039363892610049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104917081597438303713626797 39343905599039363892610049)
      ·
        refine ⟨29507929199279522919457537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39343905599039363892610049 29507929199279522919457537)
        ·
          refine ⟨22130946899459642189593153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29507929199279522919457537 22130946899459642189593153)
          ·
            refine ⟨16598210174594731642194865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22130946899459642189593153 16598210174594731642194865)
            ·
              refine ⟨12448657630946048731646149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16598210174594731642194865 12448657630946048731646149)
              ·
                refine ⟨2334123305802384137183653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12448657630946048731646149 2334123305802384137183653)
                ·
                  refine ⟨437648119837947025721935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334123305802384137183653 437648119837947025721935)
                  ·
                    rfl

theorem cell22_3835425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 4].length) (baseStart_3835425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835425 prefixEnd_3835425 := by exact prefixLift 3835425
  have htrace : WordTrace (prefixWord ++ tailWord_3835425) baseStart_3835425 baseEnd_3835425 := by
    simpa [prefixWord, tailWord_3835425, baseEnd_3835425] using wordTrace_append hprefix tailTrace_3835425
  have hstable : (prefixWord ++ tailWord_3835425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835425).length < 2 ^ (prefixWord ++ tailWord_3835425).sum := by decide
  have hdescent : baseEnd_3835425 < baseStart_3835425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835575 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 1, 5]
def baseStart_3835575 : Nat := 118140960795 + 3835575 * 2 ^ 59
def prefixEnd_3835575 : Nat := 4983230072969 + 3 ^ 40 * 3835575 * 2
def baseEnd_3835575 : Nat := 1312995707579290685915345

theorem tailTrace_3835575 : CollatzResearch.WordTrace tailWord_3835575 prefixEnd_3835575 1312995707579290685915345 := by
  unfold tailWord_3835575
  simp only [CollatzResearch.WordTrace]
  refine ⟨139894913079374313902796179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93263275386249542601864119 139894913079374313902796179)
  ·
    refine ⟨209842369619061470854194269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139894913079374313902796179 209842369619061470854194269)
    ·
      refine ⟨78690888607148051570322851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209842369619061470854194269 78690888607148051570322851)
      ·
        refine ⟨118036332910722077355484277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78690888607148051570322851 118036332910722077355484277)
        ·
          refine ⟨11065906210380194752076651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118036332910722077355484277 11065906210380194752076651)
          ·
            refine ⟨16598859315570292128114977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11065906210380194752076651 16598859315570292128114977)
            ·
              refine ⟨12449144486677719096086233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16598859315570292128114977 12449144486677719096086233)
              ·
                refine ⟨9336858365008289322064675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12449144486677719096086233 9336858365008289322064675)
                ·
                  refine ⟨14005287547512433983097013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9336858365008289322064675 14005287547512433983097013)
                  ·
                    refine ⟨1312995707579290685915345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14005287547512433983097013 1312995707579290685915345)
                    ·
                      rfl

theorem cell22_3835575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_3835575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835575 prefixEnd_3835575 := by exact prefixLift 3835575
  have htrace : WordTrace (prefixWord ++ tailWord_3835575) baseStart_3835575 baseEnd_3835575 := by
    simpa [prefixWord, tailWord_3835575, baseEnd_3835575] using wordTrace_append hprefix tailTrace_3835575
  have hstable : (prefixWord ++ tailWord_3835575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835575).length < 2 ^ (prefixWord ++ tailWord_3835575).sum := by decide
  have hdescent : baseEnd_3835575 < baseStart_3835575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835609 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 2, 3]
def baseStart_3835609 : Nat := 118140960795 + 3835609 * 2 ^ 59
def prefixEnd_3835609 : Nat := 4983230072969 + 3 ^ 40 * 3835609 * 2
def baseEnd_3835609 : Nat := 1313007346474125930565241

theorem tailTrace_3835609 : CollatzResearch.WordTrace tailWord_3835609 prefixEnd_3835609 1313007346474125930565241 := by
  unfold tailWord_3835609
  simp only [CollatzResearch.WordTrace]
  refine ⟨139896153161251137709533881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93264102107500758473022587 139896153161251137709533881)
  ·
    refine ⟨104922114870938353282150411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139896153161251137709533881 104922114870938353282150411)
    ·
      refine ⟨157383172306407529923225617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104922114870938353282150411 157383172306407529923225617)
      ·
        refine ⟨118037379229805647442419213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157383172306407529923225617 118037379229805647442419213)
        ·
          refine ⟨44264017211177117790907205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118037379229805647442419213 44264017211177117790907205)
          ·
            refine ⟨8299503227095709585795101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44264017211177117790907205 8299503227095709585795101)
            ·
              refine ⟨3112313710160891094673163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8299503227095709585795101 3112313710160891094673163)
              ·
                refine ⟨4668470565241336642009745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112313710160891094673163 4668470565241336642009745)
                ·
                  refine ⟨3501352923931002481507309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4668470565241336642009745 3501352923931002481507309)
                  ·
                    refine ⟨1313007346474125930565241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3501352923931002481507309 1313007346474125930565241)
                    ·
                      rfl

theorem cell22_3835609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 2, 3].length) (baseStart_3835609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835609 prefixEnd_3835609 := by exact prefixLift 3835609
  have htrace : WordTrace (prefixWord ++ tailWord_3835609) baseStart_3835609 baseEnd_3835609 := by
    simpa [prefixWord, tailWord_3835609, baseEnd_3835609] using wordTrace_append hprefix tailTrace_3835609
  have hstable : (prefixWord ++ tailWord_3835609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835609).length < 2 ^ (prefixWord ++ tailWord_3835609).sum := by decide
  have hdescent : baseEnd_3835609 < baseStart_3835609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835705 : List Nat := [1, 2, 1, 7, 1, 2, 2, 2, 1, 3]
def baseStart_3835705 : Nat := 118140960795 + 3835705 * 2 ^ 59
def prefixEnd_3835705 : Nat := 4983230072969 + 3 ^ 40 * 3835705 * 2
def baseEnd_3835705 : Nat := 1313040209236013680164947

theorem tailTrace_3835705 : CollatzResearch.WordTrace tailWord_3835705 prefixEnd_3835705 1313040209236013680164947 := by
  unfold tailWord_3835705
  simp only [CollatzResearch.WordTrace]
  refine ⟨139899654568903346105028569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93266436379268897403352379 139899654568903346105028569)
  ·
    refine ⟨104924740926677509578771427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139899654568903346105028569 104924740926677509578771427)
    ·
      refine ⟨157387111390016264368157141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104924740926677509578771427 157387111390016264368157141)
      ·
        refine ⟨3688760423203506196128683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 157387111390016264368157141 3688760423203506196128683)
        ·
          refine ⟨5533140634805259294193025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688760423203506196128683 5533140634805259294193025)
          ·
            refine ⟨4149855476103944470644769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5533140634805259294193025 4149855476103944470644769)
            ·
              refine ⟨3112391607077958352983577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149855476103944470644769 3112391607077958352983577)
              ·
                refine ⟨2334293705308468764737683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112391607077958352983577 2334293705308468764737683)
                ·
                  refine ⟨3501440557962703147106525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334293705308468764737683 3501440557962703147106525)
                  ·
                    refine ⟨1313040209236013680164947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3501440557962703147106525 1313040209236013680164947)
                    ·
                      rfl

theorem cell22_3835705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 1, 3].length) (baseStart_3835705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835705 prefixEnd_3835705 := by exact prefixLift 3835705
  have htrace : WordTrace (prefixWord ++ tailWord_3835705) baseStart_3835705 baseEnd_3835705 := by
    simpa [prefixWord, tailWord_3835705, baseEnd_3835705] using wordTrace_append hprefix tailTrace_3835705
  have hstable : (prefixWord ++ tailWord_3835705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835705).length < 2 ^ (prefixWord ++ tailWord_3835705).sum := by decide
  have hdescent : baseEnd_3835705 < baseStart_3835705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835746 : List Nat := [3, 3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_3835746 : Nat := 118140960795 + 3835746 * 2 ^ 59
def prefixEnd_3835746 : Nat := 4983230072969 + 3 ^ 40 * 3835746 * 2
def baseEnd_3835746 : Nat := 437684748124634413296607

theorem tailTrace_3835746 : CollatzResearch.WordTrace tailWord_3835746 prefixEnd_3835746 437684748124634413296607 := by
  unfold tailWord_3835746
  simp only [CollatzResearch.WordTrace]
  refine ⟨34975287490438702526817773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93267433307836540071514061 34975287490438702526817773)
  ·
    refine ⟨13115732808914513447556665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34975287490438702526817773 13115732808914513447556665)
    ·
      refine ⟨9836799606685885085667499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13115732808914513447556665 9836799606685885085667499)
      ·
        refine ⟨14755199410028827628501249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9836799606685885085667499 14755199410028827628501249)
        ·
          refine ⟨11066399557521620721375937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14755199410028827628501249 11066399557521620721375937)
          ·
            refine ⟨8299799668141215541031953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11066399557521620721375937 8299799668141215541031953)
            ·
              refine ⟨6224849751105911655773965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8299799668141215541031953 6224849751105911655773965)
              ·
                refine ⟨2334318656664716870915237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6224849751105911655773965 2334318656664716870915237)
                ·
                  refine ⟨437684748124634413296607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334318656664716870915237 437684748124634413296607)
                  ·
                    rfl

theorem cell22_3835746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_3835746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835746 prefixEnd_3835746 := by exact prefixLift 3835746
  have htrace : WordTrace (prefixWord ++ tailWord_3835746) baseStart_3835746 baseEnd_3835746 := by
    simpa [prefixWord, tailWord_3835746, baseEnd_3835746] using wordTrace_append hprefix tailTrace_3835746
  have hstable : (prefixWord ++ tailWord_3835746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835746).length < 2 ^ (prefixWord ++ tailWord_3835746).sum := by decide
  have hdescent : baseEnd_3835746 < baseStart_3835746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835748 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_3835748 : Nat := 118140960795 + 3835748 * 2 ^ 59
def prefixEnd_3835748 : Nat := 4983230072969 + 3 ^ 40 * 3835748 * 2
def baseEnd_3835748 : Nat := 1313054929014775901339815

theorem tailTrace_3835748 : CollatzResearch.WordTrace tailWord_3835748 prefixEnd_3835748 1313054929014775901339815 := by
  unfold tailWord_3835748
  simp only [CollatzResearch.WordTrace]
  refine ⟨69950611453873782224421949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93267481938498376299229265 69950611453873782224421949)
  ·
    refine ⟨26231479295202668334158231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69950611453873782224421949 26231479295202668334158231)
    ·
      refine ⟨39347218942804002501237347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26231479295202668334158231 39347218942804002501237347)
      ·
        refine ⟨59020828414206003751856021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39347218942804002501237347 59020828414206003751856021)
        ·
          refine ⟨2766601331915906425868251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59020828414206003751856021 2766601331915906425868251)
          ·
            refine ⟨4149901997873859638802377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766601331915906425868251 4149901997873859638802377)
            ·
              refine ⟨3112426498405394729101783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149901997873859638802377 3112426498405394729101783)
              ·
                refine ⟨4668639747608092093652675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112426498405394729101783 4668639747608092093652675)
                ·
                  refine ⟨7002959621412138140479013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668639747608092093652675 7002959621412138140479013)
                  ·
                    refine ⟨1313054929014775901339815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7002959621412138140479013 1313054929014775901339815)
                    ·
                      rfl

theorem cell22_3835748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_3835748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835748 prefixEnd_3835748 := by exact prefixLift 3835748
  have htrace : WordTrace (prefixWord ++ tailWord_3835748) baseStart_3835748 baseEnd_3835748 := by
    simpa [prefixWord, tailWord_3835748, baseEnd_3835748] using wordTrace_append hprefix tailTrace_3835748
  have hstable : (prefixWord ++ tailWord_3835748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835748).length < 2 ^ (prefixWord ++ tailWord_3835748).sum := by decide
  have hdescent : baseEnd_3835748 < baseStart_3835748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835770 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_3835770 : Nat := 118140960795 + 3835770 * 2 ^ 59
def prefixEnd_3835770 : Nat := 4983230072969 + 3 ^ 40 * 3835770 * 2
def baseEnd_3835770 : Nat := 1313062460064375177289747

theorem tailTrace_3835770 : CollatzResearch.WordTrace tailWord_3835770 prefixEnd_3835770 1313062460064375177289747 := by
  unfold tailWord_3835770
  simp only [CollatzResearch.WordTrace]
  refine ⟨34975506328416965551536191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93268016875778574804096509 34975506328416965551536191)
  ·
    refine ⟨52463259492625448327304287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34975506328416965551536191 52463259492625448327304287)
    ·
      refine ⟨78694889238938172490956431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52463259492625448327304287 78694889238938172490956431)
      ·
        refine ⟨118042333858407258736434647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78694889238938172490956431 118042333858407258736434647)
        ·
          refine ⟨177063500787610888104651971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118042333858407258736434647 177063500787610888104651971)
          ·
            refine ⟨265595251181416332156977957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177063500787610888104651971 265595251181416332156977957)
            ·
              refine ⟨49799109596515562279433367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265595251181416332156977957 49799109596515562279433367)
              ·
                refine ⟨74698664394773343419150051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49799109596515562279433367 74698664394773343419150051)
                ·
                  refine ⟨112047996592160015128725077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74698664394773343419150051 112047996592160015128725077)
                  ·
                    refine ⟨1313062460064375177289747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112047996592160015128725077 1313062460064375177289747)
                    ·
                      rfl

theorem cell22_3835770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_3835770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835770 prefixEnd_3835770 := by exact prefixLift 3835770
  have htrace : WordTrace (prefixWord ++ tailWord_3835770) baseStart_3835770 baseEnd_3835770 := by
    simpa [prefixWord, tailWord_3835770, baseEnd_3835770] using wordTrace_append hprefix tailTrace_3835770
  have hstable : (prefixWord ++ tailWord_3835770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835770).length < 2 ^ (prefixWord ++ tailWord_3835770).sum := by decide
  have hdescent : baseEnd_3835770 < baseStart_3835770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835802 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_3835802 : Nat := 118140960795 + 3835802 * 2 ^ 59
def prefixEnd_3835802 : Nat := 4983230072969 + 3 ^ 40 * 3835802 * 2
def baseEnd_3835802 : Nat := 437691138106112586829883

theorem tailTrace_3835802 : CollatzResearch.WordTrace tailWord_3835802 prefixEnd_3835802 437691138106112586829883 := by
  unfold tailWord_3835802
  simp only [CollatzResearch.WordTrace]
  refine ⟨34975798112387982917827415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93268794966367954447539773 34975798112387982917827415)
  ·
    refine ⟨52463697168581974376741123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34975798112387982917827415 52463697168581974376741123)
    ·
      refine ⟨78695545752872961565111685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52463697168581974376741123 78695545752872961565111685)
      ·
        refine ⟨14755414828663680293458441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78695545752872961565111685 14755414828663680293458441)
        ·
          refine ⟨11066561121497760220093831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14755414828663680293458441 11066561121497760220093831)
          ·
            refine ⟨16599841682246640330140747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11066561121497760220093831 16599841682246640330140747)
            ·
              refine ⟨24899762523369960495211121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16599841682246640330140747 24899762523369960495211121)
              ·
                refine ⟨18674821892527470371408341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24899762523369960495211121 18674821892527470371408341)
                ·
                  refine ⟨437691138106112586829883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18674821892527470371408341 437691138106112586829883)
                  ·
                    rfl

theorem cell22_3835802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_3835802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835802 prefixEnd_3835802 := by exact prefixLift 3835802
  have htrace : WordTrace (prefixWord ++ tailWord_3835802) baseStart_3835802 baseEnd_3835802 := by
    simpa [prefixWord, tailWord_3835802, baseEnd_3835802] using wordTrace_append hprefix tailTrace_3835802
  have hstable : (prefixWord ++ tailWord_3835802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835802).length < 2 ^ (prefixWord ++ tailWord_3835802).sum := by decide
  have hdescent : baseEnd_3835802 < baseStart_3835802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835832 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_3835832 : Nat := 118140960795 + 3835832 * 2 ^ 59
def prefixEnd_3835832 : Nat := 4983230072969 + 3 ^ 40 * 3835832 * 2
def baseEnd_3835832 : Nat := 1313083683931427682239557

theorem tailTrace_3835832 : CollatzResearch.WordTrace tailWord_3835832 prefixEnd_3835832 1313083683931427682239557 := by
  unfold tailWord_3835832
  simp only [CollatzResearch.WordTrace]
  refine ⟨69952143319721623397450875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93269524426295497863267833 69952143319721623397450875)
  ·
    refine ⟨104928214979582435096176313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69952143319721623397450875 104928214979582435096176313)
    ·
      refine ⟨78696161234686826322132235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104928214979582435096176313 78696161234686826322132235)
      ·
        refine ⟨118044241852030239483198353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78696161234686826322132235 118044241852030239483198353)
        ·
          refine ⟨88533181389022679612398765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118044241852030239483198353 88533181389022679612398765)
          ·
            refine ⟨33199943020883504854649537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88533181389022679612398765 33199943020883504854649537)
            ·
              refine ⟨24899957265662628640987153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33199943020883504854649537 24899957265662628640987153)
              ·
                refine ⟨18674967949246971480740365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24899957265662628640987153 18674967949246971480740365)
                ·
                  refine ⟨7003112980967614305277637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18674967949246971480740365 7003112980967614305277637)
                  ·
                    refine ⟨1313083683931427682239557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7003112980967614305277637 1313083683931427682239557)
                    ·
                      rfl

theorem cell22_3835832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_3835832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835832 prefixEnd_3835832 := by exact prefixLift 3835832
  have htrace : WordTrace (prefixWord ++ tailWord_3835832) baseStart_3835832 baseEnd_3835832 := by
    simpa [prefixWord, tailWord_3835832, baseEnd_3835832] using wordTrace_append hprefix tailTrace_3835832
  have hstable : (prefixWord ++ tailWord_3835832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835832).length < 2 ^ (prefixWord ++ tailWord_3835832).sum := by decide
  have hdescent : baseEnd_3835832 < baseStart_3835832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835836 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 5]
def baseStart_3835836 : Nat := 118140960795 + 3835836 * 2 ^ 59
def prefixEnd_3835836 : Nat := 4983230072969 + 3 ^ 40 * 3835836 * 2
def baseEnd_3835836 : Nat := 437695017737724335046515

theorem tailTrace_3835836 : CollatzResearch.WordTrace tailWord_3835836 prefixEnd_3835836 437695017737724335046515 := by
  unfold tailWord_3835836
  simp only [CollatzResearch.WordTrace]
  refine ⟨69952216265714377739023681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93269621687619170318698241 69952216265714377739023681)
  ·
    refine ⟨52464162199285783304267761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69952216265714377739023681 52464162199285783304267761)
    ·
      refine ⟨39348121649464337478200821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52464162199285783304267761 39348121649464337478200821)
      ·
        refine ⟨3688886404637281638581327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39348121649464337478200821 3688886404637281638581327)
        ·
          refine ⟨5533329606955922457871991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688886404637281638581327 5533329606955922457871991)
          ·
            refine ⟨8299994410433883686807987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533329606955922457871991 8299994410433883686807987)
            ·
              refine ⟨12449991615650825530211981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8299994410433883686807987 12449991615650825530211981)
              ·
                refine ⟨4668746855869059573829493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12449991615650825530211981 4668746855869059573829493)
                ·
                  refine ⟨437695017737724335046515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4668746855869059573829493 437695017737724335046515)
                  ·
                    rfl

theorem cell22_3835836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_3835836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835836 prefixEnd_3835836 := by exact prefixLift 3835836
  have htrace : WordTrace (prefixWord ++ tailWord_3835836) baseStart_3835836 baseEnd_3835836 := by
    simpa [prefixWord, tailWord_3835836, baseEnd_3835836] using wordTrace_append hprefix tailTrace_3835836
  have hstable : (prefixWord ++ tailWord_3835836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835836).length < 2 ^ (prefixWord ++ tailWord_3835836).sum := by decide
  have hdescent : baseEnd_3835836 < baseStart_3835836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835864 : List Nat := [2, 1, 2, 2, 2, 2, 2, 5, 4]
def baseStart_3835864 : Nat := 118140960795 + 3835864 * 2 ^ 59
def prefixEnd_3835864 : Nat := 4983230072969 + 3 ^ 40 * 3835864 * 2
def baseEnd_3835864 : Nat := 437698212728463421813153

theorem tailTrace_3835864 : CollatzResearch.WordTrace tailWord_3835864 prefixEnd_3835864 437698212728463421813153 := by
  unfold tailWord_3835864
  simp only [CollatzResearch.WordTrace]
  refine ⟨69952726887663658130033323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93270302516884877506711097 69952726887663658130033323)
  ·
    refine ⟨104929090331495487195049985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69952726887663658130033323 104929090331495487195049985)
    ·
      refine ⟨78696817748621615396287489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104929090331495487195049985 78696817748621615396287489)
      ·
        refine ⟨59022613311466211547215617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78696817748621615396287489 59022613311466211547215617)
        ·
          refine ⟨44266959983599658660411713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59022613311466211547215617 44266959983599658660411713)
          ·
            refine ⟨33200219987699743995308785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44266959983599658660411713 33200219987699743995308785)
            ·
              refine ⟨24900164990774807996481589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33200219987699743995308785 24900164990774807996481589)
              ·
                refine ⟨2334390467885138249670149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24900164990774807996481589 2334390467885138249670149)
                ·
                  refine ⟨437698212728463421813153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334390467885138249670149 437698212728463421813153)
                  ·
                    rfl

theorem cell22_3835864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 4].length) (baseStart_3835864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835864 prefixEnd_3835864 := by exact prefixLift 3835864
  have htrace : WordTrace (prefixWord ++ tailWord_3835864) baseStart_3835864 baseEnd_3835864 := by
    simpa [prefixWord, tailWord_3835864, baseEnd_3835864] using wordTrace_append hprefix tailTrace_3835864
  have hstable : (prefixWord ++ tailWord_3835864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835864).length < 2 ^ (prefixWord ++ tailWord_3835864).sum := by decide
  have hdescent : baseEnd_3835864 < baseStart_3835864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835874 : List Nat := [3, 3, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3835874 : Nat := 118140960795 + 3835874 * 2 ^ 59
def prefixEnd_3835874 : Nat := 4983230072969 + 3 ^ 40 * 3835874 * 2
def baseEnd_3835874 : Nat := 1313098061389753572689429

theorem tailTrace_3835874 : CollatzResearch.WordTrace tailWord_3835874 prefixEnd_3835874 1313098061389753572689429 := by
  unfold tailWord_3835874
  simp only [CollatzResearch.WordTrace]
  refine ⟨34976454626322771991982669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93270545670194058645287117 34976454626322771991982669)
  ·
    refine ⟨13116170484871039496993501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34976454626322771991982669 13116170484871039496993501)
    ·
      refine ⟨4918563931826639811372563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13116170484871039496993501 4918563931826639811372563)
      ·
        refine ⟨7377845897739959717058845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918563931826639811372563 7377845897739959717058845)
        ·
          refine ⟨2766692211652484893897067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7377845897739959717058845 2766692211652484893897067)
          ·
            refine ⟨4150038317478727340845601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766692211652484893897067 4150038317478727340845601)
            ·
              refine ⟨3112528738109045505634201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150038317478727340845601 3112528738109045505634201)
              ·
                refine ⟨2334396553581784129225651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112528738109045505634201 2334396553581784129225651)
                ·
                  refine ⟨3501594830372676193838477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334396553581784129225651 3501594830372676193838477)
                  ·
                    refine ⟨1313098061389753572689429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3501594830372676193838477 1313098061389753572689429)
                    ·
                      rfl

theorem cell22_3835874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3835874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835874 prefixEnd_3835874 := by exact prefixLift 3835874
  have htrace : WordTrace (prefixWord ++ tailWord_3835874) baseStart_3835874 baseEnd_3835874 := by
    simpa [prefixWord, tailWord_3835874, baseEnd_3835874] using wordTrace_append hprefix tailTrace_3835874
  have hstable : (prefixWord ++ tailWord_3835874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835874).length < 2 ^ (prefixWord ++ tailWord_3835874).sum := by decide
  have hdescent : baseEnd_3835874 < baseStart_3835874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835909 : List Nat := [1, 3, 1, 1, 2, 5, 3, 6]
def baseStart_3835909 : Nat := 118140960795 + 3835909 * 2 ^ 59
def prefixEnd_3835909 : Nat := 4983230072969 + 3 ^ 40 * 3835909 * 2
def baseEnd_3835909 : Nat := 145901115845002794229369

theorem tailTrace_3835909 : CollatzResearch.WordTrace tailWord_3835909 prefixEnd_3835909 145901115845002794229369 := by
  unfold tailWord_3835909
  simp only [CollatzResearch.WordTrace]
  refine ⟨139907095060164288945454781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93271396706776192630303187 139907095060164288945454781)
  ·
    refine ⟨52465160647561608354545543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139907095060164288945454781 52465160647561608354545543)
    ·
      refine ⟨78697740971342412531818315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52465160647561608354545543 78697740971342412531818315)
      ·
        refine ⟨118046611457013618797727473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78697740971342412531818315 118046611457013618797727473)
        ·
          refine ⟨88534958592760214098295605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118046611457013618797727473 88534958592760214098295605)
          ·
            refine ⟨8300152368071270071715213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88534958592760214098295605 8300152368071270071715213)
            ·
              refine ⟨3112557138026726276893205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8300152368071270071715213 3112557138026726276893205)
              ·
                refine ⟨145901115845002794229369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3112557138026726276893205 145901115845002794229369)
                ·
                  rfl

theorem cell22_3835909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 6].length) (baseStart_3835909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835909 prefixEnd_3835909 := by exact prefixLift 3835909
  have htrace : WordTrace (prefixWord ++ tailWord_3835909) baseStart_3835909 baseEnd_3835909 := by
    simpa [prefixWord, tailWord_3835909, baseEnd_3835909] using wordTrace_append hprefix tailTrace_3835909
  have hstable : (prefixWord ++ tailWord_3835909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835909).length < 2 ^ (prefixWord ++ tailWord_3835909).sum := by decide
  have hdescent : baseEnd_3835909 < baseStart_3835909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835911 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 2, 4]
def baseStart_3835911 : Nat := 118140960795 + 3835911 * 2 ^ 59
def prefixEnd_3835911 : Nat := 4983230072969 + 3 ^ 40 * 3835911 * 2
def baseEnd_3835911 : Nat := 1313110727245897809514315

theorem tailTrace_3835911 : CollatzResearch.WordTrace tailWord_3835911 prefixEnd_3835911 1313110727245897809514315 := by
  unfold tailWord_3835911
  simp only [CollatzResearch.WordTrace]
  refine ⟨139907168006157043287027587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93271445337438028858018391 139907168006157043287027587)
  ·
    refine ⟨209860752009235564930541381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139907168006157043287027587 209860752009235564930541381)
    ·
      refine ⟨39348891001731668424476509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209860752009235564930541381 39348891001731668424476509)
      ·
        refine ⟨14755834125649375659178691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39348891001731668424476509 14755834125649375659178691)
        ·
          refine ⟨22133751188474063488768037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14755834125649375659178691 22133751188474063488768037)
          ·
            refine ⟨4150078347838886904144007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22133751188474063488768037 4150078347838886904144007)
            ·
              refine ⟨6225117521758330356216011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150078347838886904144007 6225117521758330356216011)
              ·
                refine ⟨9337676282637495534324017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6225117521758330356216011 9337676282637495534324017)
                ·
                  refine ⟨7003257211978121650743013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9337676282637495534324017 7003257211978121650743013)
                  ·
                    refine ⟨1313110727245897809514315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7003257211978121650743013 1313110727245897809514315)
                    ·
                      rfl

theorem cell22_3835911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_3835911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835911 prefixEnd_3835911 := by exact prefixLift 3835911
  have htrace : WordTrace (prefixWord ++ tailWord_3835911) baseStart_3835911 baseEnd_3835911 := by
    simpa [prefixWord, tailWord_3835911, baseEnd_3835911] using wordTrace_append hprefix tailTrace_3835911
  have hstable : (prefixWord ++ tailWord_3835911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835911).length < 2 ^ (prefixWord ++ tailWord_3835911).sum := by decide
  have hdescent : baseEnd_3835911 < baseStart_3835911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835941 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 3, 3]
def baseStart_3835941 : Nat := 118140960795 + 3835941 * 2 ^ 59
def prefixEnd_3835941 : Nat := 4983230072969 + 3 ^ 40 * 3835941 * 2
def baseEnd_3835941 : Nat := 1313120996858987731264223

theorem tailTrace_3835941 : CollatzResearch.WordTrace tailWord_3835941 prefixEnd_3835941 1313120996858987731264223 := by
  unfold tailWord_3835941
  simp only [CollatzResearch.WordTrace]
  refine ⟨139908262196048358410619677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93272174797365572273746451 139908262196048358410619677)
  ·
    refine ⟨52465598323518134403982379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139908262196048358410619677 52465598323518134403982379)
    ·
      refine ⟨78698397485277201605973569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52465598323518134403982379 78698397485277201605973569)
      ·
        refine ⟨59023798113957901204480177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78698397485277201605973569 59023798113957901204480177)
        ·
          refine ⟨44267848585468425903360133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59023798113957901204480177 44267848585468425903360133)
          ·
            refine ⟨8300221609775329856880025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44267848585468425903360133 8300221609775329856880025)
            ·
              refine ⟨6225166207331497392660019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8300221609775329856880025 6225166207331497392660019)
              ·
                refine ⟨9337749310997246088990029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6225166207331497392660019 9337749310997246088990029)
                ·
                  refine ⟨3501655991623967283371261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9337749310997246088990029 3501655991623967283371261)
                  ·
                    refine ⟨1313120996858987731264223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3501655991623967283371261 1313120996858987731264223)
                    ·
                      rfl

theorem cell22_3835941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_3835941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3835941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3835941 prefixEnd_3835941 := by exact prefixLift 3835941
  have htrace : WordTrace (prefixWord ++ tailWord_3835941) baseStart_3835941 baseEnd_3835941 := by
    simpa [prefixWord, tailWord_3835941, baseEnd_3835941] using wordTrace_append hprefix tailTrace_3835941
  have hstable : (prefixWord ++ tailWord_3835941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835941).length < 2 ^ (prefixWord ++ tailWord_3835941).sum := by decide
  have hdescent : baseEnd_3835941 < baseStart_3835941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836018 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_3836018 : Nat := 118140960795 + 3836018 * 2 ^ 59
def prefixEnd_3836018 : Nat := 4983230072969 + 3 ^ 40 * 3836018 * 2
def baseEnd_3836018 : Nat := 1313147355532585197088987

theorem tailTrace_3836018 : CollatzResearch.WordTrace tailWord_3836018 prefixEnd_3836018 1313147355532585197088987 := by
  unfold tailWord_3836018
  simp only [CollatzResearch.WordTrace]
  refine ⟨34977767654192350140293177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93274047077846267040781805 34977767654192350140293177)
  ·
    refine ⟨26233325740644262605219883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34977767654192350140293177 26233325740644262605219883)
    ·
      refine ⟨39349988610966393907829825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26233325740644262605219883 39349988610966393907829825)
      ·
        refine ⟨29512491458224795430872369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39349988610966393907829825 29512491458224795430872369)
        ·
          refine ⟨22134368593668596573154277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29512491458224795430872369 22134368593668596573154277)
          ·
            refine ⟨4150194111312861857466427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22134368593668596573154277 4150194111312861857466427)
            ·
              refine ⟨6225291166969292786199641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150194111312861857466427 6225291166969292786199641)
              ·
                refine ⟨4668968375226969589649731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6225291166969292786199641 4668968375226969589649731)
                ·
                  refine ⟨7003452562840454384474597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668968375226969589649731 7003452562840454384474597)
                  ·
                    refine ⟨1313147355532585197088987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7003452562840454384474597 1313147355532585197088987)
                    ·
                      rfl

theorem cell22_3836018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_3836018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836018 prefixEnd_3836018 := by exact prefixLift 3836018
  have htrace : WordTrace (prefixWord ++ tailWord_3836018) baseStart_3836018 baseEnd_3836018 := by
    simpa [prefixWord, tailWord_3836018, baseEnd_3836018] using wordTrace_append hprefix tailTrace_3836018
  have hstable : (prefixWord ++ tailWord_3836018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836018).length < 2 ^ (prefixWord ++ tailWord_3836018).sum := by decide
  have hdescent : baseEnd_3836018 < baseStart_3836018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836061 : List Nat := [1, 4, 2, 1, 1, 5, 1, 7]
def baseStart_3836061 : Nat := 118140960795 + 3836061 * 2 ^ 59
def prefixEnd_3836061 : Nat := 4983230072969 + 3 ^ 40 * 3836061 * 2
def baseEnd_3836061 : Nat := 145906897256816379807095

theorem tailTrace_3836061 : CollatzResearch.WordTrace tailWord_3836061 prefixEnd_3836061 145906897256816379807095 := by
  unfold tailWord_3836061
  simp only [CollatzResearch.WordTrace]
  refine ⟨139912638955613618904988037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93275092637075745936658691 139912638955613618904988037)
  ·
    refine ⟨26233619804177553544685257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139912638955613618904988037 26233619804177553544685257)
    ·
      refine ⟨19675214853133165158513943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26233619804177553544685257 19675214853133165158513943)
      ·
        refine ⟨29512822279699747737770915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19675214853133165158513943 29512822279699747737770915)
        ·
          refine ⟨44269233419549621606656373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29512822279699747737770915 44269233419549621606656373)
          ·
            refine ⟨4150240633082777025624035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44269233419549621606656373 4150240633082777025624035)
            ·
              refine ⟨6225360949624165538436053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150240633082777025624035 6225360949624165538436053)
              ·
                refine ⟨145906897256816379807095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6225360949624165538436053 145906897256816379807095)
                ·
                  rfl

theorem cell22_3836061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 7].length) (baseStart_3836061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836061 prefixEnd_3836061 := by exact prefixLift 3836061
  have htrace : WordTrace (prefixWord ++ tailWord_3836061) baseStart_3836061 baseEnd_3836061 := by
    simpa [prefixWord, tailWord_3836061, baseEnd_3836061] using wordTrace_append hprefix tailTrace_3836061
  have hstable : (prefixWord ++ tailWord_3836061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836061).length < 2 ^ (prefixWord ++ tailWord_3836061).sum := by decide
  have hdescent : baseEnd_3836061 < baseStart_3836061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836084 : List Nat := [2, 5, 3, 1, 1, 1, 2, 3, 4]
def baseStart_3836084 : Nat := 118140960795 + 3836084 * 2 ^ 59
def prefixEnd_3836084 : Nat := 4983230072969 + 3 ^ 40 * 3836084 * 2
def baseEnd_3836084 : Nat := 437723316227127674979595

theorem tailTrace_3836084 : CollatzResearch.WordTrace tailWord_3836084 prefixEnd_3836084 437723316227127674979595 := by
  unfold tailWord_3836084
  simp only [CollatzResearch.WordTrace]
  refine ⟨69956738917265146916537653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93275651889686862555383537 69956738917265146916537653)
  ·
    refine ⟨6558444273493607523425405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69956738917265146916537653 6558444273493607523425405)
    ·
      refine ⟨2459416602560102821284527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6558444273493607523425405 2459416602560102821284527)
      ·
        refine ⟨3689124903840154231926791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459416602560102821284527 3689124903840154231926791)
        ·
          refine ⟨5533687355760231347890187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689124903840154231926791 5533687355760231347890187)
          ·
            refine ⟨8300531033640347021835281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533687355760231347890187 8300531033640347021835281)
            ·
              refine ⟨6225398275230260266376461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8300531033640347021835281 6225398275230260266376461)
              ·
                refine ⟨2334524353211347599891173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6225398275230260266376461 2334524353211347599891173)
                ·
                  refine ⟨437723316227127674979595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334524353211347599891173 437723316227127674979595)
                  ·
                    rfl

theorem cell22_3836084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_3836084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836084 prefixEnd_3836084 := by exact prefixLift 3836084
  have htrace : WordTrace (prefixWord ++ tailWord_3836084) baseStart_3836084 baseEnd_3836084 := by
    simpa [prefixWord, tailWord_3836084, baseEnd_3836084] using wordTrace_append hprefix tailTrace_3836084
  have hstable : (prefixWord ++ tailWord_3836084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836084).length < 2 ^ (prefixWord ++ tailWord_3836084).sum := by decide
  have hdescent : baseEnd_3836084 < baseStart_3836084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836089 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 7]
def baseStart_3836089 : Nat := 118140960795 + 3836089 * 2 ^ 59
def prefixEnd_3836089 : Nat := 4983230072969 + 3 ^ 40 * 3836089 * 2
def baseEnd_3836089 : Nat := 437723886761188226187923

theorem tailTrace_3836089 : CollatzResearch.WordTrace tailWord_3836089 prefixEnd_3836089 437723886761188226187923 := by
  unfold tailWord_3836089
  simp only [CollatzResearch.WordTrace]
  refine ⟨139913660199512179687007321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93275773466341453124671547 139913660199512179687007321)
  ·
    refine ⟨104935245149634134765255491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139913660199512179687007321 104935245149634134765255491)
    ·
      refine ⟨157402867724451202147883237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104935245149634134765255491 157402867724451202147883237)
      ·
        refine ⟨29513037698334600402728107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157402867724451202147883237 29513037698334600402728107)
        ·
          refine ⟨44269556547501900604092161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29513037698334600402728107 44269556547501900604092161)
          ·
            refine ⟨33202167410626425453069121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44269556547501900604092161 33202167410626425453069121)
            ·
              refine ⟨24901625557969819089801841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33202167410626425453069121 24901625557969819089801841)
              ·
                refine ⟨18676219168477364317351381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24901625557969819089801841 18676219168477364317351381)
                ·
                  refine ⟨437723886761188226187923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18676219168477364317351381 437723886761188226187923)
                  ·
                    rfl

theorem cell22_3836089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_3836089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836089 prefixEnd_3836089 := by exact prefixLift 3836089
  have htrace : WordTrace (prefixWord ++ tailWord_3836089) baseStart_3836089 baseEnd_3836089 := by
    simpa [prefixWord, tailWord_3836089, baseEnd_3836089] using wordTrace_append hprefix tailTrace_3836089
  have hstable : (prefixWord ++ tailWord_3836089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836089).length < 2 ^ (prefixWord ++ tailWord_3836089).sum := by decide
  have hdescent : baseEnd_3836089 < baseStart_3836089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836110 : List Nat := [4, 1, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_3836110 : Nat := 118140960795 + 3836110 * 2 ^ 59
def prefixEnd_3836110 : Nat := 4983230072969 + 3 ^ 40 * 3836110 * 2
def baseEnd_3836110 : Nat := 1313178849012727623788705

theorem tailTrace_3836110 : CollatzResearch.WordTrace tailWord_3836110 prefixEnd_3836110 1313178849012727623788705 := by
  unfold tailWord_3836110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489303266554512534190223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93276284088290733515681189 17489303266554512534190223)
  ·
    refine ⟨26233954899831768801285335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17489303266554512534190223 26233954899831768801285335)
    ·
      refine ⟨39350932349747653201928003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26233954899831768801285335 39350932349747653201928003)
      ·
        refine ⟨59026398524621479802892005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39350932349747653201928003 59026398524621479802892005)
        ·
          refine ⟨11067449723366527463042251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59026398524621479802892005 11067449723366527463042251)
          ·
            refine ⟨16601174585049791194563377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11067449723366527463042251 16601174585049791194563377)
            ·
              refine ⟨12450880938787343395922533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16601174585049791194563377 12450880938787343395922533)
              ·
                refine ⟨2334540176022626886735475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12450880938787343395922533 2334540176022626886735475)
                ·
                  refine ⟨3501810264033940330103213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334540176022626886735475 3501810264033940330103213)
                  ·
                    refine ⟨1313178849012727623788705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3501810264033940330103213 1313178849012727623788705)
                    ·
                      rfl

theorem cell22_3836110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_3836110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836110 prefixEnd_3836110 := by exact prefixLift 3836110
  have htrace : WordTrace (prefixWord ++ tailWord_3836110) baseStart_3836110 baseEnd_3836110 := by
    simpa [prefixWord, tailWord_3836110, baseEnd_3836110] using wordTrace_append hprefix tailTrace_3836110
  have hstable : (prefixWord ++ tailWord_3836110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836110).length < 2 ^ (prefixWord ++ tailWord_3836110).sum := by decide
  have hdescent : baseEnd_3836110 < baseStart_3836110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836168 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 6]
def baseStart_3836168 : Nat := 118140960795 + 3836168 * 2 ^ 59
def prefixEnd_3836168 : Nat := 4983230072969 + 3 ^ 40 * 3836168 * 2
def baseEnd_3836168 : Nat := 437732901199344935279509

theorem tailTrace_3836168 : CollatzResearch.WordTrace tailWord_3836168 prefixEnd_3836168 437732901199344935279509 := by
  unfold tailWord_3836168
  simp only [CollatzResearch.WordTrace]
  refine ⟨69958270783112988089566579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93277694377483984119422105 69958270783112988089566579)
  ·
    refine ⟨104937406174669482134349869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69958270783112988089566579 104937406174669482134349869)
    ·
      refine ⟨39351527315501055800381201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104937406174669482134349869 39351527315501055800381201)
      ·
        refine ⟨29513645486625791850285901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39351527315501055800381201 29513645486625791850285901)
        ·
          refine ⟨11067617057484671943857213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29513645486625791850285901 11067617057484671943857213)
          ·
            refine ⟨4150356396556751978946455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11067617057484671943857213 4150356396556751978946455)
            ·
              refine ⟨6225534594835127968419683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150356396556751978946455 6225534594835127968419683)
              ·
                refine ⟨9338301892252691952629525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6225534594835127968419683 9338301892252691952629525)
                ·
                  refine ⟨437732901199344935279509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9338301892252691952629525 437732901199344935279509)
                  ·
                    rfl

theorem cell22_3836168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 6].length) (baseStart_3836168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836168 prefixEnd_3836168 := by exact prefixLift 3836168
  have htrace : WordTrace (prefixWord ++ tailWord_3836168) baseStart_3836168 baseEnd_3836168 := by
    simpa [prefixWord, tailWord_3836168, baseEnd_3836168] using wordTrace_append hprefix tailTrace_3836168
  have hstable : (prefixWord ++ tailWord_3836168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836168).length < 2 ^ (prefixWord ++ tailWord_3836168).sum := by decide
  have hdescent : baseEnd_3836168 < baseStart_3836168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836196 : List Nat := [2, 3, 1, 3, 1, 2, 2, 8]
def baseStart_3836196 : Nat := 118140960795 + 3836196 * 2 ^ 59
def prefixEnd_3836196 : Nat := 4983230072969 + 3 ^ 40 * 3836196 * 2
def baseEnd_3836196 : Nat := 145912032063361340682049

theorem tailTrace_3836196 : CollatzResearch.WordTrace tailWord_3836196 prefixEnd_3836196 145912032063361340682049 := by
  unfold tailWord_3836196
  simp only [CollatzResearch.WordTrace]
  refine ⟨69958781405062268480576221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93278375206749691307434961 69958781405062268480576221)
  ·
    refine ⟨26234543026898350680216083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69958781405062268480576221 26234543026898350680216083)
    ·
      refine ⟨39351814540347526020324125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26234543026898350680216083 39351814540347526020324125)
      ·
        refine ⟨14756930452630322257621547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39351814540347526020324125 14756930452630322257621547)
        ·
          refine ⟨22135395678945483386432321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14756930452630322257621547 22135395678945483386432321)
          ·
            refine ⟨16601546759209112539824241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22135395678945483386432321 16601546759209112539824241)
            ·
              refine ⟨12451160069406834404868181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16601546759209112539824241 12451160069406834404868181)
              ·
                refine ⟨145912032063361340682049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12451160069406834404868181 145912032063361340682049)
                ·
                  rfl

theorem cell22_3836196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 8].length) (baseStart_3836196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836196 prefixEnd_3836196 := by exact prefixLift 3836196
  have htrace : WordTrace (prefixWord ++ tailWord_3836196) baseStart_3836196 baseEnd_3836196 := by
    simpa [prefixWord, tailWord_3836196, baseEnd_3836196] using wordTrace_append hprefix tailTrace_3836196
  have hstable : (prefixWord ++ tailWord_3836196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836196).length < 2 ^ (prefixWord ++ tailWord_3836196).sum := by decide
  have hdescent : baseEnd_3836196 < baseStart_3836196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836245 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 3, 3]
def baseStart_3836245 : Nat := 118140960795 + 3836245 * 2 ^ 59
def prefixEnd_3836245 : Nat := 4983230072969 + 3 ^ 40 * 3836245 * 2
def baseEnd_3836245 : Nat := 1313225062271632271663291

theorem tailTrace_3836245 : CollatzResearch.WordTrace tailWord_3836245 prefixEnd_3836245 1313225062271632271663291 := by
  unfold tailWord_3836245
  simp only [CollatzResearch.WordTrace]
  refine ⟨139919349986947018329686189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93279566657964678886457459 139919349986947018329686189)
  ·
    refine ⟨52469756245105131873632321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139919349986947018329686189 52469756245105131873632321)
    ·
      refine ⟨39352317183828848905224241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52469756245105131873632321 39352317183828848905224241)
      ·
        refine ⟨29514237887871636678918181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39352317183828848905224241 29514237887871636678918181)
        ·
          refine ⟨5533919603975931877297159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29514237887871636678918181 5533919603975931877297159)
          ·
            refine ⟨8300879405963897815945739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533919603975931877297159 8300879405963897815945739)
            ·
              refine ⟨12451319108945846723918609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8300879405963897815945739 12451319108945846723918609)
              ·
                refine ⟨9338489331709385042938957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12451319108945846723918609 9338489331709385042938957)
                ·
                  refine ⟨3501933499391019391102109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9338489331709385042938957 3501933499391019391102109)
                  ·
                    refine ⟨1313225062271632271663291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3501933499391019391102109 1313225062271632271663291)
                    ·
                      rfl

theorem cell22_3836245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_3836245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836245 prefixEnd_3836245 := by exact prefixLift 3836245
  have htrace : WordTrace (prefixWord ++ tailWord_3836245) baseStart_3836245 baseEnd_3836245 := by
    simpa [prefixWord, tailWord_3836245, baseEnd_3836245] using wordTrace_append hprefix tailTrace_3836245
  have hstable : (prefixWord ++ tailWord_3836245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836245).length < 2 ^ (prefixWord ++ tailWord_3836245).sum := by decide
  have hdescent : baseEnd_3836245 < baseStart_3836245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836271 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 5, 4]
def baseStart_3836271 : Nat := 118140960795 + 3836271 * 2 ^ 59
def prefixEnd_3836271 : Nat := 4983230072969 + 3 ^ 40 * 3836271 * 2
def baseEnd_3836271 : Nat := 1313233962602976870513211

theorem tailTrace_3836271 : CollatzResearch.WordTrace tailWord_3836271 prefixEnd_3836271 1313233962602976870513211 := by
  unfold tailWord_3836271
  simp only [CollatzResearch.WordTrace]
  refine ⟨139920298284852824770132667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93280198856568549846755111 139920298284852824770132667)
  ·
    refine ⟨209880447427279237155199001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139920298284852824770132667 209880447427279237155199001)
    ·
      refine ⟨157410335570459427866399251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209880447427279237155199001 157410335570459427866399251)
      ·
        refine ⟨236115503355689141799598877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157410335570459427866399251 236115503355689141799598877)
        ·
          refine ⟨88543313758383428174849579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236115503355689141799598877 88543313758383428174849579)
          ·
            refine ⟨132814970637575142262274369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88543313758383428174849579 132814970637575142262274369)
            ·
              refine ⟨99611227978181356696705777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132814970637575142262274369 99611227978181356696705777)
              ·
                refine ⟨74708420983636017522529333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99611227978181356696705777 74708420983636017522529333)
                ·
                  refine ⟨7003914467215876642737125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74708420983636017522529333 7003914467215876642737125)
                  ·
                    refine ⟨1313233962602976870513211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7003914467215876642737125 1313233962602976870513211)
                    ·
                      rfl

theorem cell22_3836271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_3836271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836271 prefixEnd_3836271 := by exact prefixLift 3836271
  have htrace : WordTrace (prefixWord ++ tailWord_3836271) baseStart_3836271 baseEnd_3836271 := by
    simpa [prefixWord, tailWord_3836271, baseEnd_3836271] using wordTrace_append hprefix tailTrace_3836271
  have hstable : (prefixWord ++ tailWord_3836271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836271).length < 2 ^ (prefixWord ++ tailWord_3836271).sum := by decide
  have hdescent : baseEnd_3836271 < baseStart_3836271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836320 : List Nat := [2, 1, 1, 4, 1, 3, 3, 3, 4]
def baseStart_3836320 : Nat := 118140960795 + 3836320 * 2 ^ 59
def prefixEnd_3836320 : Nat := 4983230072969 + 3 ^ 40 * 3836320 * 2
def baseEnd_3836320 : Nat := 437750245434785692012687

theorem tailTrace_3836320 : CollatzResearch.WordTrace tailWord_3836320 prefixEnd_3836320 437750245434785692012687 := by
  unfold tailWord_3836320
  simp only [CollatzResearch.WordTrace]
  refine ⟨69961042730837653069333207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93281390307783537425777609 69961042730837653069333207)
  ·
    refine ⟨104941564096256479603999811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69961042730837653069333207 104941564096256479603999811)
    ·
      refine ⟨157412346144384719405999717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104941564096256479603999811 157412346144384719405999717)
      ·
        refine ⟨29514814902072134888624947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157412346144384719405999717 29514814902072134888624947)
        ·
          refine ⟨44272222353108202332937421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29514814902072134888624947 44272222353108202332937421)
          ·
            refine ⟨16602083382415575874851533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44272222353108202332937421 16602083382415575874851533)
            ·
              refine ⟨6225781268405840953069325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16602083382415575874851533 6225781268405840953069325)
              ·
                refine ⟨2334667975652190357400997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6225781268405840953069325 2334667975652190357400997)
                ·
                  refine ⟨437750245434785692012687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334667975652190357400997 437750245434785692012687)
                  ·
                    rfl

theorem cell22_3836320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 4].length) (baseStart_3836320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836320 prefixEnd_3836320 := by exact prefixLift 3836320
  have htrace : WordTrace (prefixWord ++ tailWord_3836320) baseStart_3836320 baseEnd_3836320 := by
    simpa [prefixWord, tailWord_3836320, baseEnd_3836320] using wordTrace_append hprefix tailTrace_3836320
  have hstable : (prefixWord ++ tailWord_3836320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836320).length < 2 ^ (prefixWord ++ tailWord_3836320).sum := by decide
  have hdescent : baseEnd_3836320 < baseStart_3836320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836337 : List Nat := [1, 2, 2, 4, 1, 3, 3, 2, 4]
def baseStart_3836337 : Nat := 118140960795 + 3836337 * 2 ^ 59
def prefixEnd_3836337 : Nat := 4983230072969 + 3 ^ 40 * 3836337 * 2
def baseEnd_3836337 : Nat := 437752185250591566121003

theorem tailTrace_3836337 : CollatzResearch.WordTrace tailWord_3836337 prefixEnd_3836337 437752185250591566121003 := by
  unfold tailWord_3836337
  simp only [CollatzResearch.WordTrace]
  refine ⟨139922705502613718042035265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93281803668409145361356843 139922705502613718042035265)
  ·
    refine ⟨104942029126960288531526449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139922705502613718042035265 104942029126960288531526449)
    ·
      refine ⟨78706521845220216398644837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104942029126960288531526449 78706521845220216398644837)
      ·
        refine ⟨14757472845978790574745907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78706521845220216398644837 14757472845978790574745907)
        ·
          refine ⟨22136209268968185862118861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14757472845978790574745907 22136209268968185862118861)
          ·
            refine ⟨8301078475863069698294573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22136209268968185862118861 8301078475863069698294573)
            ·
              refine ⟨3112904428448651136860465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8301078475863069698294573 3112904428448651136860465)
              ·
                refine ⟨2334678321336488352645349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112904428448651136860465 2334678321336488352645349)
                ·
                  refine ⟨437752185250591566121003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334678321336488352645349 437752185250591566121003)
                  ·
                    rfl

theorem cell22_3836337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 4].length) (baseStart_3836337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836337 prefixEnd_3836337 := by exact prefixLift 3836337
  have htrace : WordTrace (prefixWord ++ tailWord_3836337) baseStart_3836337 baseEnd_3836337 := by
    simpa [prefixWord, tailWord_3836337, baseEnd_3836337] using wordTrace_append hprefix tailTrace_3836337
  have hstable : (prefixWord ++ tailWord_3836337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836337).length < 2 ^ (prefixWord ++ tailWord_3836337).sum := by decide
  have hdescent : baseEnd_3836337 < baseStart_3836337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836348 : List Nat := [2, 2, 2, 4, 1, 1, 1, 9]
def baseStart_3836348 : Nat := 118140960795 + 3836348 * 2 ^ 59
def prefixEnd_3836348 : Nat := 4983230072969 + 3 ^ 40 * 3836348 * 2
def baseEnd_3836348 : Nat := 145917813475174926259775

theorem tailTrace_3836348 : CollatzResearch.WordTrace tailWord_3836348 prefixEnd_3836348 145917813475174926259775 := by
  unfold tailWord_3836348
  simp only [CollatzResearch.WordTrace]
  refine ⟨69961553352786933460342849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93282071137049244613790465 69961553352786933460342849)
  ·
    refine ⟨52471165014590200095257137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69961553352786933460342849 52471165014590200095257137)
    ·
      refine ⟨39353373760942650071442853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52471165014590200095257137 39353373760942650071442853)
      ·
        refine ⟨7378757580176746888395535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39353373760942650071442853 7378757580176746888395535)
        ·
          refine ⟨11068136370265120332593303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7378757580176746888395535 11068136370265120332593303)
          ·
            refine ⟨16602204555397680498889955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068136370265120332593303 16602204555397680498889955)
            ·
              refine ⟨24903306833096520748334933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16602204555397680498889955 24903306833096520748334933)
              ·
                refine ⟨145917813475174926259775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24903306833096520748334933 145917813475174926259775)
                ·
                  rfl

theorem cell22_3836348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 9].length) (baseStart_3836348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836348 prefixEnd_3836348 := by exact prefixLift 3836348
  have htrace : WordTrace (prefixWord ++ tailWord_3836348) baseStart_3836348 baseEnd_3836348 := by
    simpa [prefixWord, tailWord_3836348, baseEnd_3836348] using wordTrace_append hprefix tailTrace_3836348
  have hstable : (prefixWord ++ tailWord_3836348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836348).length < 2 ^ (prefixWord ++ tailWord_3836348).sum := by decide
  have hdescent : baseEnd_3836348 < baseStart_3836348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836363 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 5, 3]
def baseStart_3836363 : Nat := 118140960795 + 3836363 * 2 ^ 59
def prefixEnd_3836363 : Nat := 4983230072969 + 3 ^ 40 * 3836363 * 2
def baseEnd_3836363 : Nat := 1313265456083119297212929

theorem tailTrace_3836363 : CollatzResearch.WordTrace tailWord_3836363 prefixEnd_3836363 1313265456083119297212929 := by
  unfold tailWord_3836363
  simp only [CollatzResearch.WordTrace]
  refine ⟨139923653800519524482481743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93282435867013016321654495 139923653800519524482481743)
  ·
    refine ⟨209885480700779286723722615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139923653800519524482481743 209885480700779286723722615)
    ·
      refine ⟨314828221051168930085583923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209885480700779286723722615 314828221051168930085583923)
      ·
        refine ⟨472242331576753395128375885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314828221051168930085583923 472242331576753395128375885)
        ·
          refine ⟨177090874341282523173140957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472242331576753395128375885 177090874341282523173140957)
          ·
            refine ⟨66409077877980946189927859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177090874341282523173140957 66409077877980946189927859)
            ·
              refine ⟨99613616816971419284891789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66409077877980946189927859 99613616816971419284891789)
              ·
                refine ⟨37355106306364282231834421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99613616816971419284891789 37355106306364282231834421)
                ·
                  refine ⟨3502041216221651459234477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37355106306364282231834421 3502041216221651459234477)
                  ·
                    refine ⟨1313265456083119297212929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3502041216221651459234477 1313265456083119297212929)
                    ·
                      rfl

theorem cell22_3836363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 3].length) (baseStart_3836363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836363 prefixEnd_3836363 := by exact prefixLift 3836363
  have htrace : WordTrace (prefixWord ++ tailWord_3836363) baseStart_3836363 baseEnd_3836363 := by
    simpa [prefixWord, tailWord_3836363, baseEnd_3836363] using wordTrace_append hprefix tailTrace_3836363
  have hstable : (prefixWord ++ tailWord_3836363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836363).length < 2 ^ (prefixWord ++ tailWord_3836363).sum := by decide
  have hdescent : baseEnd_3836363 < baseStart_3836363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836386 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3836386 : Nat := 118140960795 + 3836386 * 2 ^ 59
def prefixEnd_3836386 : Nat := 4983230072969 + 3 ^ 40 * 3836386 * 2
def baseEnd_3836386 : Nat := 1313273329453154903887859

theorem tailTrace_3836386 : CollatzResearch.WordTrace tailWord_3836386 prefixEnd_3836386 1313273329453154903887859 := by
  unfold tailWord_3836386
  simp only [CollatzResearch.WordTrace]
  refine ⟨34981123169859049852642253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93282995119624132940379341 34981123169859049852642253)
  ·
    refine ⟨13117921188697143694740845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34981123169859049852642253 13117921188697143694740845)
    ·
      refine ⟨4919220445761428885527817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13117921188697143694740845 4919220445761428885527817)
      ·
        refine ⟨3689415334321071664145863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4919220445761428885527817 3689415334321071664145863)
        ·
          refine ⟨5534123001481607496218795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689415334321071664145863 5534123001481607496218795)
          ·
            refine ⟨8301184502222411244328193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5534123001481607496218795 8301184502222411244328193)
            ·
              refine ⟨6225888376666808433246145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8301184502222411244328193 6225888376666808433246145)
              ·
                refine ⟨4669416282500106324934609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6225888376666808433246145 4669416282500106324934609)
                ·
                  refine ⟨3502062211875079743700957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4669416282500106324934609 3502062211875079743700957)
                  ·
                    refine ⟨1313273329453154903887859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3502062211875079743700957 1313273329453154903887859)
                    ·
                      rfl

theorem cell22_3836386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3836386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836386 prefixEnd_3836386 := by exact prefixLift 3836386
  have htrace : WordTrace (prefixWord ++ tailWord_3836386) baseStart_3836386 baseEnd_3836386 := by
    simpa [prefixWord, tailWord_3836386, baseEnd_3836386] using wordTrace_append hprefix tailTrace_3836386
  have hstable : (prefixWord ++ tailWord_3836386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836386).length < 2 ^ (prefixWord ++ tailWord_3836386).sum := by decide
  have hdescent : baseEnd_3836386 < baseStart_3836386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836408 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_3836408 : Nat := 118140960795 + 3836408 * 2 ^ 59
def prefixEnd_3836408 : Nat := 4983230072969 + 3 ^ 40 * 3836408 * 2
def baseEnd_3836408 : Nat := 1313280860502754179837791

theorem tailTrace_3836408 : CollatzResearch.WordTrace tailWord_3836408 prefixEnd_3836408 1313280860502754179837791 := by
  unfold tailWord_3836408
  simp only [CollatzResearch.WordTrace]
  refine ⟨69962647542678248583934939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93283530056904331445246585 69962647542678248583934939)
  ·
    refine ⟨104943971314017372875902409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69962647542678248583934939 104943971314017372875902409)
    ·
      refine ⟨78707978485513029656926807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104943971314017372875902409 78707978485513029656926807)
      ·
        refine ⟨118061967728269544485390211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78707978485513029656926807 118061967728269544485390211)
        ·
          refine ⟨177092951592404316728085317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118061967728269544485390211 177092951592404316728085317)
          ·
            refine ⟨33204928423575809386515997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177092951592404316728085317 33204928423575809386515997)
            ·
              refine ⟨12451848158840928519943499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33204928423575809386515997 12451848158840928519943499)
              ·
                refine ⟨18677772238261392779915249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12451848158840928519943499 18677772238261392779915249)
                ·
                  refine ⟨14008329178696044584936437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18677772238261392779915249 14008329178696044584936437)
                  ·
                    refine ⟨1313280860502754179837791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14008329178696044584936437 1313280860502754179837791)
                    ·
                      rfl

theorem cell22_3836408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_3836408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836408 prefixEnd_3836408 := by exact prefixLift 3836408
  have htrace : WordTrace (prefixWord ++ tailWord_3836408) baseStart_3836408 baseEnd_3836408 := by
    simpa [prefixWord, tailWord_3836408, baseEnd_3836408] using wordTrace_append hprefix tailTrace_3836408
  have hstable : (prefixWord ++ tailWord_3836408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836408).length < 2 ^ (prefixWord ++ tailWord_3836408).sum := by decide
  have hdescent : baseEnd_3836408 < baseStart_3836408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836453 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_3836453 : Nat := 118140960795 + 3836453 * 2 ^ 59
def prefixEnd_3836453 : Nat := 4983230072969 + 3 ^ 40 * 3836453 * 2
def baseEnd_3836453 : Nat := 1313296264922389062462653

theorem tailTrace_3836453 : CollatzResearch.WordTrace tailWord_3836453 prefixEnd_3836453 1313296264922389062462653 := by
  unfold tailWord_3836453
  simp only [CollatzResearch.WordTrace]
  refine ⟨139926936370193469853258013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93284624246795646568838675 139926936370193469853258013)
  ·
    refine ⟨52472601138822551194971755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139926936370193469853258013 52472601138822551194971755)
    ·
      refine ⟨78708901708233826792457633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52472601138822551194971755 78708901708233826792457633)
      ·
        refine ⟨59031676281175370094343225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78708901708233826792457633 59031676281175370094343225)
        ·
          refine ⟨44273757210881527570757419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59031676281175370094343225 44273757210881527570757419)
          ·
            refine ⟨66410635816322291356136129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44273757210881527570757419 66410635816322291356136129)
            ·
              refine ⟨49807976862241718517102097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66410635816322291356136129 49807976862241718517102097)
              ·
                refine ⟨37355982646681288887826573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49807976862241718517102097 37355982646681288887826573)
                ·
                  refine ⟨14008493492505483332934965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37355982646681288887826573 14008493492505483332934965)
                  ·
                    refine ⟨1313296264922389062462653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14008493492505483332934965 1313296264922389062462653)
                    ·
                      rfl

theorem cell22_3836453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_3836453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836453 prefixEnd_3836453 := by exact prefixLift 3836453
  have htrace : WordTrace (prefixWord ++ tailWord_3836453) baseStart_3836453 baseEnd_3836453 := by
    simpa [prefixWord, tailWord_3836453, baseEnd_3836453] using wordTrace_append hprefix tailTrace_3836453
  have hstable : (prefixWord ++ tailWord_3836453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836453).length < 2 ^ (prefixWord ++ tailWord_3836453).sum := by decide
  have hdescent : baseEnd_3836453 < baseStart_3836453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836500 : List Nat := [2, 4, 1, 1, 1, 5, 8]
def baseStart_3836500 : Nat := 118140960795 + 3836500 * 2 ^ 59
def prefixEnd_3836500 : Nat := 4983230072969 + 3 ^ 40 * 3836500 * 2
def baseEnd_3836500 : Nat := 48641198295662837279167

theorem tailTrace_3836500 : CollatzResearch.WordTrace tailWord_3836500 prefixEnd_3836500 48641198295662837279167 := by
  unfold tailWord_3836500
  simp only [CollatzResearch.WordTrace]
  refine ⟨69964325300511598440109477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93285767067348797920145969 69964325300511598440109477)
  ·
    refine ⟨13118310993845924707520527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69964325300511598440109477 13118310993845924707520527)
    ·
      refine ⟨19677466490768887061280791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13118310993845924707520527 19677466490768887061280791)
      ·
        refine ⟨29516199736153330591921187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19677466490768887061280791 29516199736153330591921187)
        ·
          refine ⟨44274299604229995887881781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29516199736153330591921187 44274299604229995887881781)
          ·
            refine ⟨4150715587896562114488917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44274299604229995887881781 4150715587896562114488917)
            ·
              refine ⟨48641198295662837279167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4150715587896562114488917 48641198295662837279167)
              ·
                rfl

theorem cell22_3836500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 8].length) (baseStart_3836500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836500 prefixEnd_3836500 := by exact prefixLift 3836500
  have htrace : WordTrace (prefixWord ++ tailWord_3836500) baseStart_3836500 baseEnd_3836500 := by
    simpa [prefixWord, tailWord_3836500, baseEnd_3836500] using wordTrace_append hprefix tailTrace_3836500
  have hstable : (prefixWord ++ tailWord_3836500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836500).length < 2 ^ (prefixWord ++ tailWord_3836500).sum := by decide
  have hdescent : baseEnd_3836500 < baseStart_3836500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836543 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 3, 7]
def baseStart_3836543 : Nat := 118140960795 + 3836543 * 2 ^ 59
def prefixEnd_3836543 : Nat := 4983230072969 + 3 ^ 40 * 3836543 * 2
def baseEnd_3836543 : Nat := 1313327073761658827712377

theorem tailTrace_3836543 : CollatzResearch.WordTrace tailWord_3836543 prefixEnd_3836543 1313327073761658827712377 := by
  unfold tailWord_3836543
  simp only [CollatzResearch.WordTrace]
  refine ⟨139930218939867415224034283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93286812626578276816022855 139930218939867415224034283)
  ·
    refine ⟨209895328409801122836051425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139930218939867415224034283 209895328409801122836051425)
    ·
      refine ⟨157421496307350842127038569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209895328409801122836051425 157421496307350842127038569)
      ·
        refine ⟨118066122230513131595278927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157421496307350842127038569 118066122230513131595278927)
        ·
          refine ⟨177099183345769697392918391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118066122230513131595278927 177099183345769697392918391)
          ·
            refine ⟨265648775018654546089377587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177099183345769697392918391 265648775018654546089377587)
            ·
              refine ⟨398473162527981819134066381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265648775018654546089377587 398473162527981819134066381)
              ·
                refine ⟨149427435947993182175274893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398473162527981819134066381 149427435947993182175274893)
                ·
                  refine ⟨56035288480497443315728085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149427435947993182175274893 56035288480497443315728085)
                  ·
                    refine ⟨1313327073761658827712377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56035288480497443315728085 1313327073761658827712377)
                    ·
                      rfl

theorem cell22_3836543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_3836543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836543 prefixEnd_3836543 := by exact prefixLift 3836543
  have htrace : WordTrace (prefixWord ++ tailWord_3836543) baseStart_3836543 baseEnd_3836543 := by
    simpa [prefixWord, tailWord_3836543, baseEnd_3836543] using wordTrace_append hprefix tailTrace_3836543
  have hstable : (prefixWord ++ tailWord_3836543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836543).length < 2 ^ (prefixWord ++ tailWord_3836543).sum := by decide
  have hdescent : baseEnd_3836543 < baseStart_3836543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836562 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_3836562 : Nat := 118140960795 + 3836562 * 2 ^ 59
def prefixEnd_3836562 : Nat := 4983230072969 + 3 ^ 40 * 3836562 * 2
def baseEnd_3836562 : Nat := 437777859283316370495773

theorem tailTrace_3836562 : CollatzResearch.WordTrace tailWord_3836562 prefixEnd_3836562 437777859283316370495773 := by
  unfold tailWord_3836562
  simp only [CollatzResearch.WordTrace]
  refine ⟨34982727981699645367243985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93287274617865720979317293 34982727981699645367243985)
  ·
    refine ⟨26237045986274734025432989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34982727981699645367243985 26237045986274734025432989)
    ·
      refine ⟨9838892244853025259537371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26237045986274734025432989 9838892244853025259537371)
      ·
        refine ⟨14758338367279537889306057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9838892244853025259537371 14758338367279537889306057)
        ·
          refine ⟨11068753775459653416979543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14758338367279537889306057 11068753775459653416979543)
          ·
            refine ⟨16603130663189480125469315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068753775459653416979543 16603130663189480125469315)
            ·
              refine ⟨24904695994784220188203973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16603130663189480125469315 24904695994784220188203973)
              ·
                refine ⟨4669630499022041285288245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24904695994784220188203973 4669630499022041285288245)
                ·
                  refine ⟨437777859283316370495773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4669630499022041285288245 437777859283316370495773)
                  ·
                    rfl

theorem cell22_3836562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_3836562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836562 prefixEnd_3836562 := by exact prefixLift 3836562
  have htrace : WordTrace (prefixWord ++ tailWord_3836562) baseStart_3836562 baseEnd_3836562 := by
    simpa [prefixWord, tailWord_3836562, baseEnd_3836562] using wordTrace_append hprefix tailTrace_3836562
  have hstable : (prefixWord ++ tailWord_3836562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836562).length < 2 ^ (prefixWord ++ tailWord_3836562).sum := by decide
  have hdescent : baseEnd_3836562 < baseStart_3836562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836577 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 2, 5]
def baseStart_3836577 : Nat := 118140960795 + 3836577 * 2 ^ 59
def prefixEnd_3836577 : Nat := 4983230072969 + 3 ^ 40 * 3836577 * 2
def baseEnd_3836577 : Nat := 1313338712656494072362273

theorem tailTrace_3836577 : CollatzResearch.WordTrace tailWord_3836577 prefixEnd_3836577 1313338712656494072362273 := by
  unfold tailWord_3836577
  simp only [CollatzResearch.WordTrace]
  refine ⟨139931459021744239030771985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93287639347829492687181323 139931459021744239030771985)
  ·
    refine ⟨104948594266308179273078989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139931459021744239030771985 104948594266308179273078989)
    ·
      refine ⟨39355722849865567227404621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104948594266308179273078989 39355722849865567227404621)
      ·
        refine ⟨14758396068699587710276733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39355722849865567227404621 14758396068699587710276733)
        ·
          refine ⟨5534398525762345391353775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14758396068699587710276733 5534398525762345391353775)
          ·
            refine ⟨8301597788643518087030663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5534398525762345391353775 8301597788643518087030663)
            ·
              refine ⟨12452396682965277130545995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8301597788643518087030663 12452396682965277130545995)
              ·
                refine ⟨18678595024447915695818993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12452396682965277130545995 18678595024447915695818993)
                ·
                  refine ⟨14008946268335936771864245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18678595024447915695818993 14008946268335936771864245)
                  ·
                    refine ⟨1313338712656494072362273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14008946268335936771864245 1313338712656494072362273)
                    ·
                      rfl

theorem cell22_3836577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_3836577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836577 prefixEnd_3836577 := by exact prefixLift 3836577
  have htrace : WordTrace (prefixWord ++ tailWord_3836577) baseStart_3836577 baseEnd_3836577 := by
    simpa [prefixWord, tailWord_3836577, baseEnd_3836577] using wordTrace_append hprefix tailTrace_3836577
  have hstable : (prefixWord ++ tailWord_3836577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836577).length < 2 ^ (prefixWord ++ tailWord_3836577).sum := by decide
  have hdescent : baseEnd_3836577 < baseStart_3836577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836607 : List Nat := [1, 1, 2, 2, 2, 4, 1, 5, 4]
def baseStart_3836607 : Nat := 118140960795 + 3836607 * 2 ^ 59
def prefixEnd_3836607 : Nat := 4983230072969 + 3 ^ 40 * 3836607 * 2
def baseEnd_3836607 : Nat := 437782994089861331370727

theorem tailTrace_3836607 : CollatzResearch.WordTrace tailWord_3836607 prefixEnd_3836607 437782994089861331370727 := by
  unfold tailWord_3836607
  simp only [CollatzResearch.WordTrace]
  refine ⟨139932553211635554154364075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93288368807757036102909383 139932553211635554154364075)
  ·
    refine ⟨209898829817453331231546113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139932553211635554154364075 209898829817453331231546113)
    ·
      refine ⟨157424122363089998423659585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209898829817453331231546113 157424122363089998423659585)
      ·
        refine ⟨118068091772317498817744689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157424122363089998423659585 118068091772317498817744689)
        ·
          refine ⟨88551068829238124113308517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118068091772317498817744689 88551068829238124113308517)
          ·
            refine ⟨16603325405482148271245347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88551068829238124113308517 16603325405482148271245347)
            ·
              refine ⟨24904988108223222406868021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16603325405482148271245347 24904988108223222406868021)
              ·
                refine ⟨2334842635145927100643877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24904988108223222406868021 2334842635145927100643877)
                ·
                  refine ⟨437782994089861331370727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334842635145927100643877 437782994089861331370727)
                  ·
                    rfl

theorem cell22_3836607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 4].length) (baseStart_3836607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836607 prefixEnd_3836607 := by exact prefixLift 3836607
  have htrace : WordTrace (prefixWord ++ tailWord_3836607) baseStart_3836607 baseEnd_3836607 := by
    simpa [prefixWord, tailWord_3836607, baseEnd_3836607] using wordTrace_append hprefix tailTrace_3836607
  have hstable : (prefixWord ++ tailWord_3836607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836607).length < 2 ^ (prefixWord ++ tailWord_3836607).sum := by decide
  have hdescent : baseEnd_3836607 < baseStart_3836607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836650 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_3836650 : Nat := 118140960795 + 3836650 * 2 ^ 59
def prefixEnd_3836650 : Nat := 4983230072969 + 3 ^ 40 * 3836650 * 2
def baseEnd_3836650 : Nat := 1313363702048346215287049

theorem tailTrace_3836650 : CollatzResearch.WordTrace tailWord_3836650 prefixEnd_3836650 1313363702048346215287049 := by
  unfold tailWord_3836650
  simp only [CollatzResearch.WordTrace]
  refine ⟨34983530387619943124544851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93289414366986514998786269 34983530387619943124544851)
  ·
    refine ⟨52475295581429914686817277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34983530387619943124544851 52475295581429914686817277)
    ·
      refine ⟨19678235843036218007556479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52475295581429914686817277 19678235843036218007556479)
      ·
        refine ⟨29517353764554327011334719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19678235843036218007556479 29517353764554327011334719)
        ·
          refine ⟨44276030646831490517002079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29517353764554327011334719 44276030646831490517002079)
          ·
            refine ⟨66414045970247235775503119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44276030646831490517002079 66414045970247235775503119)
            ·
              refine ⟨99621068955370853663254679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66414045970247235775503119 99621068955370853663254679)
              ·
                refine ⟨149431603433056280494882019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99621068955370853663254679 149431603433056280494882019)
                ·
                  refine ⟨224147405149584420742323029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149431603433056280494882019 224147405149584420742323029)
                  ·
                    refine ⟨1313363702048346215287049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 224147405149584420742323029 1313363702048346215287049)
                    ·
                      rfl

theorem cell22_3836650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_3836650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836650 prefixEnd_3836650 := by exact prefixLift 3836650
  have htrace : WordTrace (prefixWord ++ tailWord_3836650) baseStart_3836650 baseEnd_3836650 := by
    simpa [prefixWord, tailWord_3836650, baseEnd_3836650] using wordTrace_append hprefix tailTrace_3836650
  have hstable : (prefixWord ++ tailWord_3836650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836650).length < 2 ^ (prefixWord ++ tailWord_3836650).sum := by decide
  have hdescent : baseEnd_3836650 < baseStart_3836650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836690 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3836690 : Nat := 118140960795 + 3836690 * 2 ^ 59
def prefixEnd_3836690 : Nat := 4983230072969 + 3 ^ 40 * 3836690 * 2
def baseEnd_3836690 : Nat := 1313377394865799444286927

theorem tailTrace_3836690 : CollatzResearch.WordTrace tailWord_3836690 prefixEnd_3836690 1313377394865799444286927 := by
  unfold tailWord_3836690
  simp only [CollatzResearch.WordTrace]
  refine ⟨34983895117583714832408881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93290386980223239553090349 34983895117583714832408881)
  ·
    refine ⟨26237921338187786124306661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34983895117583714832408881 26237921338187786124306661)
    ·
      refine ⟨4919610250910209898307499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26237921338187786124306661 4919610250910209898307499)
      ·
        refine ⟨7379415376365314847461249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919610250910209898307499 7379415376365314847461249)
        ·
          refine ⟨5534561532273986135595937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7379415376365314847461249 5534561532273986135595937)
          ·
            refine ⟨4150921149205489601696953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5534561532273986135595937 4150921149205489601696953)
            ·
              refine ⟨3113190861904117201272715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150921149205489601696953 3113190861904117201272715)
              ·
                refine ⟨4669786292856175801909073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113190861904117201272715 4669786292856175801909073)
                ·
                  refine ⟨3502339719642131851431805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4669786292856175801909073 3502339719642131851431805)
                  ·
                    refine ⟨1313377394865799444286927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3502339719642131851431805 1313377394865799444286927)
                    ·
                      rfl

theorem cell22_3836690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3836690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836690 prefixEnd_3836690 := by exact prefixLift 3836690
  have htrace : WordTrace (prefixWord ++ tailWord_3836690) baseStart_3836690 baseEnd_3836690 := by
    simpa [prefixWord, tailWord_3836690, baseEnd_3836690] using wordTrace_append hprefix tailTrace_3836690
  have hstable : (prefixWord ++ tailWord_3836690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836690).length < 2 ^ (prefixWord ++ tailWord_3836690).sum := by decide
  have hdescent : baseEnd_3836690 < baseStart_3836690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836776 : List Nat := [2, 1, 4, 2, 1, 3, 2, 3, 4]
def baseStart_3836776 : Nat := 118140960795 + 3836776 * 2 ^ 59
def prefixEnd_3836776 : Nat := 4983230072969 + 3 ^ 40 * 3836776 * 2
def baseEnd_3836776 : Nat := 437802278141107962212221

theorem tailTrace_3836776 : CollatzResearch.WordTrace tailWord_3836776 prefixEnd_3836776 437802278141107962212221 := by
  unfold tailWord_3836776
  simp only [CollatzResearch.WordTrace]
  refine ⟨69969358574011648008633091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93292478098682197344844121 69969358574011648008633091)
  ·
    refine ⟨104954037861017472012949637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69969358574011648008633091 104954037861017472012949637)
    ·
      refine ⟨19678882098940776002428057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104954037861017472012949637 19678882098940776002428057)
      ·
        refine ⟨14759161574205582001821043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19678882098940776002428057 14759161574205582001821043)
        ·
          refine ⟨22138742361308373002731565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14759161574205582001821043 22138742361308373002731565)
          ·
            refine ⟨8302028385490639876024337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22138742361308373002731565 8302028385490639876024337)
            ·
              refine ⟨6226521289117979907018253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8302028385490639876024337 6226521289117979907018253)
              ·
                refine ⟨2334945483419242465131845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6226521289117979907018253 2334945483419242465131845)
                ·
                  refine ⟨437802278141107962212221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334945483419242465131845 437802278141107962212221)
                  ·
                    rfl

theorem cell22_3836776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 4].length) (baseStart_3836776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836776 prefixEnd_3836776 := by exact prefixLift 3836776
  have htrace : WordTrace (prefixWord ++ tailWord_3836776) baseStart_3836776 baseEnd_3836776 := by
    simpa [prefixWord, tailWord_3836776, baseEnd_3836776] using wordTrace_append hprefix tailTrace_3836776
  have hstable : (prefixWord ++ tailWord_3836776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836776).length < 2 ^ (prefixWord ++ tailWord_3836776).sum := by decide
  have hdescent : baseEnd_3836776 < baseStart_3836776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836808 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 2, 3]
def baseStart_3836808 : Nat := 118140960795 + 3836808 * 2 ^ 59
def prefixEnd_3836808 : Nat := 4983230072969 + 3 ^ 40 * 3836808 * 2
def baseEnd_3836808 : Nat := 1313417788677286469836565

theorem tailTrace_3836808 : CollatzResearch.WordTrace tailWord_3836808 prefixEnd_3836808 1313417788677286469836565 := by
  unfold tailWord_3836808
  simp only [CollatzResearch.WordTrace]
  refine ⟨69969942141953682741215539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93293256189271576988287385 69969942141953682741215539)
  ·
    refine ⟨104954913212930524111823309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69969942141953682741215539 104954913212930524111823309)
    ·
      refine ⟨39358092454848946541933741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104954913212930524111823309 39358092454848946541933741)
      ·
        refine ⟨14759284670568354953225153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39358092454848946541933741 14759284670568354953225153)
        ·
          refine ⟨11069463502926266214918865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14759284670568354953225153 11069463502926266214918865)
          ·
            refine ⟨8302097627194699661189149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11069463502926266214918865 8302097627194699661189149)
            ·
              refine ⟨3113286610198012372945931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8302097627194699661189149 3113286610198012372945931)
              ·
                refine ⟨4669929915297018559418897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113286610198012372945931 4669929915297018559418897)
                ·
                  refine ⟨3502447436472763919564173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4669929915297018559418897 3502447436472763919564173)
                  ·
                    refine ⟨1313417788677286469836565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3502447436472763919564173 1313417788677286469836565)
                    ·
                      rfl

theorem cell22_3836808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_3836808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836808 prefixEnd_3836808 := by exact prefixLift 3836808
  have htrace : WordTrace (prefixWord ++ tailWord_3836808) baseStart_3836808 baseEnd_3836808 := by
    simpa [prefixWord, tailWord_3836808, baseEnd_3836808] using wordTrace_append hprefix tailTrace_3836808
  have hstable : (prefixWord ++ tailWord_3836808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836808).length < 2 ^ (prefixWord ++ tailWord_3836808).sum := by decide
  have hdescent : baseEnd_3836808 < baseStart_3836808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836832 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 7]
def baseStart_3836832 : Nat := 118140960795 + 3836832 * 2 ^ 59
def prefixEnd_3836832 : Nat := 4983230072969 + 3 ^ 40 * 3836832 * 2
def baseEnd_3836832 : Nat := 437808668122586135745497

theorem tailTrace_3836832 : CollatzResearch.WordTrace tailWord_3836832 prefixEnd_3836832 437808668122586135745497 := by
  unfold tailWord_3836832
  simp only [CollatzResearch.WordTrace]
  refine ⟨69970379817910208790652375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93293839757213611720869833 69970379817910208790652375)
  ·
    refine ⟨104955569726865313185978563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69970379817910208790652375 104955569726865313185978563)
    ·
      refine ⟨157433354590297969778967845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104955569726865313185978563 157433354590297969778967845)
      ·
        refine ⟨29518753985680869333556471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157433354590297969778967845 29518753985680869333556471)
        ·
          refine ⟨44278130978521304000334707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29518753985680869333556471 44278130978521304000334707)
          ·
            refine ⟨66417196467781956000502061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44278130978521304000334707 66417196467781956000502061)
            ·
              refine ⟨24906448675418233500188273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66417196467781956000502061 24906448675418233500188273)
              ·
                refine ⟨18679836506563675125141205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24906448675418233500188273 18679836506563675125141205)
                ·
                  refine ⟨437808668122586135745497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18679836506563675125141205 437808668122586135745497)
                  ·
                    rfl

theorem cell22_3836832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_3836832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836832 prefixEnd_3836832 := by exact prefixLift 3836832
  have htrace : WordTrace (prefixWord ++ tailWord_3836832) baseStart_3836832 baseEnd_3836832 := by
    simpa [prefixWord, tailWord_3836832, baseEnd_3836832] using wordTrace_append hprefix tailTrace_3836832
  have hstable : (prefixWord ++ tailWord_3836832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836832).length < 2 ^ (prefixWord ++ tailWord_3836832).sum := by decide
  have hdescent : baseEnd_3836832 < baseStart_3836832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836847 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 2, 5]
def baseStart_3836847 : Nat := 118140960795 + 3836847 * 2 ^ 59
def prefixEnd_3836847 : Nat := 4983230072969 + 3 ^ 40 * 3836847 * 2
def baseEnd_3836847 : Nat := 1313431139174303368111445

theorem tailTrace_3836847 : CollatzResearch.WordTrace tailWord_3836847 prefixEnd_3836847 1313431139174303368111445 := by
  unfold tailWord_3836847
  simp only [CollatzResearch.WordTrace]
  refine ⟨139941306730766075143100795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93294204487177383428733863 139941306730766075143100795)
  ·
    refine ⟨209911960096149112714651193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139941306730766075143100795 209911960096149112714651193)
    ·
      refine ⟨157433970072111834535988395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209911960096149112714651193 157433970072111834535988395)
      ·
        refine ⟨236150955108167751803982593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157433970072111834535988395 236150955108167751803982593)
        ·
          refine ⟨177113216331125813852986945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236150955108167751803982593 177113216331125813852986945)
          ·
            refine ⟨132834912248344360389740209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177113216331125813852986945 132834912248344360389740209)
            ·
              refine ⟨99626184186258270292305157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132834912248344360389740209 99626184186258270292305157)
              ·
                refine ⟨18679909534923425679807217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99626184186258270292305157 18679909534923425679807217)
                ·
                  refine ⟨14009932151192569259855413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18679909534923425679807217 14009932151192569259855413)
                  ·
                    refine ⟨1313431139174303368111445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14009932151192569259855413 1313431139174303368111445)
                    ·
                      rfl

theorem cell22_3836847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_3836847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836847 prefixEnd_3836847 := by exact prefixLift 3836847
  have htrace : WordTrace (prefixWord ++ tailWord_3836847) baseStart_3836847 baseEnd_3836847 := by
    simpa [prefixWord, tailWord_3836847, baseEnd_3836847] using wordTrace_append hprefix tailTrace_3836847
  have hstable : (prefixWord ++ tailWord_3836847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836847).length < 2 ^ (prefixWord ++ tailWord_3836847).sum := by decide
  have hdescent : baseEnd_3836847 < baseStart_3836847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836879 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 3, 4]
def baseStart_3836879 : Nat := 118140960795 + 3836879 * 2 ^ 59
def prefixEnd_3836879 : Nat := 4983230072969 + 3 ^ 40 * 3836879 * 2
def baseEnd_3836879 : Nat := 1313442093428265951311347

theorem tailTrace_3836879 : CollatzResearch.WordTrace tailWord_3836879 prefixEnd_3836879 1313442093428265951311347 := by
  unfold tailWord_3836879
  simp only [CollatzResearch.WordTrace]
  refine ⟨139942473866650144608265691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93294982577766763072177127 139942473866650144608265691)
  ·
    refine ⟨209913710799975216912398537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139942473866650144608265691 209913710799975216912398537)
    ·
      refine ⟨157435283099981412684298903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209913710799975216912398537 157435283099981412684298903)
      ·
        refine ⟨236152924649972119026448355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157435283099981412684298903 236152924649972119026448355)
        ·
          refine ⟨354229386974958178539672533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236152924649972119026448355 354229386974958178539672533)
          ·
            refine ⟨8302251257225582309523575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 354229386974958178539672533 8302251257225582309523575)
            ·
              refine ⟨12453376885838373464285363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8302251257225582309523575 12453376885838373464285363)
              ·
                refine ⟨18680065328757560196428045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12453376885838373464285363 18680065328757560196428045)
                ·
                  refine ⟨7005024498284085073660517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18680065328757560196428045 7005024498284085073660517)
                  ·
                    refine ⟨1313442093428265951311347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7005024498284085073660517 1313442093428265951311347)
                    ·
                      rfl

theorem cell22_3836879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_3836879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836879 prefixEnd_3836879 := by exact prefixLift 3836879
  have htrace : WordTrace (prefixWord ++ tailWord_3836879) baseStart_3836879 baseEnd_3836879 := by
    simpa [prefixWord, tailWord_3836879, baseEnd_3836879] using wordTrace_append hprefix tailTrace_3836879
  have hstable : (prefixWord ++ tailWord_3836879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836879).length < 2 ^ (prefixWord ++ tailWord_3836879).sum := by decide
  have hdescent : baseEnd_3836879 < baseStart_3836879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836907 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 5, 6]
def baseStart_3836907 : Nat := 118140960795 + 3836907 * 2 ^ 59
def prefixEnd_3836907 : Nat := 4983230072969 + 3 ^ 40 * 3836907 * 2
def baseEnd_3836907 : Nat := 1313451678400483211611261

theorem tailTrace_3836907 : CollatzResearch.WordTrace tailWord_3836907 prefixEnd_3836907 1313451678400483211611261 := by
  unfold tailWord_3836907
  simp only [CollatzResearch.WordTrace]
  refine ⟨139943495110548705390284975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93295663407032470260189983 139943495110548705390284975)
  ·
    refine ⟨209915242665823058085427463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139943495110548705390284975 209915242665823058085427463)
    ·
      refine ⟨314872863998734587128141195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209915242665823058085427463 314872863998734587128141195)
      ·
        refine ⟨472309295998101880692211793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314872863998734587128141195 472309295998101880692211793)
        ·
          refine ⟨354231971998576410519158845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472309295998101880692211793 354231971998576410519158845)
          ·
            refine ⟨132836989499466153944684567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354231971998576410519158845 132836989499466153944684567)
            ·
              refine ⟨199255484249199230917026851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132836989499466153944684567 199255484249199230917026851)
              ·
                refine ⟨298883226373798846375540277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199255484249199230917026851 298883226373798846375540277)
                ·
                  refine ⟨28020302472543641847706901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 298883226373798846375540277 28020302472543641847706901)
                  ·
                    refine ⟨1313451678400483211611261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28020302472543641847706901 1313451678400483211611261)
                    ·
                      rfl

theorem cell22_3836907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_3836907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836907 prefixEnd_3836907 := by exact prefixLift 3836907
  have htrace : WordTrace (prefixWord ++ tailWord_3836907) baseStart_3836907 baseEnd_3836907 := by
    simpa [prefixWord, tailWord_3836907, baseEnd_3836907] using wordTrace_append hprefix tailTrace_3836907
  have hstable : (prefixWord ++ tailWord_3836907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836907).length < 2 ^ (prefixWord ++ tailWord_3836907).sum := by decide
  have hdescent : baseEnd_3836907 < baseStart_3836907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836911 : List Nat := [1, 1, 2, 1, 4, 4, 1, 4, 4]
def baseStart_3836911 : Nat := 118140960795 + 3836911 * 2 ^ 59
def prefixEnd_3836911 : Nat := 4983230072969 + 3 ^ 40 * 3836911 * 2
def baseEnd_3836911 : Nat := 437817682560742844837083

theorem tailTrace_3836911 : CollatzResearch.WordTrace tailWord_3836911 prefixEnd_3836911 437817682560742844837083 := by
  unfold tailWord_3836911
  simp only [CollatzResearch.WordTrace]
  refine ⟨139943641002534214073430587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93295760668356142715620391 139943641002534214073430587)
  ·
    refine ⟨209915461503801321110145881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139943641002534214073430587 209915461503801321110145881)
    ·
      refine ⟨157436596127850990832609411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209915461503801321110145881 157436596127850990832609411)
      ·
        refine ⟨236154894191776486248914117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157436596127850990832609411 236154894191776486248914117)
        ·
          refine ⟨44279042660958091171671397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236154894191776486248914117 44279042660958091171671397)
          ·
            refine ⟨8302320498929642094688387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44279042660958091171671397 8302320498929642094688387)
            ·
              refine ⟨12453480748394463142032581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8302320498929642094688387 12453480748394463142032581)
              ·
                refine ⟨2335027640323961839131109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12453480748394463142032581 2335027640323961839131109)
                ·
                  refine ⟨437817682560742844837083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335027640323961839131109 437817682560742844837083)
                  ·
                    rfl

theorem cell22_3836911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 4].length) (baseStart_3836911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836911 prefixEnd_3836911 := by exact prefixLift 3836911
  have htrace : WordTrace (prefixWord ++ tailWord_3836911) baseStart_3836911 baseEnd_3836911 := by
    simpa [prefixWord, tailWord_3836911, baseEnd_3836911] using wordTrace_append hprefix tailTrace_3836911
  have hstable : (prefixWord ++ tailWord_3836911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836911).length < 2 ^ (prefixWord ++ tailWord_3836911).sum := by decide
  have hdescent : baseEnd_3836911 < baseStart_3836911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836971 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 3, 3]
def baseStart_3836971 : Nat := 118140960795 + 3836971 * 2 ^ 59
def prefixEnd_3836971 : Nat := 4983230072969 + 3 ^ 40 * 3836971 * 2
def baseEnd_3836971 : Nat := 1313473586908408378011065

theorem tailTrace_3836971 : CollatzResearch.WordTrace tailWord_3836971 prefixEnd_3836971 1313473586908408378011065 := by
  unfold tailWord_3836971
  simp only [CollatzResearch.WordTrace]
  refine ⟨139945829382316844320614767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93297219588211229547076511 139945829382316844320614767)
  ·
    refine ⟨209918744073475266480922151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139945829382316844320614767 209918744073475266480922151)
    ·
      refine ⟨314878116110212899721383227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209918744073475266480922151 314878116110212899721383227)
      ·
        refine ⟨472317174165319349582074841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314878116110212899721383227 472317174165319349582074841)
        ·
          refine ⟨354237880623989512186556131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472317174165319349582074841 354237880623989512186556131)
          ·
            refine ⟨531356820935984268279834197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354237880623989512186556131 531356820935984268279834197)
            ·
              refine ⟨6226837745343565643904307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 531356820935984268279834197 6226837745343565643904307)
              ·
                refine ⟨9340256618015348465856461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226837745343565643904307 9340256618015348465856461)
                ·
                  refine ⟨3502596231755755674696173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9340256618015348465856461 3502596231755755674696173)
                  ·
                    refine ⟨1313473586908408378011065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3502596231755755674696173 1313473586908408378011065)
                    ·
                      rfl

theorem cell22_3836971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 3].length) (baseStart_3836971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3836971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3836971 prefixEnd_3836971 := by exact prefixLift 3836971
  have htrace : WordTrace (prefixWord ++ tailWord_3836971) baseStart_3836971 baseEnd_3836971 := by
    simpa [prefixWord, tailWord_3836971, baseEnd_3836971] using wordTrace_append hprefix tailTrace_3836971
  have hstable : (prefixWord ++ tailWord_3836971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836971).length < 2 ^ (prefixWord ++ tailWord_3836971).sum := by decide
  have hdescent : baseEnd_3836971 < baseStart_3836971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837022 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3837022 : Nat := 118140960795 + 3837022 * 2 ^ 59
def prefixEnd_3837022 : Nat := 4983230072969 + 3 ^ 40 * 3837022 * 2
def baseEnd_3837022 : Nat := 1313491045250661244985909

theorem tailTrace_3837022 : CollatzResearch.WordTrace tailWord_3837022 prefixEnd_3837022 1313491045250661244985909 := by
  unfold tailWord_3837022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17493461188141510003840165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93298459670088053353814213 17493461188141510003840165)
  ·
    refine ⟨3280023972776533125720031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17493461188141510003840165 3280023972776533125720031)
    ·
      refine ⟨4920035959164799688580047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3280023972776533125720031 4920035959164799688580047)
      ·
        refine ⟨7380053938747199532870071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4920035959164799688580047 7380053938747199532870071)
        ·
          refine ⟨11070080908120799299305107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380053938747199532870071 11070080908120799299305107)
          ·
            refine ⟨16605121362181198948957661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11070080908120799299305107 16605121362181198948957661)
            ·
              refine ⟨6226920510817949605859123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16605121362181198948957661 6226920510817949605859123)
              ·
                refine ⟨9340380766226924408788685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226920510817949605859123 9340380766226924408788685)
                ·
                  refine ⟨3502642787335096653295757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9340380766226924408788685 3502642787335096653295757)
                  ·
                    refine ⟨1313491045250661244985909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3502642787335096653295757 1313491045250661244985909)
                    ·
                      rfl

theorem cell22_3837022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3837022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837022 prefixEnd_3837022 := by exact prefixLift 3837022
  have htrace : WordTrace (prefixWord ++ tailWord_3837022) baseStart_3837022 baseEnd_3837022 := by
    simpa [prefixWord, tailWord_3837022, baseEnd_3837022] using wordTrace_append hprefix tailTrace_3837022
  have hstable : (prefixWord ++ tailWord_3837022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837022).length < 2 ^ (prefixWord ++ tailWord_3837022).sum := by decide
  have hdescent : baseEnd_3837022 < baseStart_3837022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837046 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3837046 : Nat := 118140960795 + 3837046 * 2 ^ 59
def prefixEnd_3837046 : Nat := 4983230072969 + 3 ^ 40 * 3837046 * 2
def baseEnd_3837046 : Nat := 437833086980377727461945

theorem tailTrace_3837046 : CollatzResearch.WordTrace tailWord_3837046 prefixEnd_3837046 437833086980377727461945 := by
  unfold tailWord_3837046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8746785303565320758099687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93299043238030088086396661 8746785303565320758099687)
  ·
    refine ⟨13120177955347981137149531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8746785303565320758099687 13120177955347981137149531)
    ·
      refine ⟨19680266933021971705724297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13120177955347981137149531 19680266933021971705724297)
      ·
        refine ⟨14760200199766478779293223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19680266933021971705724297 14760200199766478779293223)
        ·
          refine ⟨22140300299649718168939835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14760200199766478779293223 22140300299649718168939835)
          ·
            refine ⟨33210450449474577253409753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22140300299649718168939835 33210450449474577253409753)
            ·
              refine ⟨24907837837105932940057315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33210450449474577253409753 24907837837105932940057315)
              ·
                refine ⟨37361756755658899410085973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24907837837105932940057315 37361756755658899410085973)
                ·
                  refine ⟨437833086980377727461945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37361756755658899410085973 437833086980377727461945)
                  ·
                    rfl

theorem cell22_3837046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3837046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837046 prefixEnd_3837046 := by exact prefixLift 3837046
  have htrace : WordTrace (prefixWord ++ tailWord_3837046) baseStart_3837046 baseEnd_3837046 := by
    simpa [prefixWord, tailWord_3837046, baseEnd_3837046] using wordTrace_append hprefix tailTrace_3837046
  have hstable : (prefixWord ++ tailWord_3837046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837046).length < 2 ^ (prefixWord ++ tailWord_3837046).sum := by decide
  have hdescent : baseEnd_3837046 < baseStart_3837046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837080 : List Nat := [2, 1, 2, 4, 2, 1, 4, 2, 4]
def baseStart_3837080 : Nat := 118140960795 + 3837080 * 2 ^ 59
def prefixEnd_3837080 : Nat := 4983230072969 + 3 ^ 40 * 3837080 * 2
def baseEnd_3837080 : Nat := 437836966611989475678577

theorem tailTrace_3837080 : CollatzResearch.WordTrace tailWord_3837080 prefixEnd_3837080 437836966611989475678577 := by
  unfold tailWord_3837080
  simp only [CollatzResearch.WordTrace]
  refine ⟨69974902469460977968166347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93299869959281303957555129 69974902469460977968166347)
  ·
    refine ⟨104962353704191466952249521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69974902469460977968166347 104962353704191466952249521)
    ·
      refine ⟨78721765278143600214187141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104962353704191466952249521 78721765278143600214187141)
      ·
        refine ⟨14760330989651925040160089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78721765278143600214187141 14760330989651925040160089)
        ·
          refine ⟨11070248242238943780120067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14760330989651925040160089 11070248242238943780120067)
          ·
            refine ⟨16605372363358415670180101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11070248242238943780120067 16605372363358415670180101)
            ·
              refine ⟨3113507318129702938158769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16605372363358415670180101 3113507318129702938158769)
              ·
                refine ⟨2335130488597277203619077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3113507318129702938158769 2335130488597277203619077)
                ·
                  refine ⟨437836966611989475678577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335130488597277203619077 437836966611989475678577)
                  ·
                    rfl

theorem cell22_3837080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 4].length) (baseStart_3837080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837080 prefixEnd_3837080 := by exact prefixLift 3837080
  have htrace : WordTrace (prefixWord ++ tailWord_3837080) baseStart_3837080 baseEnd_3837080 := by
    simpa [prefixWord, tailWord_3837080, baseEnd_3837080] using wordTrace_append hprefix tailTrace_3837080
  have hstable : (prefixWord ++ tailWord_3837080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837080).length < 2 ^ (prefixWord ++ tailWord_3837080).sum := by decide
  have hdescent : baseEnd_3837080 < baseStart_3837080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837095 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3837095 : Nat := 118140960795 + 3837095 * 2 ^ 59
def prefixEnd_3837095 : Nat := 4983230072969 + 3 ^ 40 * 3837095 * 2
def baseEnd_3837095 : Nat := 1313516034642513387910685

theorem tailTrace_3837095 : CollatzResearch.WordTrace tailWord_3837095 prefixEnd_3837095 1313516034642513387910685 := by
  unfold tailWord_3837095
  simp only [CollatzResearch.WordTrace]
  refine ⟨139950352033867613498128739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93300234689245075665419159 139950352033867613498128739)
  ·
    refine ⟨209925528050801420247193109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139950352033867613498128739 209925528050801420247193109)
    ·
      refine ⟨9840259127381316574087177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209925528050801420247193109 9840259127381316574087177)
      ·
        refine ⟨7380194345535987430565383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9840259127381316574087177 7380194345535987430565383)
        ·
          refine ⟨11070291518303981145848075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380194345535987430565383 11070291518303981145848075)
          ·
            refine ⟨16605437277455971718772113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11070291518303981145848075 16605437277455971718772113)
            ·
              refine ⟨12454077958091978789079085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16605437277455971718772113 12454077958091978789079085)
              ·
                refine ⟨4670279234284492045904657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12454077958091978789079085 4670279234284492045904657)
                ·
                  refine ⟨3502709425713369034428493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4670279234284492045904657 3502709425713369034428493)
                  ·
                    refine ⟨1313516034642513387910685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3502709425713369034428493 1313516034642513387910685)
                    ·
                      rfl

theorem cell22_3837095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3837095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837095 prefixEnd_3837095 := by exact prefixLift 3837095
  have htrace : WordTrace (prefixWord ++ tailWord_3837095) baseStart_3837095 baseEnd_3837095 := by
    simpa [prefixWord, tailWord_3837095, baseEnd_3837095] using wordTrace_append hprefix tailTrace_3837095
  have hstable : (prefixWord ++ tailWord_3837095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837095).length < 2 ^ (prefixWord ++ tailWord_3837095).sum := by decide
  have hdescent : baseEnd_3837095 < baseStart_3837095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837151 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 2, 5]
def baseStart_3837151 : Nat := 118140960795 + 3837151 * 2 ^ 59
def prefixEnd_3837151 : Nat := 4983230072969 + 3 ^ 40 * 3837151 * 2
def baseEnd_3837151 : Nat := 1313535204586947908510513

theorem tailTrace_3837151 : CollatzResearch.WordTrace tailWord_3837151 prefixEnd_3837151 1313535204586947908510513 := by
  unfold tailWord_3837151
  simp only [CollatzResearch.WordTrace]
  refine ⟨139952394521664735062167307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93301596347776490041444871 139952394521664735062167307)
  ·
    refine ⟨209928591782497102593250961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139952394521664735062167307 209928591782497102593250961)
    ·
      refine ⟨157446443836872826944938221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209928591782497102593250961 157446443836872826944938221)
      ·
        refine ⟨59042416438827310104351833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157446443836872826944938221 59042416438827310104351833)
        ·
          refine ⟨44281812329120482578263875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59042416438827310104351833 44281812329120482578263875)
          ·
            refine ⟨66422718493680723867395813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44281812329120482578263875 66422718493680723867395813)
            ·
              refine ⟨12454259717565135725136715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66422718493680723867395813 12454259717565135725136715)
              ·
                refine ⟨18681389576347703587705073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12454259717565135725136715 18681389576347703587705073)
                ·
                  refine ⟨14011042182260777690778805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18681389576347703587705073 14011042182260777690778805)
                  ·
                    refine ⟨1313535204586947908510513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14011042182260777690778805 1313535204586947908510513)
                    ·
                      rfl

theorem cell22_3837151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_3837151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837151 prefixEnd_3837151 := by exact prefixLift 3837151
  have htrace : WordTrace (prefixWord ++ tailWord_3837151) baseStart_3837151 baseEnd_3837151 := by
    simpa [prefixWord, tailWord_3837151, baseEnd_3837151] using wordTrace_append hprefix tailTrace_3837151
  have hstable : (prefixWord ++ tailWord_3837151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837151).length < 2 ^ (prefixWord ++ tailWord_3837151).sum := by decide
  have hdescent : baseEnd_3837151 < baseStart_3837151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837183 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 1, 4]
def baseStart_3837183 : Nat := 118140960795 + 3837183 * 2 ^ 59
def prefixEnd_3837183 : Nat := 4983230072969 + 3 ^ 40 * 3837183 * 2
def baseEnd_3837183 : Nat := 1313546158840910491710415

theorem tailTrace_3837183 : CollatzResearch.WordTrace tailWord_3837183 prefixEnd_3837183 1313546158840910491710415 := by
  unfold tailWord_3837183
  simp only [CollatzResearch.WordTrace]
  refine ⟨139953561657548804527332203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93302374438365869684888135 139953561657548804527332203)
  ·
    refine ⟨209930342486323206790998305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139953561657548804527332203 209930342486323206790998305)
    ·
      refine ⟨157447756864742405093248729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209930342486323206790998305 157447756864742405093248729)
      ·
        refine ⟨118085817648556803819936547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157447756864742405093248729 118085817648556803819936547)
        ·
          refine ⟨177128726472835205729904821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118085817648556803819936547 177128726472835205729904821)
          ·
            refine ⟨16605818106828300537178577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177128726472835205729904821 16605818106828300537178577)
            ·
              refine ⟨12454363580121225402883933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16605818106828300537178577 12454363580121225402883933)
              ·
                refine ⟨4670386342545459526081475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12454363580121225402883933 4670386342545459526081475)
                ·
                  refine ⟨7005579513818189289122213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670386342545459526081475 7005579513818189289122213)
                  ·
                    refine ⟨1313546158840910491710415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7005579513818189289122213 1313546158840910491710415)
                    ·
                      rfl

theorem cell22_3837183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_3837183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837183 prefixEnd_3837183 := by exact prefixLift 3837183
  have htrace : WordTrace (prefixWord ++ tailWord_3837183) baseStart_3837183 baseEnd_3837183 := by
    simpa [prefixWord, tailWord_3837183, baseEnd_3837183] using wordTrace_append hprefix tailTrace_3837183
  have hstable : (prefixWord ++ tailWord_3837183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837183).length < 2 ^ (prefixWord ++ tailWord_3837183).sum := by decide
  have hdescent : baseEnd_3837183 < baseStart_3837183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837198 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_3837198 : Nat := 118140960795 + 3837198 * 2 ^ 59
def prefixEnd_3837198 : Nat := 4983230072969 + 3 ^ 40 * 3837198 * 2
def baseEnd_3837198 : Nat := 437850431215818484195123

theorem tailTrace_3837198 : CollatzResearch.WordTrace tailWord_3837198 prefixEnd_3837198 437850431215818484195123 := by
  unfold tailWord_3837198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17494263594061807761141031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93302739168329641392752165 17494263594061807761141031)
  ·
    refine ⟨26241395391092711641711547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17494263594061807761141031 26241395391092711641711547)
    ·
      refine ⟨39362093086639067462567321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26241395391092711641711547 39362093086639067462567321)
      ·
        refine ⟨29521569814979300596925491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39362093086639067462567321 29521569814979300596925491)
        ·
          refine ⟨44282354722468950895388237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29521569814979300596925491 44282354722468950895388237)
          ·
            refine ⟨16605883020925856585770589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44282354722468950895388237 16605883020925856585770589)
            ·
              refine ⟨6227206132847196219663971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16605883020925856585770589 6227206132847196219663971)
              ·
                refine ⟨9340809199270794329495957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227206132847196219663971 9340809199270794329495957)
                ·
                  refine ⟨437850431215818484195123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9340809199270794329495957 437850431215818484195123)
                  ·
                    rfl

theorem cell22_3837198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_3837198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837198 prefixEnd_3837198 := by exact prefixLift 3837198
  have htrace : WordTrace (prefixWord ++ tailWord_3837198) baseStart_3837198 baseEnd_3837198 := by
    simpa [prefixWord, tailWord_3837198, baseEnd_3837198] using wordTrace_append hprefix tailTrace_3837198
  have hstable : (prefixWord ++ tailWord_3837198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837198).length < 2 ^ (prefixWord ++ tailWord_3837198).sum := by decide
  have hdescent : baseEnd_3837198 < baseStart_3837198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837211 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 6, 4]
def baseStart_3837211 : Nat := 118140960795 + 3837211 * 2 ^ 59
def prefixEnd_3837211 : Nat := 4983230072969 + 3 ^ 40 * 3837211 * 2
def baseEnd_3837211 : Nat := 1313555743813127752010329

theorem tailTrace_3837211 : CollatzResearch.WordTrace tailWord_3837211 prefixEnd_3837211 1313555743813127752010329 := by
  unfold tailWord_3837211
  simp only [CollatzResearch.WordTrace]
  refine ⟨139954582901447365309351487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93303055267631576872900991 139954582901447365309351487)
  ·
    refine ⟨209931874352171047964027231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139954582901447365309351487 209931874352171047964027231)
    ·
      refine ⟨314897811528256571946040847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209931874352171047964027231 314897811528256571946040847)
      ·
        refine ⟨472346717292384857919061271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314897811528256571946040847 472346717292384857919061271)
        ·
          refine ⟨708520075938577286878591907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472346717292384857919061271 708520075938577286878591907)
          ·
            refine ⟨1062780113907865930317887861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708520075938577286878591907 1062780113907865930317887861)
            ·
              refine ⟨99635635678862430967301987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1062780113907865930317887861 99635635678862430967301987)
              ·
                refine ⟨149453453518293646450952981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99635635678862430967301987 149453453518293646450952981)
                ·
                  refine ⟨7005630633670014677388421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149453453518293646450952981 7005630633670014677388421)
                  ·
                    refine ⟨1313555743813127752010329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7005630633670014677388421 1313555743813127752010329)
                    ·
                      rfl

theorem cell22_3837211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 4].length) (baseStart_3837211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837211 prefixEnd_3837211 := by exact prefixLift 3837211
  have htrace : WordTrace (prefixWord ++ tailWord_3837211) baseStart_3837211 baseEnd_3837211 := by
    simpa [prefixWord, tailWord_3837211, baseEnd_3837211] using wordTrace_append hprefix tailTrace_3837211
  have hstable : (prefixWord ++ tailWord_3837211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837211).length < 2 ^ (prefixWord ++ tailWord_3837211).sum := by decide
  have hdescent : baseEnd_3837211 < baseStart_3837211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837249 : List Nat := [1, 2, 5, 2, 1, 3, 2, 2, 4]
def baseStart_3837249 : Nat := 118140960795 + 3837249 * 2 ^ 59
def prefixEnd_3837249 : Nat := 4983230072969 + 3 ^ 40 * 3837249 * 2
def baseEnd_3837249 : Nat := 437856250663236106520071

theorem tailTrace_3837249 : CollatzResearch.WordTrace tailWord_3837249 prefixEnd_3837249 437856250663236106520071 := by
  unfold tailWord_3837249
  simp only [CollatzResearch.WordTrace]
  refine ⟨139955968875309697799234801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93303979250206465199489867 139955968875309697799234801)
  ·
    refine ⟨104966976656482273349426101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139955968875309697799234801 104966976656482273349426101)
    ·
      refine ⟨9840654061545213126508697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104966976656482273349426101 9840654061545213126508697)
      ·
        refine ⟨7380490546158909844881523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9840654061545213126508697 7380490546158909844881523)
        ·
          refine ⟨11070735819238364767322285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380490546158909844881523 11070735819238364767322285)
          ·
            refine ⟨4151525932214386787745857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11070735819238364767322285 4151525932214386787745857)
            ·
              refine ⟨3113644449160790090809393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4151525932214386787745857 3113644449160790090809393)
              ·
                refine ⟨2335233336870592568107045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3113644449160790090809393 2335233336870592568107045)
                ·
                  refine ⟨437856250663236106520071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335233336870592568107045 437856250663236106520071)
                  ·
                    rfl

theorem cell22_3837249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 4].length) (baseStart_3837249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837249 prefixEnd_3837249 := by exact prefixLift 3837249
  have htrace : WordTrace (prefixWord ++ tailWord_3837249) baseStart_3837249 baseEnd_3837249 := by
    simpa [prefixWord, tailWord_3837249, baseEnd_3837249] using wordTrace_append hprefix tailTrace_3837249
  have hstable : (prefixWord ++ tailWord_3837249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837249).length < 2 ^ (prefixWord ++ tailWord_3837249).sum := by decide
  have hdescent : baseEnd_3837249 < baseStart_3837249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837258 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 7, 3]
def baseStart_3837258 : Nat := 118140960795 + 3837258 * 2 ^ 59
def prefixEnd_3837258 : Nat := 4983230072969 + 3 ^ 40 * 3837258 * 2
def baseEnd_3837258 : Nat := 1313571832873635296085185

theorem tailTrace_3837258 : CollatzResearch.WordTrace tailWord_3837258 prefixEnd_3837258 1313571832873635296085185 := by
  unfold tailWord_3837258
  simp only [CollatzResearch.WordTrace]
  refine ⟨34989074283069273084078107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93304198088184728224208285 34989074283069273084078107)
  ·
    refine ⟨52483611424603909626117161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34989074283069273084078107 52483611424603909626117161)
    ·
      refine ⟨39362708568452932219587871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52483611424603909626117161 39362708568452932219587871)
      ·
        refine ⟨59044062852679398329381807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39362708568452932219587871 59044062852679398329381807)
        ·
          refine ⟨88566094279019097494072711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59044062852679398329381807 88566094279019097494072711)
          ·
            refine ⟨132849141418528646241109067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88566094279019097494072711 132849141418528646241109067)
            ·
              refine ⟨199273712127792969361663601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132849141418528646241109067 199273712127792969361663601)
              ·
                refine ⟨149455284095844727021247701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199273712127792969361663601 149455284095844727021247701)
                ·
                  refine ⟨3502858220996360789560493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 149455284095844727021247701 3502858220996360789560493)
                  ·
                    refine ⟨1313571832873635296085185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3502858220996360789560493 1313571832873635296085185)
                    ·
                      rfl

theorem cell22_3837258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_3837258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837258 prefixEnd_3837258 := by exact prefixLift 3837258
  have htrace : WordTrace (prefixWord ++ tailWord_3837258) baseStart_3837258 baseEnd_3837258 := by
    simpa [prefixWord, tailWord_3837258, baseEnd_3837258] using wordTrace_append hprefix tailTrace_3837258
  have hstable : (prefixWord ++ tailWord_3837258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837258).length < 2 ^ (prefixWord ++ tailWord_3837258).sum := by decide
  have hdescent : baseEnd_3837258 < baseStart_3837258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837292 : List Nat := [2, 2, 1, 1, 5, 1, 1, 5, 1, 3]
def baseStart_3837292 : Nat := 118140960795 + 3837292 * 2 ^ 59
def prefixEnd_3837292 : Nat := 4983230072969 + 3 ^ 40 * 3837292 * 2
def baseEnd_3837292 : Nat := 1313583471768470540735081

theorem tailTrace_3837292 : CollatzResearch.WordTrace tailWord_3837292 prefixEnd_3837292 1313583471768470540735081 := by
  unfold tailWord_3837292
  simp only [CollatzResearch.WordTrace]
  refine ⟨69978768607076958071525065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93305024809435944095366753 69978768607076958071525065)
  ·
    refine ⟨52484076455307718553643799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69978768607076958071525065 52484076455307718553643799)
    ·
      refine ⟨78726114682961577830465699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52484076455307718553643799 78726114682961577830465699)
      ·
        refine ⟨118089172024442366745698549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78726114682961577830465699 118089172024442366745698549)
        ·
          refine ⟨11070859877291471882409239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118089172024442366745698549 11070859877291471882409239)
          ·
            refine ⟨16606289815937207823613859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11070859877291471882409239 16606289815937207823613859)
            ·
              refine ⟨24909434723905811735420789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16606289815937207823613859 24909434723905811735420789)
              ·
                refine ⟨2335259505366169850195699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24909434723905811735420789 2335259505366169850195699)
                ·
                  refine ⟨3502889258049254775293549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335259505366169850195699 3502889258049254775293549)
                  ·
                    refine ⟨1313583471768470540735081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3502889258049254775293549 1313583471768470540735081)
                    ·
                      rfl

theorem cell22_3837292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_3837292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837292 prefixEnd_3837292 := by exact prefixLift 3837292
  have htrace : WordTrace (prefixWord ++ tailWord_3837292) baseStart_3837292 baseEnd_3837292 := by
    simpa [prefixWord, tailWord_3837292, baseEnd_3837292] using wordTrace_append hprefix tailTrace_3837292
  have hstable : (prefixWord ++ tailWord_3837292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837292).length < 2 ^ (prefixWord ++ tailWord_3837292).sum := by decide
  have hdescent : baseEnd_3837292 < baseStart_3837292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837333 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 6]
def baseStart_3837333 : Nat := 118140960795 + 3837333 * 2 ^ 59
def prefixEnd_3837333 : Nat := 4983230072969 + 3 ^ 40 * 3837333 * 2
def baseEnd_3837333 : Nat := 437865835635453366819985

theorem tailTrace_3837333 : CollatzResearch.WordTrace tailWord_3837333 prefixEnd_3837333 437865835635453366819985 := by
  unfold tailWord_3837333
  simp only [CollatzResearch.WordTrace]
  refine ⟨139959032607005380145292653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93306021738003586763528435 139959032607005380145292653)
  ·
    refine ⟨52484637227627017554484745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139959032607005380145292653 52484637227627017554484745)
    ·
      refine ⟨39363477920720263165863559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52484637227627017554484745 39363477920720263165863559)
      ·
        refine ⟨59045216881080394748795339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39363477920720263165863559 59045216881080394748795339)
        ·
          refine ⟨88567825321620592123193009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59045216881080394748795339 88567825321620592123193009)
          ·
            refine ⟨66425868991215444092394757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88567825321620592123193009 66425868991215444092394757)
            ·
              refine ⟨12454850435852895767324017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66425868991215444092394757 12454850435852895767324017)
              ·
                refine ⟨9341137826889671825493013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12454850435852895767324017 9341137826889671825493013)
                ·
                  refine ⟨437865835635453366819985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9341137826889671825493013 437865835635453366819985)
                  ·
                    rfl

theorem cell22_3837333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_3837333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837333 prefixEnd_3837333 := by exact prefixLift 3837333
  have htrace : WordTrace (prefixWord ++ tailWord_3837333) baseStart_3837333 baseEnd_3837333 := by
    simpa [prefixWord, tailWord_3837333, baseEnd_3837333] using wordTrace_append hprefix tailTrace_3837333
  have hstable : (prefixWord ++ tailWord_3837333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837333).length < 2 ^ (prefixWord ++ tailWord_3837333).sum := by decide
  have hdescent : baseEnd_3837333 < baseStart_3837333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837348 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_3837348 : Nat := 118140960795 + 3837348 * 2 ^ 59
def prefixEnd_3837348 : Nat := 4983230072969 + 3 ^ 40 * 3837348 * 2
def baseEnd_3837348 : Nat := 1313602641712905061334909

theorem tailTrace_3837348 : CollatzResearch.WordTrace tailWord_3837348 prefixEnd_3837348 1313602641712905061334909 := by
  unfold tailWord_3837348
  simp only [CollatzResearch.WordTrace]
  refine ⟨69979789850975518853544349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93306386467967358471392465 69979789850975518853544349)
  ·
    refine ⟨26242421194115819570079131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69979789850975518853544349 26242421194115819570079131)
    ·
      refine ⟨39363631791173729355118697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26242421194115819570079131 39363631791173729355118697)
      ·
        refine ⟨29522723843380297016339023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39363631791173729355118697 29522723843380297016339023)
        ·
          refine ⟨44284085765070445524508535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29522723843380297016339023 44284085765070445524508535)
          ·
            refine ⟨66426128647605668286762803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44284085765070445524508535 66426128647605668286762803)
            ·
              refine ⟨99639192971408502430144205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66426128647605668286762803 99639192971408502430144205)
              ·
                refine ⟨37364697364278188411304077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99639192971408502430144205 37364697364278188411304077)
                ·
                  refine ⟨14011761511604320654239029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37364697364278188411304077 14011761511604320654239029)
                  ·
                    refine ⟨1313602641712905061334909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14011761511604320654239029 1313602641712905061334909)
                    ·
                      rfl

theorem cell22_3837348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_3837348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837348 prefixEnd_3837348 := by exact prefixLift 3837348
  have htrace : WordTrace (prefixWord ++ tailWord_3837348) baseStart_3837348 baseEnd_3837348 := by
    simpa [prefixWord, tailWord_3837348, baseEnd_3837348] using wordTrace_append hprefix tailTrace_3837348
  have hstable : (prefixWord ++ tailWord_3837348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837348).length < 2 ^ (prefixWord ++ tailWord_3837348).sum := by decide
  have hdescent : baseEnd_3837348 < baseStart_3837348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837367 : List Nat := [1, 1, 3, 1, 3, 2, 5, 2, 4]
def baseStart_3837367 : Nat := 118140960795 + 3837367 * 2 ^ 59
def prefixEnd_3837367 : Nat := 4983230072969 + 3 ^ 40 * 3837367 * 2
def baseEnd_3837367 : Nat := 437869715267065115036617

theorem tailTrace_3837367 : CollatzResearch.WordTrace tailWord_3837367 prefixEnd_3837367 437869715267065115036617 := by
  unfold tailWord_3837367
  simp only [CollatzResearch.WordTrace]
  refine ⟨139960272688882203952030355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93306848459254802634686903 139960272688882203952030355)
  ·
    refine ⟨209940409033323305928045533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139960272688882203952030355 209940409033323305928045533)
    ·
      refine ⟨78727653387496239723017075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209940409033323305928045533 78727653387496239723017075)
      ·
        refine ⟨118091480081244359584525613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78727653387496239723017075 118091480081244359584525613)
        ·
          refine ⟨44284305030466634844197105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118091480081244359584525613 44284305030466634844197105)
          ·
            refine ⟨33213228772849976133147829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44284305030466634844197105 33213228772849976133147829)
            ·
              refine ⟨3113740197454685262482609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33213228772849976133147829 3113740197454685262482609)
              ·
                refine ⟨2335305148091013946861957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3113740197454685262482609 2335305148091013946861957)
                ·
                  refine ⟨437869715267065115036617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335305148091013946861957 437869715267065115036617)
                  ·
                    rfl

theorem cell22_3837367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 4].length) (baseStart_3837367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837367 prefixEnd_3837367 := by exact prefixLift 3837367
  have htrace : WordTrace (prefixWord ++ tailWord_3837367) baseStart_3837367 baseEnd_3837367 := by
    simpa [prefixWord, tailWord_3837367, baseEnd_3837367] using wordTrace_append hprefix tailTrace_3837367
  have hstable : (prefixWord ++ tailWord_3837367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837367).length < 2 ^ (prefixWord ++ tailWord_3837367).sum := by decide
  have hdescent : baseEnd_3837367 < baseStart_3837367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837423 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 7]
def baseStart_3837423 : Nat := 118140960795 + 3837423 * 2 ^ 59
def prefixEnd_3837423 : Nat := 4983230072969 + 3 ^ 40 * 3837423 * 2
def baseEnd_3837423 : Nat := 437876105248543288569893

theorem tailTrace_3837423 : CollatzResearch.WordTrace tailWord_3837423 prefixEnd_3837423 437876105248543288569893 := by
  unfold tailWord_3837423
  simp only [CollatzResearch.WordTrace]
  refine ⟨139962315176679325516068923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93308210117786217010712615 139962315176679325516068923)
  ·
    refine ⟨209943472765018988274103385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139962315176679325516068923 209943472765018988274103385)
    ·
      refine ⟨157457604573764241205577539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209943472765018988274103385 157457604573764241205577539)
      ·
        refine ⟨236186406860646361808366309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157457604573764241205577539 236186406860646361808366309)
        ·
          refine ⟨44284951286371192839068683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236186406860646361808366309 44284951286371192839068683)
          ·
            refine ⟨66427426929556789258603025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44284951286371192839068683 66427426929556789258603025)
            ·
              refine ⟨49820570197167591943952269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66427426929556789258603025 49820570197167591943952269)
              ·
                refine ⟨18682713823937846978982101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49820570197167591943952269 18682713823937846978982101)
                ·
                  refine ⟨437876105248543288569893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18682713823937846978982101 437876105248543288569893)
                  ·
                    rfl

theorem cell22_3837423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 7].length) (baseStart_3837423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837423 prefixEnd_3837423 := by exact prefixLift 3837423
  have htrace : WordTrace (prefixWord ++ tailWord_3837423) baseStart_3837423 baseEnd_3837423 := by
    simpa [prefixWord, tailWord_3837423, baseEnd_3837423] using wordTrace_append hprefix tailTrace_3837423
  have hstable : (prefixWord ++ tailWord_3837423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837423).length < 2 ^ (prefixWord ++ tailWord_3837423).sum := by decide
  have hdescent : baseEnd_3837423 < baseStart_3837423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837444 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_3837444 : Nat := 118140960795 + 3837444 * 2 ^ 59
def prefixEnd_3837444 : Nat := 4983230072969 + 3 ^ 40 * 3837444 * 2
def baseEnd_3837444 : Nat := 1313635504474792810934615

theorem tailTrace_3837444 : CollatzResearch.WordTrace tailWord_3837444 prefixEnd_3837444 1313635504474792810934615 := by
  unfold tailWord_3837444
  simp only [CollatzResearch.WordTrace]
  refine ⟨69981540554801623051291693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93308720739735497401722257 69981540554801623051291693)
  ·
    refine ⟨26243077708050608644234385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69981540554801623051291693 26243077708050608644234385)
    ·
      refine ⟨19682308281037956483175789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26243077708050608644234385 19682308281037956483175789)
      ·
        refine ⟨7380865605389233681190921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19682308281037956483175789 7380865605389233681190921)
        ·
          refine ⟨5535649204041925260893191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7380865605389233681190921 5535649204041925260893191)
          ·
            refine ⟨8303473806062887891339787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535649204041925260893191 8303473806062887891339787)
            ·
              refine ⟨12455210709094331837009681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303473806062887891339787 12455210709094331837009681)
              ·
                refine ⟨9341408031820748877757261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12455210709094331837009681 9341408031820748877757261)
                ·
                  refine ⟨3503028011932780829158973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9341408031820748877757261 3503028011932780829158973)
                  ·
                    refine ⟨1313635504474792810934615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3503028011932780829158973 1313635504474792810934615)
                    ·
                      rfl

theorem cell22_3837444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_3837444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837444 prefixEnd_3837444 := by exact prefixLift 3837444
  have htrace : WordTrace (prefixWord ++ tailWord_3837444) baseStart_3837444 baseEnd_3837444 := by
    simpa [prefixWord, tailWord_3837444, baseEnd_3837444] using wordTrace_append hprefix tailTrace_3837444
  have hstable : (prefixWord ++ tailWord_3837444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837444).length < 2 ^ (prefixWord ++ tailWord_3837444).sum := by decide
  have hdescent : baseEnd_3837444 < baseStart_3837444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837483 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 2, 9]
def baseStart_3837483 : Nat := 118140960795 + 3837483 * 2 ^ 59
def prefixEnd_3837483 : Nat := 4983230072969 + 3 ^ 40 * 3837483 * 2
def baseEnd_3837483 : Nat := 1313648854971809709209495

theorem tailTrace_3837483 : CollatzResearch.WordTrace tailWord_3837483 prefixEnd_3837483 1313648854971809709209495 := by
  unfold tailWord_3837483
  simp only [CollatzResearch.WordTrace]
  refine ⟨139964503556461955763253103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93309669037641303842168735 139964503556461955763253103)
  ·
    refine ⟨209946755334692933644879655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139964503556461955763253103 209946755334692933644879655)
    ·
      refine ⟨314920133002039400467319483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209946755334692933644879655 314920133002039400467319483)
      ·
        refine ⟨472380199503059100700979225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314920133002039400467319483 472380199503059100700979225)
        ·
          refine ⟨354285149627294325525734419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472380199503059100700979225 354285149627294325525734419)
          ·
            refine ⟨531427724440941488288601629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354285149627294325525734419 531427724440941488288601629)
            ·
              refine ⟨199285396665353058108225611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531427724440941488288601629 199285396665353058108225611)
              ·
                refine ⟨298928094998029587162338417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199285396665353058108225611 298928094998029587162338417)
                ·
                  refine ⟨224196071248522190371753813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298928094998029587162338417 224196071248522190371753813)
                  ·
                    refine ⟨1313648854971809709209495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 224196071248522190371753813 1313648854971809709209495)
                    ·
                      rfl

theorem cell22_3837483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_3837483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837483 prefixEnd_3837483 := by exact prefixLift 3837483
  have htrace : WordTrace (prefixWord ++ tailWord_3837483) baseStart_3837483 baseEnd_3837483 := by
    simpa [prefixWord, tailWord_3837483, baseEnd_3837483] using wordTrace_append hprefix tailTrace_3837483
  have hstable : (prefixWord ++ tailWord_3837483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837483).length < 2 ^ (prefixWord ++ tailWord_3837483).sum := by decide
  have hdescent : baseEnd_3837483 < baseStart_3837483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837515 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 2, 4]
def baseStart_3837515 : Nat := 118140960795 + 3837515 * 2 ^ 59
def prefixEnd_3837515 : Nat := 4983230072969 + 3 ^ 40 * 3837515 * 2
def baseEnd_3837515 : Nat := 1313659809225772292409397

theorem tailTrace_3837515 : CollatzResearch.WordTrace tailWord_3837515 prefixEnd_3837515 1313659809225772292409397 := by
  unfold tailWord_3837515
  simp only [CollatzResearch.WordTrace]
  refine ⟨139965670692346025228417999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93310447128230683485611999 139965670692346025228417999)
  ·
    refine ⟨209948506038519037842626999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139965670692346025228417999 209948506038519037842626999)
    ·
      refine ⟨314922759057778556763940499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209948506038519037842626999 314922759057778556763940499)
      ·
        refine ⟨472384138586667835145910749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314922759057778556763940499 472384138586667835145910749)
        ·
          refine ⟨177144051970000438179716531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472384138586667835145910749 177144051970000438179716531)
          ·
            refine ⟨265716077955000657269574797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177144051970000438179716531 265716077955000657269574797)
            ·
              refine ⟨99643529233125246476090549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265716077955000657269574797 99643529233125246476090549)
              ·
                refine ⟨9341580865605491857133489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99643529233125246476090549 9341580865605491857133489)
                ·
                  refine ⟨7006185649204118892850117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9341580865605491857133489 7006185649204118892850117)
                  ·
                    refine ⟨1313659809225772292409397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7006185649204118892850117 1313659809225772292409397)
                    ·
                      rfl

theorem cell22_3837515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 4].length) (baseStart_3837515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837515 prefixEnd_3837515 := by exact prefixLift 3837515
  have htrace : WordTrace (prefixWord ++ tailWord_3837515) baseStart_3837515 baseEnd_3837515 := by
    simpa [prefixWord, tailWord_3837515, baseEnd_3837515] using wordTrace_append hprefix tailTrace_3837515
  have hstable : (prefixWord ++ tailWord_3837515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837515).length < 2 ^ (prefixWord ++ tailWord_3837515).sum := by decide
  have hdescent : baseEnd_3837515 < baseStart_3837515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837532 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3837532 : Nat := 118140960795 + 3837532 * 2 ^ 59
def prefixEnd_3837532 : Nat := 4983230072969 + 3 ^ 40 * 3837532 * 2
def baseEnd_3837532 : Nat := 1313665628673189914734345

theorem tailTrace_3837532 : CollatzResearch.WordTrace tailWord_3837532 prefixEnd_3837532 1313665628673189914734345 := by
  unfold tailWord_3837532
  simp only [CollatzResearch.WordTrace]
  refine ⟨69983145366642218565893425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93310860488856291421191233 69983145366642218565893425)
  ·
    refine ⟨52487359024981663924420069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69983145366642218565893425 52487359024981663924420069)
    ·
      refine ⟨9841379817184061985828763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52487359024981663924420069 9841379817184061985828763)
      ·
        refine ⟨14762069725776092978743145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9841379817184061985828763 14762069725776092978743145)
        ·
          refine ⟨11071552294332069734057359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14762069725776092978743145 11071552294332069734057359)
          ·
            refine ⟨16607328441498104601086039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11071552294332069734057359 16607328441498104601086039)
            ·
              refine ⟨24910992662247156901629059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16607328441498104601086039 24910992662247156901629059)
              ·
                refine ⟨37366488993370735352443589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24910992662247156901629059 37366488993370735352443589)
                ·
                  refine ⟨7006216686257012878583173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37366488993370735352443589 7006216686257012878583173)
                  ·
                    refine ⟨1313665628673189914734345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7006216686257012878583173 1313665628673189914734345)
                    ·
                      rfl

theorem cell22_3837532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3837532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837532 prefixEnd_3837532 := by exact prefixLift 3837532
  have htrace : WordTrace (prefixWord ++ tailWord_3837532) baseStart_3837532 baseEnd_3837532 := by
    simpa [prefixWord, tailWord_3837532, baseEnd_3837532] using wordTrace_append hprefix tailTrace_3837532
  have hstable : (prefixWord ++ tailWord_3837532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837532).length < 2 ^ (prefixWord ++ tailWord_3837532).sum := by decide
  have hdescent : baseEnd_3837532 < baseStart_3837532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837579 : List Nat := [1, 1, 1, 1, 4, 1, 4, 5, 1, 3]
def baseStart_3837579 : Nat := 118140960795 + 3837579 * 2 ^ 59
def prefixEnd_3837579 : Nat := 4983230072969 + 3 ^ 40 * 3837579 * 2
def baseEnd_3837579 : Nat := 1313681717733697458809201

theorem tailTrace_3837579 : CollatzResearch.WordTrace tailWord_3837579 prefixEnd_3837579 1313681717733697458809201 := by
  unfold tailWord_3837579
  simp only [CollatzResearch.WordTrace]
  refine ⟨139968004964114164158747791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93312003309409442772498527 139968004964114164158747791)
  ·
    refine ⟨209952007446171246238121687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139968004964114164158747791 209952007446171246238121687)
    ·
      refine ⟨314928011169256869357182531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209952007446171246238121687 314928011169256869357182531)
      ·
        refine ⟨472392016753885304035773797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314928011169256869357182531 472392016753885304035773797)
        ·
          refine ⟨88573503141353494506707587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472392016753885304035773797 88573503141353494506707587)
          ·
            refine ⟨132860254712030241760061381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88573503141353494506707587 132860254712030241760061381)
            ·
              refine ⟨24911297758505670330011509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132860254712030241760061381 24911297758505670330011509)
              ·
                refine ⟨2335434164859906593438579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24911297758505670330011509 2335434164859906593438579)
                ·
                  refine ⟨3503151247289859890157869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335434164859906593438579 3503151247289859890157869)
                  ·
                    refine ⟨1313681717733697458809201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3503151247289859890157869 1313681717733697458809201)
                    ·
                      rfl

theorem cell22_3837579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 1, 3].length) (baseStart_3837579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837579 prefixEnd_3837579 := by exact prefixLift 3837579
  have htrace : WordTrace (prefixWord ++ tailWord_3837579) baseStart_3837579 baseEnd_3837579 := by
    simpa [prefixWord, tailWord_3837579, baseEnd_3837579] using wordTrace_append hprefix tailTrace_3837579
  have hstable : (prefixWord ++ tailWord_3837579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837579).length < 2 ^ (prefixWord ++ tailWord_3837579).sum := by decide
  have hdescent : baseEnd_3837579 < baseStart_3837579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837592 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 5]
def baseStart_3837592 : Nat := 118140960795 + 3837592 * 2 ^ 59
def prefixEnd_3837592 : Nat := 4983230072969 + 3 ^ 40 * 3837592 * 2
def baseEnd_3837592 : Nat := 437895389299789919411387

theorem tailTrace_3837592 : CollatzResearch.WordTrace tailWord_3837592 prefixEnd_3837592 437895389299789919411387 := by
  unfold tailWord_3837592
  simp only [CollatzResearch.WordTrace]
  refine ⟨69984239556533533689485515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93312319408711378252647353 69984239556533533689485515)
  ·
    refine ⟨104976359334800300534228273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69984239556533533689485515 104976359334800300534228273)
    ·
      refine ⟨78732269501100225400671205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104976359334800300534228273 78732269501100225400671205)
      ·
        refine ⟨14762300531456292262625851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78732269501100225400671205 14762300531456292262625851)
        ·
          refine ⟨22143450797184438393938777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14762300531456292262625851 22143450797184438393938777)
          ·
            refine ⟨16607588097888328795454083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22143450797184438393938777 16607588097888328795454083)
            ·
              refine ⟨24911382146832493193181125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16607588097888328795454083 24911382146832493193181125)
              ·
                refine ⟨4670884152531092473721461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24911382146832493193181125 4670884152531092473721461)
                ·
                  refine ⟨437895389299789919411387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4670884152531092473721461 437895389299789919411387)
                  ·
                    rfl

theorem cell22_3837592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_3837592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837592 prefixEnd_3837592 := by exact prefixLift 3837592
  have htrace : WordTrace (prefixWord ++ tailWord_3837592) baseStart_3837592 baseEnd_3837592 := by
    simpa [prefixWord, tailWord_3837592, baseEnd_3837592] using wordTrace_append hprefix tailTrace_3837592
  have hstable : (prefixWord ++ tailWord_3837592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837592).length < 2 ^ (prefixWord ++ tailWord_3837592).sum := by decide
  have hdescent : baseEnd_3837592 < baseStart_3837592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837682 : List Nat := [3, 2, 1, 3, 1, 1, 3, 8]
def baseStart_3837682 : Nat := 118140960795 + 3837682 * 2 ^ 59
def prefixEnd_3837682 : Nat := 4983230072969 + 3 ^ 40 * 3837682 * 2
def baseEnd_3837682 : Nat := 145968552970959947053765

theorem tailTrace_3837682 : CollatzResearch.WordTrace tailWord_3837682 prefixEnd_3837682 145968552970959947053765 := by
  unfold tailWord_3837682
  simp only [CollatzResearch.WordTrace]
  refine ⟨34992940420685253187436825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93314507788494008499831533 34992940420685253187436825)
  ·
    refine ⟨26244705315513939890577619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34992940420685253187436825 26244705315513939890577619)
    ·
      refine ⟨39367057973270909835866429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26244705315513939890577619 39367057973270909835866429)
      ·
        refine ⟨14762646739976591188449911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39367057973270909835866429 14762646739976591188449911)
        ·
          refine ⟨22143970109964886782674867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14762646739976591188449911 22143970109964886782674867)
          ·
            refine ⟨33215955164947330174012301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22143970109964886782674867 33215955164947330174012301)
            ·
              refine ⟨12455983186855248815254613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33215955164947330174012301 12455983186855248815254613)
              ·
                refine ⟨145968552970959947053765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12455983186855248815254613 145968552970959947053765)
                ·
                  rfl

theorem cell22_3837682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_3837682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837682 prefixEnd_3837682 := by exact prefixLift 3837682
  have htrace : WordTrace (prefixWord ++ tailWord_3837682) baseStart_3837682 baseEnd_3837682 := by
    simpa [prefixWord, tailWord_3837682, baseEnd_3837682] using wordTrace_append hprefix tailTrace_3837682
  have hstable : (prefixWord ++ tailWord_3837682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837682).length < 2 ^ (prefixWord ++ tailWord_3837682).sum := by decide
  have hdescent : baseEnd_3837682 < baseStart_3837682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837804 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_3837804 : Nat := 118140960795 + 3837804 * 2 ^ 59
def prefixEnd_3837804 : Nat := 4983230072969 + 3 ^ 40 * 3837804 * 2
def baseEnd_3837804 : Nat := 1313758739831871871933511

theorem tailTrace_3837804 : CollatzResearch.WordTrace tailWord_3837804 prefixEnd_3837804 1313758739831871871933511 := by
  unfold tailWord_3837804
  simp only [CollatzResearch.WordTrace]
  refine ⟨69988105694149513792844233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93317474258866018390458977 69988105694149513792844233)
  ·
    refine ⟨52491079270612135344633175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69988105694149513792844233 52491079270612135344633175)
    ·
      refine ⟨78736618905918203016949763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52491079270612135344633175 78736618905918203016949763)
      ·
        refine ⟨118104928358877304525424645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78736618905918203016949763 118104928358877304525424645)
        ·
          refine ⟨22144674067289494598517121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118104928358877304525424645 22144674067289494598517121)
          ·
            refine ⟨16608505550467120948887841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22144674067289494598517121 16608505550467120948887841)
            ·
              refine ⟨12456379162850340711665881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16608505550467120948887841 12456379162850340711665881)
              ·
                refine ⟨9342284372137755533749411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12456379162850340711665881 9342284372137755533749411)
                ·
                  refine ⟨14013426558206633300624117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9342284372137755533749411 14013426558206633300624117)
                  ·
                    refine ⟨1313758739831871871933511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14013426558206633300624117 1313758739831871871933511)
                    ·
                      rfl

theorem cell22_3837804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_3837804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837804 prefixEnd_3837804 := by exact prefixLift 3837804
  have htrace : WordTrace (prefixWord ++ tailWord_3837804) baseStart_3837804 baseEnd_3837804 := by
    simpa [prefixWord, tailWord_3837804, baseEnd_3837804] using wordTrace_append hprefix tailTrace_3837804
  have hstable : (prefixWord ++ tailWord_3837804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837804).length < 2 ^ (prefixWord ++ tailWord_3837804).sum := by decide
  have hdescent : baseEnd_3837804 < baseStart_3837804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837817 : List Nat := [1, 2, 1, 3, 2, 2, 11]
def baseStart_3837817 : Nat := 118140960795 + 3837817 * 2 ^ 59
def prefixEnd_3837817 : Nat := 4983230072969 + 3 ^ 40 * 3837817 * 2
def baseEnd_3837817 : Nat := 48657895925834969309573

theorem tailTrace_3837817 : CollatzResearch.WordTrace tailWord_3837817 prefixEnd_3837817 48657895925834969309573 := by
  unfold tailWord_3837817
  simp only [CollatzResearch.WordTrace]
  refine ⟨139976685537251930805911705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93317790358167953870607803 139976685537251930805911705)
  ·
    refine ⟨104982514152938948104433779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139976685537251930805911705 104982514152938948104433779)
    ·
      refine ⟨157473771229408422156650669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104982514152938948104433779 157473771229408422156650669)
      ·
        refine ⟨59052664211028158308744001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157473771229408422156650669 59052664211028158308744001)
        ·
          refine ⟨44289498158271118731558001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59052664211028158308744001 44289498158271118731558001)
          ·
            refine ⟨33217123618703339048668501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44289498158271118731558001 33217123618703339048668501)
            ·
              refine ⟨48657895925834969309573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33217123618703339048668501 48657895925834969309573)
              ·
                rfl

theorem cell22_3837817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 11].length) (baseStart_3837817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837817 prefixEnd_3837817 := by exact prefixLift 3837817
  have htrace : WordTrace (prefixWord ++ tailWord_3837817) baseStart_3837817 baseEnd_3837817 := by
    simpa [prefixWord, tailWord_3837817, baseEnd_3837817] using wordTrace_append hprefix tailTrace_3837817
  have hstable : (prefixWord ++ tailWord_3837817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837817).length < 2 ^ (prefixWord ++ tailWord_3837817).sum := by decide
  have hdescent : baseEnd_3837817 < baseStart_3837817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837879 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 5]
def baseStart_3837879 : Nat := 118140960795 + 3837879 * 2 ^ 59
def prefixEnd_3837879 : Nat := 4983230072969 + 3 ^ 40 * 3837879 * 2
def baseEnd_3837879 : Nat := 437928137954865558769427

theorem tailTrace_3837879 : CollatzResearch.WordTrace tailWord_3837879 prefixEnd_3837879 437928137954865558769427 := by
  unfold tailWord_3837879
  simp only [CollatzResearch.WordTrace]
  refine ⟨139978946863027315394668691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93319297908684876929779127 139978946863027315394668691)
  ·
    refine ⟨209968420294540973092003037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139978946863027315394668691 209968420294540973092003037)
    ·
      refine ⟨78738157610452864909501139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209968420294540973092003037 78738157610452864909501139)
      ·
        refine ⟨118107236415679297364251709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78738157610452864909501139 118107236415679297364251709)
        ·
          refine ⟨44290213655879736511594391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118107236415679297364251709 44290213655879736511594391)
          ·
            refine ⟨66435320483819604767391587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44290213655879736511594391 66435320483819604767391587)
            ·
              refine ⟨99652980725729407151087381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66435320483819604767391587 99652980725729407151087381)
              ·
                refine ⟨4671233471518565960207221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99652980725729407151087381 4671233471518565960207221)
                ·
                  refine ⟨437928137954865558769427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4671233471518565960207221 437928137954865558769427)
                  ·
                    rfl

theorem cell22_3837879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 5].length) (baseStart_3837879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837879 prefixEnd_3837879 := by exact prefixLift 3837879
  have htrace : WordTrace (prefixWord ++ tailWord_3837879) baseStart_3837879 baseEnd_3837879 := by
    simpa [prefixWord, tailWord_3837879, baseEnd_3837879] using wordTrace_append hprefix tailTrace_3837879
  have hstable : (prefixWord ++ tailWord_3837879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837879).length < 2 ^ (prefixWord ++ tailWord_3837879).sum := by decide
  have hdescent : baseEnd_3837879 < baseStart_3837879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837896 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 5]
def baseStart_3837896 : Nat := 118140960795 + 3837896 * 2 ^ 59
def prefixEnd_3837896 : Nat := 4983230072969 + 3 ^ 40 * 3837896 * 2
def baseEnd_3837896 : Nat := 437930077770671432877743

theorem tailTrace_3837896 : CollatzResearch.WordTrace tailWord_3837896 prefixEnd_3837896 437930077770671432877743 := by
  unfold tailWord_3837896
  simp only [CollatzResearch.WordTrace]
  refine ⟨69989783451982863649018771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93319711269310484865358361 69989783451982863649018771)
  ·
    refine ⟨104984675177974295473528157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69989783451982863649018771 104984675177974295473528157)
    ·
      refine ⟨39369253191740360802573059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104984675177974295473528157 39369253191740360802573059)
      ·
        refine ⟨59053879787610541203859589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39369253191740360802573059 59053879787610541203859589)
        ·
          refine ⟨11072602460176976475723673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59053879787610541203859589 11072602460176976475723673)
          ·
            refine ⟨8304451845132732356792755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11072602460176976475723673 8304451845132732356792755)
            ·
              refine ⟨12456677767699098535189133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8304451845132732356792755 12456677767699098535189133)
              ·
                refine ⟨4671254162887161950695925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12456677767699098535189133 4671254162887161950695925)
                ·
                  refine ⟨437930077770671432877743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4671254162887161950695925 437930077770671432877743)
                  ·
                    rfl

theorem cell22_3837896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_3837896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837896 prefixEnd_3837896 := by exact prefixLift 3837896
  have htrace : WordTrace (prefixWord ++ tailWord_3837896) baseStart_3837896 baseEnd_3837896 := by
    simpa [prefixWord, tailWord_3837896, baseEnd_3837896] using wordTrace_append hprefix tailTrace_3837896
  have hstable : (prefixWord ++ tailWord_3837896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837896).length < 2 ^ (prefixWord ++ tailWord_3837896).sum := by decide
  have hdescent : baseEnd_3837896 < baseStart_3837896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837971 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 2, 4]
def baseStart_3837971 : Nat := 118140960795 + 3837971 * 2 ^ 59
def prefixEnd_3837971 : Nat := 4983230072969 + 3 ^ 40 * 3837971 * 2
def baseEnd_3837971 : Nat := 1313815907344739103007999

theorem tailTrace_3837971 : CollatzResearch.WordTrace tailWord_3837971 prefixEnd_3837971 1313815907344739103007999 := by
  unfold tailWord_3837971
  simp only [CollatzResearch.WordTrace]
  refine ⟨139982302378694015107017767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93321534919129343404678511 139982302378694015107017767)
  ·
    refine ⟨209973453568041022660526651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139982302378694015107017767 209973453568041022660526651)
    ·
      refine ⟨314960180352061533990789977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209973453568041022660526651 314960180352061533990789977)
      ·
        refine ⟨236220135264046150493092483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314960180352061533990789977 236220135264046150493092483)
        ·
          refine ⟨354330202896069225739638725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236220135264046150493092483 354330202896069225739638725)
          ·
            refine ⟨66436913043012979826182261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354330202896069225739638725 66436913043012979826182261)
            ·
              refine ⟨6228460597782466858704587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66436913043012979826182261 6228460597782466858704587)
              ·
                refine ⟨9342690896673700288056881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228460597782466858704587 9342690896673700288056881)
                ·
                  refine ⟨7007018172505275216042661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9342690896673700288056881 7007018172505275216042661)
                  ·
                    refine ⟨1313815907344739103007999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7007018172505275216042661 1313815907344739103007999)
                    ·
                      rfl

theorem cell22_3837971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 4].length) (baseStart_3837971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837971 prefixEnd_3837971 := by exact prefixLift 3837971
  have htrace : WordTrace (prefixWord ++ tailWord_3837971) baseStart_3837971 baseEnd_3837971 := by
    simpa [prefixWord, tailWord_3837971, baseEnd_3837971] using wordTrace_append hprefix tailTrace_3837971
  have hstable : (prefixWord ++ tailWord_3837971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837971).length < 2 ^ (prefixWord ++ tailWord_3837971).sum := by decide
  have hdescent : baseEnd_3837971 < baseStart_3837971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837975 : List Nat := [1, 1, 3, 5, 2, 1, 2, 3, 4]
def baseStart_3837975 : Nat := 118140960795 + 3837975 * 2 ^ 59
def prefixEnd_3837975 : Nat := 4983230072969 + 3 ^ 40 * 3837975 * 2
def baseEnd_3837975 : Nat := 437939092208828141969329

theorem tailTrace_3837975 : CollatzResearch.WordTrace tailWord_3837975 prefixEnd_3837975 437939092208828141969329 := by
  unfold tailWord_3837975
  simp only [CollatzResearch.WordTrace]
  refine ⟨139982448270679523790163379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93321632180453015860108919 139982448270679523790163379)
  ·
    refine ⟨209973672406019285685245069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139982448270679523790163379 209973672406019285685245069)
    ·
      refine ⟨78740127152257232131966901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209973672406019285685245069 78740127152257232131966901)
      ·
        refine ⟨7381886920524115512371897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78740127152257232131966901 7381886920524115512371897)
        ·
          refine ⟨5536415190393086634278923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7381886920524115512371897 5536415190393086634278923)
          ·
            refine ⟨8304622785589629951418385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5536415190393086634278923 8304622785589629951418385)
            ·
              refine ⟨6228467089192222463563789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8304622785589629951418385 6228467089192222463563789)
              ·
                refine ⟨2335675158447083423836421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6228467089192222463563789 2335675158447083423836421)
                ·
                  refine ⟨437939092208828141969329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335675158447083423836421 437939092208828141969329)
                  ·
                    rfl

theorem cell22_3837975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 4].length) (baseStart_3837975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837975 prefixEnd_3837975 := by exact prefixLift 3837975
  have htrace : WordTrace (prefixWord ++ tailWord_3837975) baseStart_3837975 baseEnd_3837975 := by
    simpa [prefixWord, tailWord_3837975, baseEnd_3837975] using wordTrace_append hprefix tailTrace_3837975
  have hstable : (prefixWord ++ tailWord_3837975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837975).length < 2 ^ (prefixWord ++ tailWord_3837975).sum := by decide
  have hdescent : baseEnd_3837975 < baseStart_3837975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837999 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 2, 6]
def baseStart_3837999 : Nat := 118140960795 + 3837999 * 2 ^ 59
def prefixEnd_3837999 : Nat := 4983230072969 + 3 ^ 40 * 3837999 * 2
def baseEnd_3837999 : Nat := 1313825492316956363307913

theorem tailTrace_3837999 : CollatzResearch.WordTrace tailWord_3837999 prefixEnd_3837999 1313825492316956363307913 := by
  unfold tailWord_3837999
  simp only [CollatzResearch.WordTrace]
  refine ⟨139983323622592575889037051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93322215748395050592691367 139983323622592575889037051)
  ·
    refine ⟨209974985433888863833555577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139983323622592575889037051 209974985433888863833555577)
    ·
      refine ⟨157481239075416647875166683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209974985433888863833555577 157481239075416647875166683)
      ·
        refine ⟨236221858613124971812750025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157481239075416647875166683 236221858613124971812750025)
        ·
          refine ⟨177166393959843728859562519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236221858613124971812750025 177166393959843728859562519)
          ·
            refine ⟨265749590939765593289343779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177166393959843728859562519 265749590939765593289343779)
            ·
              refine ⟨398624386409648389934015669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265749590939765593289343779 398624386409648389934015669)
              ·
                refine ⟨37371036225904536556313969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398624386409648389934015669 37371036225904536556313969)
                ·
                  refine ⟨28028277169428402417235477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37371036225904536556313969 28028277169428402417235477)
                  ·
                    refine ⟨1313825492316956363307913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28028277169428402417235477 1313825492316956363307913)
                    ·
                      rfl

theorem cell22_3837999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_3837999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3837999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3837999 prefixEnd_3837999 := by exact prefixLift 3837999
  have htrace : WordTrace (prefixWord ++ tailWord_3837999) baseStart_3837999 baseEnd_3837999 := by
    simpa [prefixWord, tailWord_3837999, baseEnd_3837999] using wordTrace_append hprefix tailTrace_3837999
  have hstable : (prefixWord ++ tailWord_3837999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837999).length < 2 ^ (prefixWord ++ tailWord_3837999).sum := by decide
  have hdescent : baseEnd_3837999 < baseStart_3837999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838125 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3838125 : Nat := 118140960795 + 3838125 * 2 ^ 59
def prefixEnd_3838125 : Nat := 4983230072969 + 3 ^ 40 * 3838125 * 2
def baseEnd_3838125 : Nat := 1313868624691934034657527

theorem tailTrace_3838125 : CollatzResearch.WordTrace tailWord_3838125 prefixEnd_3838125 1313868624691934034657527 := by
  unfold tailWord_3838125
  simp only [CollatzResearch.WordTrace]
  refine ⟨139987919220136099408123829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93325279480090732938749219 139987919220136099408123829)
  ·
    refine ⟨13123867426887759319511609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139987919220136099408123829 13123867426887759319511609)
    ·
      refine ⟨9842900570165819489633707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13123867426887759319511609 9842900570165819489633707)
      ·
        refine ⟨14764350855248729234450561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9842900570165819489633707 14764350855248729234450561)
        ·
          refine ⟨11073263141436546925837921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14764350855248729234450561 11073263141436546925837921)
          ·
            refine ⟨8304947356077410194378441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11073263141436546925837921 8304947356077410194378441)
            ·
              refine ⟨6228710517058057645783831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8304947356077410194378441 6228710517058057645783831)
              ·
                refine ⟨9343065775587086468675747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228710517058057645783831 9343065775587086468675747)
                ·
                  refine ⟨14014598663380629703013621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9343065775587086468675747 14014598663380629703013621)
                  ·
                    refine ⟨1313868624691934034657527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14014598663380629703013621 1313868624691934034657527)
                    ·
                      rfl

theorem cell22_3838125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3838125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838125 prefixEnd_3838125 := by exact prefixLift 3838125
  have htrace : WordTrace (prefixWord ++ tailWord_3838125) baseStart_3838125 baseEnd_3838125 := by
    simpa [prefixWord, tailWord_3838125, baseEnd_3838125] using wordTrace_append hprefix tailTrace_3838125
  have hstable : (prefixWord ++ tailWord_3838125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838125).length < 2 ^ (prefixWord ++ tailWord_3838125).sum := by decide
  have hdescent : baseEnd_3838125 < baseStart_3838125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838146 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3838146 : Nat := 118140960795 + 3838146 * 2 ^ 59
def prefixEnd_3838146 : Nat := 4983230072969 + 3 ^ 40 * 3838146 * 2
def baseEnd_3838146 : Nat := 1313875813421096979882463

theorem tailTrace_3838146 : CollatzResearch.WordTrace tailWord_3838146 prefixEnd_3838146 1313875813421096979882463 := by
  unfold tailWord_3838146
  simp only [CollatzResearch.WordTrace]
  refine ⟨34997171288265004998659573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93325790102040013329758861 34997171288265004998659573)
  ·
    refine ⟨3280984808274844218624335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34997171288265004998659573 3280984808274844218624335)
    ·
      refine ⟨4921477212412266327936503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3280984808274844218624335 4921477212412266327936503)
      ·
        refine ⟨7382215818618399491904755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4921477212412266327936503 7382215818618399491904755)
        ·
          refine ⟨11073323727927599237857133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7382215818618399491904755 11073323727927599237857133)
          ·
            refine ⟨4152496397972849714196425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11073323727927599237857133 4152496397972849714196425)
            ·
              refine ⟨3114372298479637285647319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4152496397972849714196425 3114372298479637285647319)
              ·
                refine ⟨4671558447719455928470979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114372298479637285647319 4671558447719455928470979)
                ·
                  refine ⟨7007337671579183892706469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671558447719455928470979 7007337671579183892706469)
                  ·
                    refine ⟨1313875813421096979882463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7007337671579183892706469 1313875813421096979882463)
                    ·
                      rfl

theorem cell22_3838146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3838146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838146 prefixEnd_3838146 := by exact prefixLift 3838146
  have htrace : WordTrace (prefixWord ++ tailWord_3838146) baseStart_3838146 baseEnd_3838146 := by
    simpa [prefixWord, tailWord_3838146, baseEnd_3838146] using wordTrace_append hprefix tailTrace_3838146
  have hstable : (prefixWord ++ tailWord_3838146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838146).length < 2 ^ (prefixWord ++ tailWord_3838146).sum := by decide
  have hdescent : baseEnd_3838146 < baseStart_3838146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838198 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3838198 : Nat := 118140960795 + 3838198 * 2 ^ 59
def prefixEnd_3838198 : Nat := 4983230072969 + 3 ^ 40 * 3838198 * 2
def baseEnd_3838198 : Nat := 1313893614083786177582303

theorem tailTrace_3838198 : CollatzResearch.WordTrace tailWord_3838198 prefixEnd_3838198 1313893614083786177582303 := by
  unfold tailWord_3838198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8749411359304477054720703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93327054499247755250354165 8749411359304477054720703)
  ·
    refine ⟨13124117038956715582081055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8749411359304477054720703 13124117038956715582081055)
    ·
      refine ⟨19686175558435073373121583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13124117038956715582081055 19686175558435073373121583)
      ·
        refine ⟨29529263337652610059682375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19686175558435073373121583 29529263337652610059682375)
        ·
          refine ⟨44293895006478915089523563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29529263337652610059682375 44293895006478915089523563)
          ·
            refine ⟨66440842509718372634285345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44293895006478915089523563 66440842509718372634285345)
            ·
              refine ⟨49830631882288779475714009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66440842509718372634285345 49830631882288779475714009)
              ·
                refine ⟨37372973911716584606785507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49830631882288779475714009 37372973911716584606785507)
                ·
                  refine ⟨56059460867574876910178261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37372973911716584606785507 56059460867574876910178261)
                  ·
                    refine ⟨1313893614083786177582303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56059460867574876910178261 1313893614083786177582303)
                    ·
                      rfl

theorem cell22_3838198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3838198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838198 prefixEnd_3838198 := by exact prefixLift 3838198
  have htrace : WordTrace (prefixWord ++ tailWord_3838198) baseStart_3838198 baseEnd_3838198 := by
    simpa [prefixWord, tailWord_3838198, baseEnd_3838198] using wordTrace_append hprefix tailTrace_3838198
  have hstable : (prefixWord ++ tailWord_3838198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838198).length < 2 ^ (prefixWord ++ tailWord_3838198).sum := by decide
  have hdescent : baseEnd_3838198 < baseStart_3838198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838204 : List Nat := [2, 2, 2, 1, 4, 3, 1, 3, 1, 3]
def baseStart_3838204 : Nat := 118140960795 + 3838204 * 2 ^ 59
def prefixEnd_3838204 : Nat := 4983230072969 + 3 ^ 40 * 3838204 * 2
def baseEnd_3838204 : Nat := 1313895668006404161932285

theorem tailTrace_3838204 : CollatzResearch.WordTrace tailWord_3838204 prefixEnd_3838204 1313895668006404161932285 := by
  unfold tailWord_3838204
  simp only [CollatzResearch.WordTrace]
  refine ⟨69995400293424947950124833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93327200391233263933499777 69995400293424947950124833)
  ·
    refine ⟨52496550220068710962593625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69995400293424947950124833 52496550220068710962593625)
    ·
      refine ⟨39372412665051533221945219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52496550220068710962593625 39372412665051533221945219)
      ·
        refine ⟨59058618997577299832917829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39372412665051533221945219 59058618997577299832917829)
        ·
          refine ⟨11073491062045743718672093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59058618997577299832917829 11073491062045743718672093)
          ·
            refine ⟨4152559148267153894502035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11073491062045743718672093 4152559148267153894502035)
            ·
              refine ⟨6228838722400730841753053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152559148267153894502035 6228838722400730841753053)
              ·
                refine ⟨2335814520900274065657395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6228838722400730841753053 2335814520900274065657395)
                ·
                  refine ⟨3503721781350411098486093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335814520900274065657395 3503721781350411098486093)
                  ·
                    refine ⟨1313895668006404161932285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3503721781350411098486093 1313895668006404161932285)
                    ·
                      rfl

theorem cell22_3838204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_3838204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838204 prefixEnd_3838204 := by exact prefixLift 3838204
  have htrace : WordTrace (prefixWord ++ tailWord_3838204) baseStart_3838204 baseEnd_3838204 := by
    simpa [prefixWord, tailWord_3838204, baseEnd_3838204] using wordTrace_append hprefix tailTrace_3838204
  have hstable : (prefixWord ++ tailWord_3838204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838204).length < 2 ^ (prefixWord ++ tailWord_3838204).sum := by decide
  have hdescent : baseEnd_3838204 < baseStart_3838204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838234 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_3838234 : Nat := 118140960795 + 3838234 * 2 ^ 59
def prefixEnd_3838234 : Nat := 4983230072969 + 3 ^ 40 * 3838234 * 2
def baseEnd_3838234 : Nat := 437968645873164694560731

theorem tailTrace_3838234 : CollatzResearch.WordTrace tailWord_3838234 prefixEnd_3838234 437968645873164694560731 := by
  unfold tailWord_3838234
  simp only [CollatzResearch.WordTrace]
  refine ⟨34997973694185302755960439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93327929851160807349227837 34997973694185302755960439)
  ·
    refine ⟨52496960541277954133940659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34997973694185302755960439 52496960541277954133940659)
    ·
      refine ⟨78745440811916931200910989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52496960541277954133940659 78745440811916931200910989)
      ·
        refine ⟨29529540304468849200341621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78745440811916931200910989 29529540304468849200341621)
        ·
          refine ⟨2768394403543954612532027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29529540304468849200341621 2768394403543954612532027)
          ·
            refine ⟨4152591605315931918798041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768394403543954612532027 4152591605315931918798041)
            ·
              refine ⟨3114443703986948939098531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4152591605315931918798041 3114443703986948939098531)
              ·
                refine ⟨4671665555980423408647797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114443703986948939098531 4671665555980423408647797)
                ·
                  refine ⟨437968645873164694560731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4671665555980423408647797 437968645873164694560731)
                  ·
                    rfl

theorem cell22_3838234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_3838234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838234 prefixEnd_3838234 := by exact prefixLift 3838234
  have htrace : WordTrace (prefixWord ++ tailWord_3838234) baseStart_3838234 baseEnd_3838234 := by
    simpa [prefixWord, tailWord_3838234, baseEnd_3838234] using wordTrace_append hprefix tailTrace_3838234
  have hstable : (prefixWord ++ tailWord_3838234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838234).length < 2 ^ (prefixWord ++ tailWord_3838234).sum := by decide
  have hdescent : baseEnd_3838234 < baseStart_3838234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838243 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 1, 5]
def baseStart_3838243 : Nat := 118140960795 + 3838243 * 2 ^ 59
def prefixEnd_3838243 : Nat := 4983230072969 + 3 ^ 40 * 3838243 * 2
def baseEnd_3838243 : Nat := 1313909018503421060207165

theorem tailTrace_3838243 : CollatzResearch.WordTrace tailWord_3838243 prefixEnd_3838243 1313909018503421060207165 := by
  unfold tailWord_3838243
  simp only [CollatzResearch.WordTrace]
  refine ⟨139992223033708605560919383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93328148689139070373946255 139992223033708605560919383)
  ·
    refine ⟨209988334550562908341379075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139992223033708605560919383 209988334550562908341379075)
    ·
      refine ⟨314982501825844362512068613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209988334550562908341379075 314982501825844362512068613)
      ·
        refine ⟨59059219092345817971012865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314982501825844362512068613 59059219092345817971012865)
        ·
          refine ⟨44294414319259363478259649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59059219092345817971012865 44294414319259363478259649)
          ·
            refine ⟨33220810739444522608694737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44294414319259363478259649 33220810739444522608694737)
            ·
              refine ⟨24915608054583391956521053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33220810739444522608694737 24915608054583391956521053)
              ·
                refine ⟨9343353020468771983695395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24915608054583391956521053 9343353020468771983695395)
                ·
                  refine ⟨14015029530703157975543093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9343353020468771983695395 14015029530703157975543093)
                  ·
                    refine ⟨1313909018503421060207165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14015029530703157975543093 1313909018503421060207165)
                    ·
                      rfl

theorem cell22_3838243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 5].length) (baseStart_3838243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838243 prefixEnd_3838243 := by exact prefixLift 3838243
  have htrace : WordTrace (prefixWord ++ tailWord_3838243) baseStart_3838243 baseEnd_3838243 := by
    simpa [prefixWord, tailWord_3838243, baseEnd_3838243] using wordTrace_append hprefix tailTrace_3838243
  have hstable : (prefixWord ++ tailWord_3838243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838243).length < 2 ^ (prefixWord ++ tailWord_3838243).sum := by decide
  have hdescent : baseEnd_3838243 < baseStart_3838243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838260 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3838260 : Nat := 118140960795 + 3838260 * 2 ^ 59
def prefixEnd_3838260 : Nat := 4983230072969 + 3 ^ 40 * 3838260 * 2
def baseEnd_3838260 : Nat := 1313914837950838682532113

theorem tailTrace_3838260 : CollatzResearch.WordTrace tailWord_3838260 prefixEnd_3838260 1313914837950838682532113 := by
  unfold tailWord_3838260
  simp only [CollatzResearch.WordTrace]
  refine ⟨69996421537323508732144117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93328562049764678309525489 69996421537323508732144117)
  ·
    refine ⟨6562164519124078943638511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69996421537323508732144117 6562164519124078943638511)
    ·
      refine ⟨9843246778686118415457767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6562164519124078943638511 9843246778686118415457767)
      ·
        refine ⟨14764870168029177623186651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9843246778686118415457767 14764870168029177623186651)
        ·
          refine ⟨22147305252043766434779977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14764870168029177623186651 22147305252043766434779977)
          ·
            refine ⟨16610478939032824826084983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22147305252043766434779977 16610478939032824826084983)
            ·
              refine ⟨24915718408549237239127475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16610478939032824826084983 24915718408549237239127475)
              ·
                refine ⟨37373577612823855858691213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24915718408549237239127475 37373577612823855858691213)
                ·
                  refine ⟨14015091604808945947009205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37373577612823855858691213 14015091604808945947009205)
                  ·
                    refine ⟨1313914837950838682532113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14015091604808945947009205 1313914837950838682532113)
                    ·
                      rfl

theorem cell22_3838260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3838260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838260 prefixEnd_3838260 := by exact prefixLift 3838260
  have htrace : WordTrace (prefixWord ++ tailWord_3838260) baseStart_3838260 baseEnd_3838260 := by
    simpa [prefixWord, tailWord_3838260, baseEnd_3838260] using wordTrace_append hprefix tailTrace_3838260
  have hstable : (prefixWord ++ tailWord_3838260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838260).length < 2 ^ (prefixWord ++ tailWord_3838260).sum := by decide
  have hdescent : baseEnd_3838260 < baseStart_3838260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838273 : List Nat := [1, 2, 5, 2, 12]
def baseStart_3838273 : Nat := 118140960795 + 3838273 * 2 ^ 59
def prefixEnd_3838273 : Nat := 4983230072969 + 3 ^ 40 * 3838273 * 2
def baseEnd_3838273 : Nat := 5407075259738728320811

theorem tailTrace_3838273 : CollatzResearch.WordTrace tailWord_3838273 prefixEnd_3838273 5407075259738728320811 := by
  unfold tailWord_3838273
  simp only [CollatzResearch.WordTrace]
  refine ⟨139993317223599920684511473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93328878149066613789674315 139993317223599920684511473)
  ·
    refine ⟨104994987917699940513383605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139993317223599920684511473 104994987917699940513383605)
    ·
      refine ⟨9843280117284369423129713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104994987917699940513383605 9843280117284369423129713)
      ·
        refine ⟨7382460087963277067347285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9843280117284369423129713 7382460087963277067347285)
        ·
          refine ⟨5407075259738728320811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7382460087963277067347285 5407075259738728320811)
          ·
            rfl

theorem cell22_3838273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 12].length) (baseStart_3838273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838273 prefixEnd_3838273 := by exact prefixLift 3838273
  have htrace : WordTrace (prefixWord ++ tailWord_3838273) baseStart_3838273 baseEnd_3838273 := by
    simpa [prefixWord, tailWord_3838273, baseEnd_3838273] using wordTrace_append hprefix tailTrace_3838273
  have hstable : (prefixWord ++ tailWord_3838273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838273).length < 2 ^ (prefixWord ++ tailWord_3838273).sum := by decide
  have hdescent : baseEnd_3838273 < baseStart_3838273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838358 : List Nat := [5, 3, 1, 2, 1, 2, 2, 6]
def baseStart_3838358 : Nat := 118140960795 + 3838358 * 2 ^ 59
def prefixEnd_3838358 : Nat := 4983230072969 + 3 ^ 40 * 3838358 * 2
def baseEnd_3838358 : Nat := 145994265039288788175757

theorem tailTrace_3838358 : CollatzResearch.WordTrace tailWord_3838358 prefixEnd_3838358 145994265039288788175757 := by
  unfold tailWord_3838358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8749776089268248762584733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93330944952194653467570485 8749776089268248762584733)
  ·
    refine ⟨3281166033475593285969275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8749776089268248762584733 3281166033475593285969275)
    ·
      refine ⟨4921749050213389928953913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3281166033475593285969275 4921749050213389928953913)
      ·
        refine ⟨3691311787660042446715435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4921749050213389928953913 3691311787660042446715435)
        ·
          refine ⟨5536967681490063670073153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691311787660042446715435 5536967681490063670073153)
          ·
            refine ⟨4152725761117547752554865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5536967681490063670073153 4152725761117547752554865)
            ·
              refine ⟨3114544320838160814416149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4152725761117547752554865 3114544320838160814416149)
              ·
                refine ⟨145994265039288788175757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3114544320838160814416149 145994265039288788175757)
                ·
                  rfl

theorem cell22_3838358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_3838358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838358 prefixEnd_3838358 := by exact prefixLift 3838358
  have htrace : WordTrace (prefixWord ++ tailWord_3838358) baseStart_3838358 baseEnd_3838358 := by
    simpa [prefixWord, tailWord_3838358, baseEnd_3838358] using wordTrace_append hprefix tailTrace_3838358
  have hstable : (prefixWord ++ tailWord_3838358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838358).length < 2 ^ (prefixWord ++ tailWord_3838358).sum := by decide
  have hdescent : baseEnd_3838358 < baseStart_3838358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838397 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 6]
def baseStart_3838397 : Nat := 118140960795 + 3838397 * 2 ^ 59
def prefixEnd_3838397 : Nat := 4983230072969 + 3 ^ 40 * 3838397 * 2
def baseEnd_3838397 : Nat := 437987245283538663952231

theorem tailTrace_3838397 : CollatzResearch.WordTrace tailWord_3838397 prefixEnd_3838397 437987245283538663952231 := by
  unfold tailWord_3838397
  simp only [CollatzResearch.WordTrace]
  refine ⟨139997839875150689862025445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93331893250100459908016963 139997839875150689862025445)
  ·
    refine ⟨26249594976590754349129771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139997839875150689862025445 26249594976590754349129771)
    ·
      refine ⟨39374392464886131523694657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26249594976590754349129771 39374392464886131523694657)
      ·
        refine ⟨29530794348664598642770993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39374392464886131523694657 29530794348664598642770993)
        ·
          refine ⟨22148095761498448982078245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29530794348664598642770993 22148095761498448982078245)
          ·
            refine ⟨4152767955280959184139671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22148095761498448982078245 4152767955280959184139671)
            ·
              refine ⟨6229151932921438776209507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152767955280959184139671 6229151932921438776209507)
              ·
                refine ⟨9343727899382158164314261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229151932921438776209507 9343727899382158164314261)
                ·
                  refine ⟨437987245283538663952231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9343727899382158164314261 437987245283538663952231)
                  ·
                    rfl

theorem cell22_3838397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_3838397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838397 prefixEnd_3838397 := by exact prefixLift 3838397
  have htrace : WordTrace (prefixWord ++ tailWord_3838397) baseStart_3838397 baseEnd_3838397 := by
    simpa [prefixWord, tailWord_3838397, baseEnd_3838397] using wordTrace_append hprefix tailTrace_3838397
  have hstable : (prefixWord ++ tailWord_3838397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838397).length < 2 ^ (prefixWord ++ tailWord_3838397).sum := by decide
  have hdescent : baseEnd_3838397 < baseStart_3838397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838410 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_3838410 : Nat := 118140960795 + 3838410 * 2 ^ 59
def prefixEnd_3838410 : Nat := 4983230072969 + 3 ^ 40 * 3838410 * 2
def baseEnd_3838410 : Nat := 1313966186016288291281653

theorem tailTrace_3838410 : CollatzResearch.WordTrace tailWord_3838410 prefixEnd_3838410 1313966186016288291281653 := by
  unfold tailWord_3838410
  simp only [CollatzResearch.WordTrace]
  refine ⟨34999578506025898270562171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93332209349402395388165789 34999578506025898270562171)
  ·
    refine ⟨52499367759038847405843257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34999578506025898270562171 52499367759038847405843257)
    ·
      refine ⟨39374525819279135554382443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52499367759038847405843257 39374525819279135554382443)
      ·
        refine ⟨59061788728918703331573665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39374525819279135554382443 59061788728918703331573665)
        ·
          refine ⟨44296341546689027498680249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59061788728918703331573665 44296341546689027498680249)
          ·
            refine ⟨33222256160016770624010187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44296341546689027498680249 33222256160016770624010187)
            ·
              refine ⟨49833384240025155936015281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33222256160016770624010187 49833384240025155936015281)
              ·
                refine ⟨37375038180018866952011461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49833384240025155936015281 37375038180018866952011461)
                ·
                  refine ⟨7007819658753537553502149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37375038180018866952011461 7007819658753537553502149)
                  ·
                    refine ⟨1313966186016288291281653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7007819658753537553502149 1313966186016288291281653)
                    ·
                      rfl

theorem cell22_3838410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_3838410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838410 prefixEnd_3838410 := by exact prefixLift 3838410
  have htrace : WordTrace (prefixWord ++ tailWord_3838410) baseStart_3838410 baseEnd_3838410 := by
    simpa [prefixWord, tailWord_3838410, baseEnd_3838410] using wordTrace_append hprefix tailTrace_3838410
  have hstable : (prefixWord ++ tailWord_3838410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838410).length < 2 ^ (prefixWord ++ tailWord_3838410).sum := by decide
  have hdescent : baseEnd_3838410 < baseStart_3838410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838485 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_3838485 : Nat := 118140960795 + 3838485 * 2 ^ 59
def prefixEnd_3838485 : Nat := 4983230072969 + 3 ^ 40 * 3838485 * 2
def baseEnd_3838485 : Nat := 1313991860049013095656423

theorem tailTrace_3838485 : CollatzResearch.WordTrace tailWord_3838485 prefixEnd_3838485 1313991860049013095656423 := by
  unfold tailWord_3838485
  simp only [CollatzResearch.WordTrace]
  refine ⟨140001049498831880891228909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93334032999221253927485939 140001049498831880891228909)
  ·
    refine ⟨52500393562061955334210841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140001049498831880891228909 52500393562061955334210841)
    ·
      refine ⟨39375295171546466500658131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52500393562061955334210841 39375295171546466500658131)
      ·
        refine ⟨59062942757319699750987197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39375295171546466500658131 59062942757319699750987197)
        ·
          refine ⟨22148603533994887406620199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59062942757319699750987197 22148603533994887406620199)
          ·
            refine ⟨33222905300992331109930299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22148603533994887406620199 33222905300992331109930299)
            ·
              refine ⟨49834357951488496664895449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33222905300992331109930299 49834357951488496664895449)
              ·
                refine ⟨37375768463616372498671587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49834357951488496664895449 37375768463616372498671587)
                ·
                  refine ⟨56063652695424558748007381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37375768463616372498671587 56063652695424558748007381)
                  ·
                    refine ⟨1313991860049013095656423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56063652695424558748007381 1313991860049013095656423)
                    ·
                      rfl

theorem cell22_3838485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_3838485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838485 prefixEnd_3838485 := by exact prefixLift 3838485
  have htrace : WordTrace (prefixWord ++ tailWord_3838485) baseStart_3838485 baseEnd_3838485 := by
    simpa [prefixWord, tailWord_3838485, baseEnd_3838485] using wordTrace_append hprefix tailTrace_3838485
  have hstable : (prefixWord ++ tailWord_3838485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838485).length < 2 ^ (prefixWord ++ tailWord_3838485).sum := by decide
  have hdescent : baseEnd_3838485 < baseStart_3838485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838504 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 5]
def baseStart_3838504 : Nat := 118140960795 + 3838504 * 2 ^ 59
def prefixEnd_3838504 : Nat := 4983230072969 + 3 ^ 40 * 3838504 * 2
def baseEnd_3838504 : Nat := 437999454712434459810455

theorem tailTrace_3838504 : CollatzResearch.WordTrace tailWord_3838504 prefixEnd_3838504 437999454712434459810455 := by
  unfold tailWord_3838504
  simp only [CollatzResearch.WordTrace]
  refine ⟨70000871242881523568085283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93334494990508698090780377 70000871242881523568085283)
  ·
    refine ⟨105001306864322285352127925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70000871242881523568085283 105001306864322285352127925)
    ·
      refine ⟨9843872518530214251761993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105001306864322285352127925 9843872518530214251761993)
      ·
        refine ⟨7382904388897660688821495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9843872518530214251761993 7382904388897660688821495)
        ·
          refine ⟨11074356583346491033232243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7382904388897660688821495 11074356583346491033232243)
          ·
            refine ⟨16611534875019736549848365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11074356583346491033232243 16611534875019736549848365)
            ·
              refine ⟨6229325578132401206193137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16611534875019736549848365 6229325578132401206193137)
              ·
                refine ⟨4671994183599300904644853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6229325578132401206193137 4671994183599300904644853)
                ·
                  refine ⟨437999454712434459810455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4671994183599300904644853 437999454712434459810455)
                  ·
                    rfl

theorem cell22_3838504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_3838504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838504 prefixEnd_3838504 := by exact prefixLift 3838504
  have htrace : WordTrace (prefixWord ++ tailWord_3838504) baseStart_3838504 baseEnd_3838504 := by
    simpa [prefixWord, tailWord_3838504, baseEnd_3838504] using wordTrace_append hprefix tailTrace_3838504
  have hstable : (prefixWord ++ tailWord_3838504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838504).length < 2 ^ (prefixWord ++ tailWord_3838504).sum := by decide
  have hdescent : baseEnd_3838504 < baseStart_3838504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838549 : List Nat := [1, 3, 2, 2, 1, 1, 5, 3, 4]
def baseStart_3838549 : Nat := 118140960795 + 3838549 * 2 ^ 59
def prefixEnd_3838549 : Nat := 4983230072969 + 3 ^ 40 * 3838549 * 2
def baseEnd_3838549 : Nat := 438004589518979420685409

theorem tailTrace_3838549 : CollatzResearch.WordTrace tailWord_3838549 prefixEnd_3838549 438004589518979420685409 := by
  unfold tailWord_3838549
  simp only [CollatzResearch.WordTrace]
  refine ⟨140003383770600019821558701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93335589180400013214372467 140003383770600019821558701)
  ·
    refine ⟨52501268913975007433084513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140003383770600019821558701 52501268913975007433084513)
    ·
      refine ⟨39375951685481255574813385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52501268913975007433084513 39375951685481255574813385)
      ·
        refine ⟨29531963764110941681110039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39375951685481255574813385 29531963764110941681110039)
        ·
          refine ⟨44297945646166412521665059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29531963764110941681110039 44297945646166412521665059)
          ·
            refine ⟨66446918469249618782497589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44297945646166412521665059 66446918469249618782497589)
            ·
              refine ⟨6229398606492151760859149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66446918469249618782497589 6229398606492151760859149)
              ·
                refine ⟨2336024477434556910322181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6229398606492151760859149 2336024477434556910322181)
                ·
                  refine ⟨438004589518979420685409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336024477434556910322181 438004589518979420685409)
                  ·
                    rfl

theorem cell22_3838549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_3838549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838549 prefixEnd_3838549 := by exact prefixLift 3838549
  have htrace : WordTrace (prefixWord ++ tailWord_3838549) baseStart_3838549 baseEnd_3838549 := by
    simpa [prefixWord, tailWord_3838549, baseEnd_3838549] using wordTrace_append hprefix tailTrace_3838549
  have hstable : (prefixWord ++ tailWord_3838549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838549).length < 2 ^ (prefixWord ++ tailWord_3838549).sum := by decide
  have hdescent : baseEnd_3838549 < baseStart_3838549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838560 : List Nat := [2, 1, 1, 3, 2, 1, 12]
def baseStart_3838560 : Nat := 118140960795 + 3838560 * 2 ^ 59
def prefixEnd_3838560 : Nat := 4983230072969 + 3 ^ 40 * 3838560 * 2
def baseEnd_3838560 : Nat := 48667316077101403704859

theorem tailTrace_3838560 : CollatzResearch.WordTrace tailWord_3838560 prefixEnd_3838560 48667316077101403704859 := by
  unfold tailWord_3838560
  simp only [CollatzResearch.WordTrace]
  refine ⟨70001892486780084350104567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93335856649040112466806089 70001892486780084350104567)
  ·
    refine ⟨105002838730170126525156851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70001892486780084350104567 105002838730170126525156851)
    ·
      refine ⟨157504258095255189787735277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105002838730170126525156851 157504258095255189787735277)
      ·
        refine ⟨59064096785720696170400729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157504258095255189787735277 59064096785720696170400729)
        ·
          refine ⟨44298072589290522127800547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59064096785720696170400729 44298072589290522127800547)
          ·
            refine ⟨66447108883935783191700821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44298072589290522127800547 66447108883935783191700821)
            ·
              refine ⟨48667316077101403704859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 66447108883935783191700821 48667316077101403704859)
              ·
                rfl

theorem cell22_3838560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 12].length) (baseStart_3838560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838560 prefixEnd_3838560 := by exact prefixLift 3838560
  have htrace : WordTrace (prefixWord ++ tailWord_3838560) baseStart_3838560 baseEnd_3838560 := by
    simpa [prefixWord, tailWord_3838560, baseEnd_3838560] using wordTrace_append hprefix tailTrace_3838560
  have hstable : (prefixWord ++ tailWord_3838560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838560).length < 2 ^ (prefixWord ++ tailWord_3838560).sum := by decide
  have hdescent : baseEnd_3838560 < baseStart_3838560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838564 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_3838564 : Nat := 118140960795 + 3838564 * 2 ^ 59
def prefixEnd_3838564 : Nat := 4983230072969 + 3 ^ 40 * 3838564 * 2
def baseEnd_3838564 : Nat := 1314018903363483222931181

theorem tailTrace_3838564 : CollatzResearch.WordTrace tailWord_3838564 prefixEnd_3838564 1314018903363483222931181 := by
  unfold tailWord_3838564
  simp only [CollatzResearch.WordTrace]
  refine ⟨70001965432772838691677373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93335953910363784922236497 70001965432772838691677373)
  ·
    refine ⟨26250737037289814509379015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70001965432772838691677373 26250737037289814509379015)
    ·
      refine ⟨39376105555934721764068523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26250737037289814509379015 39376105555934721764068523)
      ·
        refine ⟨59064158333902082646102785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39376105555934721764068523 59064158333902082646102785)
        ·
          refine ⟨44298118750426561984577089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59064158333902082646102785 44298118750426561984577089)
          ·
            refine ⟨33223589062819921488432817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44298118750426561984577089 33223589062819921488432817)
            ·
              refine ⟨24917691797114941116324613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33223589062819921488432817 24917691797114941116324613)
              ·
                refine ⟨4672067211959051459310865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24917691797114941116324613 4672067211959051459310865)
                ·
                  refine ⟨3504050408969288594483149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4672067211959051459310865 3504050408969288594483149)
                  ·
                    refine ⟨1314018903363483222931181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504050408969288594483149 1314018903363483222931181)
                    ·
                      rfl

theorem cell22_3838564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_3838564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838564 prefixEnd_3838564 := by exact prefixLift 3838564
  have htrace : WordTrace (prefixWord ++ tailWord_3838564) baseStart_3838564 baseEnd_3838564 := by
    simpa [prefixWord, tailWord_3838564, baseEnd_3838564] using wordTrace_append hprefix tailTrace_3838564
  have hstable : (prefixWord ++ tailWord_3838564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838564).length < 2 ^ (prefixWord ++ tailWord_3838564).sum := by decide
  have hdescent : baseEnd_3838564 < baseStart_3838564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838697 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_3838697 : Nat := 118140960795 + 3838697 * 2 ^ 59
def prefixEnd_3838697 : Nat := 4983230072969 + 3 ^ 40 * 3838697 * 2
def baseEnd_3838697 : Nat := 1314064431981515209355773

theorem tailTrace_3838697 : CollatzResearch.WordTrace tailWord_3838697 prefixEnd_3838697 1314064431981515209355773 := by
  unfold tailWord_3838697
  simp only [CollatzResearch.WordTrace]
  refine ⟨140008781774063841097946345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93339187849375894065297563 140008781774063841097946345)
  ·
    refine ⟨105006586330547880823459759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140008781774063841097946345 105006586330547880823459759)
    ·
      refine ⟨157509879495821821235189639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105006586330547880823459759 157509879495821821235189639)
      ·
        refine ⟨236264819243732731852784459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157509879495821821235189639 236264819243732731852784459)
        ·
          refine ⟨354397228865599097779176689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236264819243732731852784459 354397228865599097779176689)
          ·
            refine ⟨265797921649199323334382517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354397228865599097779176689 265797921649199323334382517)
            ·
              refine ⟨24918555154612436562598361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265797921649199323334382517 24918555154612436562598361)
              ·
                refine ⟨18688916365959327421948771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24918555154612436562598361 18688916365959327421948771)
                ·
                  refine ⟨28033374548938991132923157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18688916365959327421948771 28033374548938991132923157)
                  ·
                    refine ⟨1314064431981515209355773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28033374548938991132923157 1314064431981515209355773)
                    ·
                      rfl

theorem cell22_3838697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_3838697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838697 prefixEnd_3838697 := by exact prefixLift 3838697
  have htrace : WordTrace (prefixWord ++ tailWord_3838697) baseStart_3838697 baseEnd_3838697 := by
    simpa [prefixWord, tailWord_3838697, baseEnd_3838697] using wordTrace_append hprefix tailTrace_3838697
  have hstable : (prefixWord ++ tailWord_3838697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838697).length < 2 ^ (prefixWord ++ tailWord_3838697).sum := by decide
  have hdescent : baseEnd_3838697 < baseStart_3838697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838712 : List Nat := [2, 1, 2, 1, 1, 2, 5, 8]
def baseStart_3838712 : Nat := 118140960795 + 3838712 * 2 ^ 59
def prefixEnd_3838712 : Nat := 4983230072969 + 3 ^ 40 * 3838712 * 2
def baseEnd_3838712 : Nat := 146007729643117796692303

theorem tailTrace_3838712 : CollatzResearch.WordTrace tailWord_3838712 prefixEnd_3838712 146007729643117796692303 := by
  unfold tailWord_3838712
  simp only [CollatzResearch.WordTrace]
  refine ⟨70004664434504749329871195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93339552579339665773161593 70004664434504749329871195)
  ·
    refine ⟨105006996651757123994806793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70004664434504749329871195 105006996651757123994806793)
    ·
      refine ⟨78755247488817842996105095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105006996651757123994806793 78755247488817842996105095)
      ·
        refine ⟨118132871233226764494157643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78755247488817842996105095 118132871233226764494157643)
        ·
          refine ⟨177199306849840146741236465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118132871233226764494157643 177199306849840146741236465)
          ·
            refine ⟨132899480137380110055927349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177199306849840146741236465 132899480137380110055927349)
            ·
              refine ⟨12459326262879385317743189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132899480137380110055927349 12459326262879385317743189)
              ·
                refine ⟨146007729643117796692303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12459326262879385317743189 146007729643117796692303)
                ·
                  rfl

theorem cell22_3838712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 8].length) (baseStart_3838712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838712 prefixEnd_3838712 := by exact prefixLift 3838712
  have htrace : WordTrace (prefixWord ++ tailWord_3838712) baseStart_3838712 baseEnd_3838712 := by
    simpa [prefixWord, tailWord_3838712, baseEnd_3838712] using wordTrace_append hprefix tailTrace_3838712
  have hstable : (prefixWord ++ tailWord_3838712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838712).length < 2 ^ (prefixWord ++ tailWord_3838712).sum := by decide
  have hdescent : baseEnd_3838712 < baseStart_3838712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838718 : List Nat := [4, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_3838718 : Nat := 118140960795 + 3838718 * 2 ^ 59
def prefixEnd_3838718 : Nat := 4983230072969 + 3 ^ 40 * 3838718 * 2
def baseEnd_3838718 : Nat := 438023873570226051526903

theorem tailTrace_3838718 : CollatzResearch.WordTrace tailWord_3838718 prefixEnd_3838718 438023873570226051526903 := by
  unfold tailWord_3838718
  simp only [CollatzResearch.WordTrace]
  refine ⟨17501193463373470210557601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93339698471325174456307205 17501193463373470210557601)
  ·
    refine ⟨13125895097530102657918201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17501193463373470210557601 13125895097530102657918201)
    ·
      refine ⟨9844421323147576993438651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13125895097530102657918201 9844421323147576993438651)
      ·
        refine ⟨14766631984721365490157977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9844421323147576993438651 14766631984721365490157977)
        ·
          refine ⟨11074973988541024117618483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14766631984721365490157977 11074973988541024117618483)
          ·
            refine ⟨16612460982811536176427725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11074973988541024117618483 16612460982811536176427725)
            ·
              refine ⟨6229672868554326066160397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16612460982811536176427725 6229672868554326066160397)
              ·
                refine ⟨2336127325707872274810149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6229672868554326066160397 2336127325707872274810149)
                ·
                  refine ⟨438023873570226051526903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336127325707872274810149 438023873570226051526903)
                  ·
                    rfl

theorem cell22_3838718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_3838718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838718 prefixEnd_3838718 := by exact prefixLift 3838718
  have htrace : WordTrace (prefixWord ++ tailWord_3838718) baseStart_3838718 baseEnd_3838718 := by
    simpa [prefixWord, tailWord_3838718, baseEnd_3838718] using wordTrace_append hprefix tailTrace_3838718
  have hstable : (prefixWord ++ tailWord_3838718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838718).length < 2 ^ (prefixWord ++ tailWord_3838718).sum := by decide
  have hdescent : baseEnd_3838718 < baseStart_3838718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838765 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3838765 : Nat := 118140960795 + 3838765 * 2 ^ 59
def prefixEnd_3838765 : Nat := 4983230072969 + 3 ^ 40 * 3838765 * 2
def baseEnd_3838765 : Nat := 1314087709771185698655565

theorem tailTrace_3838765 : CollatzResearch.WordTrace tailWord_3838765 prefixEnd_3838765 1314087709771185698655565 := by
  unfold tailWord_3838765
  simp only [CollatzResearch.WordTrace]
  refine ⟨140011261937817488711421749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93340841291878325807614499 140011261937817488711421749)
  ·
    refine ⟨13126055806670389566695789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140011261937817488711421749 13126055806670389566695789)
    ·
      refine ⟨4922270927501396087510921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13126055806670389566695789 4922270927501396087510921)
      ·
        refine ⟨3691703195626047065633191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4922270927501396087510921 3691703195626047065633191)
        ·
          refine ⟨5537554793439070598449787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691703195626047065633191 5537554793439070598449787)
          ·
            refine ⟨8306332190158605897674681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5537554793439070598449787 8306332190158605897674681)
            ·
              refine ⟨6229749142618954423256011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8306332190158605897674681 6229749142618954423256011)
              ·
                refine ⟨9344623713928431634884017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229749142618954423256011 9344623713928431634884017)
                ·
                  refine ⟨7008467785446323726163013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9344623713928431634884017 7008467785446323726163013)
                  ·
                    refine ⟨1314087709771185698655565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7008467785446323726163013 1314087709771185698655565)
                    ·
                      rfl

theorem cell22_3838765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3838765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838765 prefixEnd_3838765 := by exact prefixLift 3838765
  have htrace : WordTrace (prefixWord ++ tailWord_3838765) baseStart_3838765 baseEnd_3838765 := by
    simpa [prefixWord, tailWord_3838765, baseEnd_3838765] using wordTrace_append hprefix tailTrace_3838765
  have hstable : (prefixWord ++ tailWord_3838765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838765).length < 2 ^ (prefixWord ++ tailWord_3838765).sum := by decide
  have hdescent : baseEnd_3838765 < baseStart_3838765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838819 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 8]
def baseStart_3838819 : Nat := 118140960795 + 3838819 * 2 ^ 59
def prefixEnd_3838819 : Nat := 4983230072969 + 3 ^ 40 * 3838819 * 2
def baseEnd_3838819 : Nat := 438035398358249185935133

theorem tailTrace_3838819 : CollatzResearch.WordTrace tailWord_3838819 prefixEnd_3838819 438035398358249185935133 := by
  unfold tailWord_3838819
  simp only [CollatzResearch.WordTrace]
  refine ⟨140013231479621855933887511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93342154319747903955925007 140013231479621855933887511)
  ·
    refine ⟨210019847219432783900831267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140013231479621855933887511 210019847219432783900831267)
    ·
      refine ⟨315029770829149175851246901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210019847219432783900831267 315029770829149175851246901)
      ·
        refine ⟨29534041015232735236054397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 315029770829149175851246901 29534041015232735236054397)
        ·
          refine ⟨11075265380712275713520399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29534041015232735236054397 11075265380712275713520399)
          ·
            refine ⟨16612898071068413570280599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11075265380712275713520399 16612898071068413570280599)
            ·
              refine ⟨24919347106602620355420899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16612898071068413570280599 24919347106602620355420899)
              ·
                refine ⟨37379020659903930533131349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24919347106602620355420899 37379020659903930533131349)
                ·
                  refine ⟨438035398358249185935133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37379020659903930533131349 438035398358249185935133)
                  ·
                    rfl

theorem cell22_3838819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 8].length) (baseStart_3838819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838819 prefixEnd_3838819 := by exact prefixLift 3838819
  have htrace : WordTrace (prefixWord ++ tailWord_3838819) baseStart_3838819 baseEnd_3838819 := by
    simpa [prefixWord, tailWord_3838819, baseEnd_3838819] using wordTrace_append hprefix tailTrace_3838819
  have hstable : (prefixWord ++ tailWord_3838819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838819).length < 2 ^ (prefixWord ++ tailWord_3838819).sum := by decide
  have hdescent : baseEnd_3838819 < baseStart_3838819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838851 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 4, 3]
def baseStart_3838851 : Nat := 118140960795 + 3838851 * 2 ^ 59
def prefixEnd_3838851 : Nat := 4983230072969 + 3 ^ 40 * 3838851 * 2
def baseEnd_3838851 : Nat := 1314117149328710141005301

theorem tailTrace_3838851 : CollatzResearch.WordTrace tailWord_3838851 prefixEnd_3838851 1314117149328710141005301 := by
  unfold tailWord_3838851
  simp only [CollatzResearch.WordTrace]
  refine ⟨140014398615505925399052407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93342932410337283599368271 140014398615505925399052407)
  ·
    refine ⟨210021597923258888098578611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140014398615505925399052407 210021597923258888098578611)
    ·
      refine ⟨315032396884888332147867917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210021597923258888098578611 315032396884888332147867917)
      ·
        refine ⟨118137148831833124555450469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315032396884888332147867917 118137148831833124555450469)
        ·
          refine ⟨22150715405968710854146963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118137148831833124555450469 22150715405968710854146963)
          ·
            refine ⟨33226073108953066281220445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22150715405968710854146963 33226073108953066281220445)
            ·
              refine ⟨12459777415857399855457667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33226073108953066281220445 12459777415857399855457667)
              ·
                refine ⟨18689666123786099783186501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12459777415857399855457667 18689666123786099783186501)
                ·
                  refine ⟨3504312398209893709347469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18689666123786099783186501 3504312398209893709347469)
                  ·
                    refine ⟨1314117149328710141005301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504312398209893709347469 1314117149328710141005301)
                    ·
                      rfl

theorem cell22_3838851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 3].length) (baseStart_3838851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838851 prefixEnd_3838851 := by exact prefixLift 3838851
  have htrace : WordTrace (prefixWord ++ tailWord_3838851) baseStart_3838851 baseEnd_3838851 := by
    simpa [prefixWord, tailWord_3838851, baseEnd_3838851] using wordTrace_append hprefix tailTrace_3838851
  have hstable : (prefixWord ++ tailWord_3838851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838851).length < 2 ^ (prefixWord ++ tailWord_3838851).sum := by decide
  have hdescent : baseEnd_3838851 < baseStart_3838851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838870 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3838870 : Nat := 118140960795 + 3838870 * 2 ^ 59
def prefixEnd_3838870 : Nat := 4983230072969 + 3 ^ 40 * 3838870 * 2
def baseEnd_3838870 : Nat := 438041217805666808260081

theorem tailTrace_3838870 : CollatzResearch.WordTrace tailWord_3838870 prefixEnd_3838870 438041217805666808260081 := by
  unfold tailWord_3838870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750943225152318227749629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93343394401624727762662709 8750943225152318227749629)
  ·
    refine ⟨3281603709432119335406111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8750943225152318227749629 3281603709432119335406111)
    ·
      refine ⟨4922405564148179003109167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3281603709432119335406111 4922405564148179003109167)
      ·
        refine ⟨7383608346222268504663751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4922405564148179003109167 7383608346222268504663751)
        ·
          refine ⟨11075412519333402756995627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7383608346222268504663751 11075412519333402756995627)
          ·
            refine ⟨16613118779000104135493441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11075412519333402756995627 16613118779000104135493441)
            ·
              refine ⟨12459839084250078101620081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16613118779000104135493441 12459839084250078101620081)
              ·
                refine ⟨9344879313187558576215061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12459839084250078101620081 9344879313187558576215061)
                ·
                  refine ⟨438041217805666808260081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9344879313187558576215061 438041217805666808260081)
                  ·
                    rfl

theorem cell22_3838870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3838870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838870 prefixEnd_3838870 := by exact prefixLift 3838870
  have htrace : WordTrace (prefixWord ++ tailWord_3838870) baseStart_3838870 baseEnd_3838870 := by
    simpa [prefixWord, tailWord_3838870, baseEnd_3838870] using wordTrace_append hprefix tailTrace_3838870
  have hstable : (prefixWord ++ tailWord_3838870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838870).length < 2 ^ (prefixWord ++ tailWord_3838870).sum := by decide
  have hdescent : baseEnd_3838870 < baseStart_3838870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838881 : List Nat := [1, 2, 3, 4, 1, 2, 1, 8]
def baseStart_3838881 : Nat := 118140960795 + 3838881 * 2 ^ 59
def prefixEnd_3838881 : Nat := 4983230072969 + 3 ^ 40 * 3838881 * 2
def baseEnd_3838881 : Nat := 146014157660200006972801

theorem tailTrace_3838881 : CollatzResearch.WordTrace tailWord_3838881 prefixEnd_3838881 146014157660200006972801 := by
  unfold tailWord_3838881
  simp only [CollatzResearch.WordTrace]
  refine ⟨140015492805397240522644497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93343661870264827015096331 140015492805397240522644497)
  ·
    refine ⟨105011619604047930391983373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140015492805397240522644497 105011619604047930391983373)
    ·
      refine ⟨39379357351517973896993765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105011619604047930391983373 39379357351517973896993765)
      ·
        refine ⟨7383629503409620105686331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39379357351517973896993765 7383629503409620105686331)
        ·
          refine ⟨11075444255114430158529497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7383629503409620105686331 11075444255114430158529497)
          ·
            refine ⟨8306583191335822618897123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11075444255114430158529497 8306583191335822618897123)
            ·
              refine ⟨12459874787003733928345685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8306583191335822618897123 12459874787003733928345685)
              ·
                refine ⟨146014157660200006972801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12459874787003733928345685 146014157660200006972801)
                ·
                  rfl

theorem cell22_3838881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 8].length) (baseStart_3838881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838881 prefixEnd_3838881 := by exact prefixLift 3838881
  have htrace : WordTrace (prefixWord ++ tailWord_3838881) baseStart_3838881 baseEnd_3838881 := by
    simpa [prefixWord, tailWord_3838881, baseEnd_3838881] using wordTrace_append hprefix tailTrace_3838881
  have hstable : (prefixWord ++ tailWord_3838881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838881).length < 2 ^ (prefixWord ++ tailWord_3838881).sum := by decide
  have hdescent : baseEnd_3838881 < baseStart_3838881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838887 : List Nat := [1, 1, 6, 1, 4, 1, 1, 3, 4]
def baseStart_3838887 : Nat := 118140960795 + 3838887 * 2 ^ 59
def prefixEnd_3838887 : Nat := 4983230072969 + 3 ^ 40 * 3838887 * 2
def baseEnd_3838887 : Nat := 438043157621472682368397

theorem tailTrace_3838887 : CollatzResearch.WordTrace tailWord_3838887 prefixEnd_3838887 438043157621472682368397 := by
  unfold tailWord_3838887
  simp only [CollatzResearch.WordTrace]
  refine ⟨140015711643375503547362915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93343807762250335698241943 140015711643375503547362915)
  ·
    refine ⟨210023567465063255321044373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140015711643375503547362915 210023567465063255321044373)
    ·
      refine ⟨9844854724924840093173955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210023567465063255321044373 9844854724924840093173955)
      ·
        refine ⟨14767282087387260139760933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9844854724924840093173955 14767282087387260139760933)
        ·
          refine ⟨2768865391385111276205175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14767282087387260139760933 2768865391385111276205175)
          ·
            refine ⟨4153298087077666914307763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768865391385111276205175 4153298087077666914307763)
            ·
              refine ⟨6229947130616500371461645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153298087077666914307763 6229947130616500371461645)
              ·
                refine ⟨2336230173981187639298117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6229947130616500371461645 2336230173981187639298117)
                ·
                  refine ⟨438043157621472682368397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336230173981187639298117 438043157621472682368397)
                  ·
                    rfl

theorem cell22_3838887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 4].length) (baseStart_3838887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838887 prefixEnd_3838887 := by exact prefixLift 3838887
  have htrace : WordTrace (prefixWord ++ tailWord_3838887) baseStart_3838887 baseEnd_3838887 := by
    simpa [prefixWord, tailWord_3838887, baseEnd_3838887] using wordTrace_append hprefix tailTrace_3838887
  have hstable : (prefixWord ++ tailWord_3838887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838887).length < 2 ^ (prefixWord ++ tailWord_3838887).sum := by decide
  have hdescent : baseEnd_3838887 < baseStart_3838887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838900 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3838900 : Nat := 118140960795 + 3838900 * 2 ^ 59
def prefixEnd_3838900 : Nat := 4983230072969 + 3 ^ 40 * 3838900 * 2
def baseEnd_3838900 : Nat := 1314133923030090346530151

theorem tailTrace_3838900 : CollatzResearch.WordTrace tailWord_3838900 prefixEnd_3838900 1314133923030090346530151 := by
  unfold tailWord_3838900
  simp only [CollatzResearch.WordTrace]
  refine ⟨70008092896164203383793077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93344123861552271178390769 70008092896164203383793077)
  ·
    refine ⟨6563258709015394067230601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70008092896164203383793077 6563258709015394067230601)
    ·
      refine ⟨4922444031761545550422951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6563258709015394067230601 4922444031761545550422951)
      ·
        refine ⟨7383666047642318325634427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4922444031761545550422951 7383666047642318325634427)
        ·
          refine ⟨11075499071463477488451641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7383666047642318325634427 11075499071463477488451641)
          ·
            refine ⟨8306624303597608116338731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11075499071463477488451641 8306624303597608116338731)
            ·
              refine ⟨12459936455396412174508097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8306624303597608116338731 12459936455396412174508097)
              ·
                refine ⟨9344952341547309130881073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12459936455396412174508097 9344952341547309130881073)
                ·
                  refine ⟨7008714256160481848160805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9344952341547309130881073 7008714256160481848160805)
                  ·
                    refine ⟨1314133923030090346530151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7008714256160481848160805 1314133923030090346530151)
                    ·
                      rfl

theorem cell22_3838900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3838900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3838900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3838900 prefixEnd_3838900 := by exact prefixLift 3838900
  have htrace : WordTrace (prefixWord ++ tailWord_3838900) baseStart_3838900 baseEnd_3838900 := by
    simpa [prefixWord, tailWord_3838900, baseEnd_3838900] using wordTrace_append hprefix tailTrace_3838900
  have hstable : (prefixWord ++ tailWord_3838900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838900).length < 2 ^ (prefixWord ++ tailWord_3838900).sum := by decide
  have hdescent : baseEnd_3838900 < baseStart_3838900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839037 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_3839037 : Nat := 118140960795 + 3839037 * 2 ^ 59
def prefixEnd_3839037 : Nat := 4983230072969 + 3 ^ 40 * 3839037 * 2
def baseEnd_3839037 : Nat := 1314180820929867655854731

theorem tailTrace_3839037 : CollatzResearch.WordTrace tailWord_3839037 prefixEnd_3839037 1314180820929867655854731 := by
  unfold tailWord_3839037
  simp only [CollatzResearch.WordTrace]
  refine ⟨140021182592832079165323365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93347455061888052776882243 140021182592832079165323365)
  ·
    refine ⟨26253971736156014843498131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140021182592832079165323365 26253971736156014843498131)
    ·
      refine ⟨39380957604234022265247197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26253971736156014843498131 39380957604234022265247197)
      ·
        refine ⟨14767859101587758349467699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39380957604234022265247197 14767859101587758349467699)
        ·
          refine ⟨22151788652381637524201549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14767859101587758349467699 22151788652381637524201549)
          ·
            refine ⟨8306920744643114071575581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22151788652381637524201549 8306920744643114071575581)
            ·
              refine ⟨3115095279241167776840843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8306920744643114071575581 3115095279241167776840843)
              ·
                refine ⟨4672642918861751665261265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115095279241167776840843 4672642918861751665261265)
                ·
                  refine ⟨3504482189146313748945949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4672642918861751665261265 3504482189146313748945949)
                  ·
                    refine ⟨1314180820929867655854731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504482189146313748945949 1314180820929867655854731)
                    ·
                      rfl

theorem cell22_3839037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_3839037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839037 prefixEnd_3839037 := by exact prefixLift 3839037
  have htrace : WordTrace (prefixWord ++ tailWord_3839037) baseStart_3839037 baseEnd_3839037 := by
    simpa [prefixWord, tailWord_3839037, baseEnd_3839037] using wordTrace_append hprefix tailTrace_3839037
  have hstable : (prefixWord ++ tailWord_3839037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839037).length < 2 ^ (prefixWord ++ tailWord_3839037).sum := by decide
  have hdescent : baseEnd_3839037 < baseStart_3839037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839048 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 3, 3]
def baseStart_3839048 : Nat := 118140960795 + 3839048 * 2 ^ 59
def prefixEnd_3839048 : Nat := 4983230072969 + 3 ^ 40 * 3839048 * 2
def baseEnd_3839048 : Nat := 1314184586454667293829697

theorem tailTrace_3839048 : CollatzResearch.WordTrace tailWord_3839048 prefixEnd_3839048 1314184586454667293829697 := by
  unfold tailWord_3839048
  simp only [CollatzResearch.WordTrace]
  refine ⟨70010791897896114021986899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93347722530528152029315865 70010791897896114021986899)
  ·
    refine ⟨105016187846844171032980349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70010791897896114021986899 105016187846844171032980349)
    ·
      refine ⟨39381070442566564137367631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105016187846844171032980349 39381070442566564137367631)
      ·
        refine ⟨59071605663849846206051447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39381070442566564137367631 59071605663849846206051447)
        ·
          refine ⟨88607408495774769309077171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59071605663849846206051447 88607408495774769309077171)
          ·
            refine ⟨132911112743662153963615757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88607408495774769309077171 132911112743662153963615757)
            ·
              refine ⟨49841667278873307736355909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132911112743662153963615757 49841667278873307736355909)
              ·
                refine ⟨9345312614788745200566733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49841667278873307736355909 9345312614788745200566733)
                ·
                  refine ⟨3504492230545779450212525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9345312614788745200566733 3504492230545779450212525)
                  ·
                    refine ⟨1314184586454667293829697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504492230545779450212525 1314184586454667293829697)
                    ·
                      rfl

theorem cell22_3839048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_3839048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839048 prefixEnd_3839048 := by exact prefixLift 3839048
  have htrace : WordTrace (prefixWord ++ tailWord_3839048) baseStart_3839048 baseEnd_3839048 := by
    simpa [prefixWord, tailWord_3839048, baseEnd_3839048] using wordTrace_append hprefix tailTrace_3839048
  have hstable : (prefixWord ++ tailWord_3839048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839048).length < 2 ^ (prefixWord ++ tailWord_3839048).sum := by decide
  have hdescent : baseEnd_3839048 < baseStart_3839048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839061 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 9]
def baseStart_3839061 : Nat := 118140960795 + 3839061 * 2 ^ 59
def prefixEnd_3839061 : Nat := 4983230072969 + 3 ^ 40 * 3839061 * 2
def baseEnd_3839061 : Nat := 438063012206779864418219

theorem tailTrace_3839061 : CollatzResearch.WordTrace tailWord_3839061 prefixEnd_3839061 438063012206779864418219 := by
  unfold tailWord_3839061
  simp only [CollatzResearch.WordTrace]
  refine ⟨140022057944745131264197037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93348038629830087509464691 140022057944745131264197037)
  ·
    refine ⟨52508271729279424224073889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140022057944745131264197037 52508271729279424224073889)
    ·
      refine ⟨39381203796959568168055417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52508271729279424224073889 39381203796959568168055417)
      ·
        refine ⟨29535902847719676126041563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39381203796959568168055417 29535902847719676126041563)
        ·
          refine ⟨44303854271579514189062345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29535902847719676126041563 44303854271579514189062345)
          ·
            refine ⟨33227890703684635641796759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44303854271579514189062345 33227890703684635641796759)
            ·
              refine ⟨49841836055526953462695139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33227890703684635641796759 49841836055526953462695139)
              ·
                refine ⟨74762754083290430194042709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49841836055526953462695139 74762754083290430194042709)
                ·
                  refine ⟨438063012206779864418219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74762754083290430194042709 438063012206779864418219)
                  ·
                    rfl

theorem cell22_3839061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_3839061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839061 prefixEnd_3839061 := by exact prefixLift 3839061
  have htrace : WordTrace (prefixWord ++ tailWord_3839061) baseStart_3839061 baseEnd_3839061 := by
    simpa [prefixWord, tailWord_3839061, baseEnd_3839061] using wordTrace_append hprefix tailTrace_3839061
  have hstable : (prefixWord ++ tailWord_3839061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839061).length < 2 ^ (prefixWord ++ tailWord_3839061).sum := by decide
  have hdescent : baseEnd_3839061 < baseStart_3839061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839065 : List Nat := [1, 2, 1, 2, 2, 1, 2, 7, 1, 3]
def baseStart_3839065 : Nat := 118140960795 + 3839065 * 2 ^ 59
def prefixEnd_3839065 : Nat := 4983230072969 + 3 ^ 40 * 3839065 * 2
def baseEnd_3839065 : Nat := 1314190405902084916154645

theorem tailTrace_3839065 : CollatzResearch.WordTrace tailWord_3839065 prefixEnd_3839065 1314190405902084916154645 := by
  unfold tailWord_3839065
  simp only [CollatzResearch.WordTrace]
  refine ⟨140022203836730639947342649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93348135891153759964895099 140022203836730639947342649)
  ·
    refine ⟨105016652877547979960506987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140022203836730639947342649 105016652877547979960506987)
    ·
      refine ⟨157524979316321969940760481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105016652877547979960506987 157524979316321969940760481)
      ·
        refine ⟨118143734487241477455570361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157524979316321969940760481 118143734487241477455570361)
        ·
          refine ⟨88607800865431108091677771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118143734487241477455570361 88607800865431108091677771)
          ·
            refine ⟨132911701298146662137516657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88607800865431108091677771 132911701298146662137516657)
            ·
              refine ⟨99683775973609996603137493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132911701298146662137516657 99683775973609996603137493)
              ·
                refine ⟨2336338499381484295386035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 99683775973609996603137493 2336338499381484295386035)
                ·
                  refine ⟨3504507749072226443079053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336338499381484295386035 3504507749072226443079053)
                  ·
                    refine ⟨1314190405902084916154645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504507749072226443079053 1314190405902084916154645)
                    ·
                      rfl

theorem cell22_3839065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 1, 3].length) (baseStart_3839065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839065 prefixEnd_3839065 := by exact prefixLift 3839065
  have htrace : WordTrace (prefixWord ++ tailWord_3839065) baseStart_3839065 baseEnd_3839065 := by
    simpa [prefixWord, tailWord_3839065, baseEnd_3839065] using wordTrace_append hprefix tailTrace_3839065
  have hstable : (prefixWord ++ tailWord_3839065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839065).length < 2 ^ (prefixWord ++ tailWord_3839065).sum := by decide
  have hdescent : baseEnd_3839065 < baseStart_3839065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839082 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 3, 3]
def baseStart_3839082 : Nat := 118140960795 + 3839082 * 2 ^ 59
def prefixEnd_3839082 : Nat := 4983230072969 + 3 ^ 40 * 3839082 * 2
def baseEnd_3839082 : Nat := 1314196225349502538479593

theorem tailTrace_3839082 : CollatzResearch.WordTrace tailWord_3839082 prefixEnd_3839082 1314196225349502538479593 := by
  unfold tailWord_3839082
  simp only [CollatzResearch.WordTrace]
  refine ⟨35005705969417262962677875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93348549251779367900474333 35005705969417262962677875)
  ·
    refine ⟨52508558954125894444016813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35005705969417262962677875 52508558954125894444016813)
    ·
      refine ⟨19690709607797210416506305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52508558954125894444016813 19690709607797210416506305)
      ·
        refine ⟨14768032205847907812379729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19690709607797210416506305 14768032205847907812379729)
        ·
          refine ⟨11076024154385930859284797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14768032205847907812379729 11076024154385930859284797)
          ·
            refine ⟨4153509057894724072231799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11076024154385930859284797 4153509057894724072231799)
            ·
              refine ⟨6230263586842086108347699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153509057894724072231799 6230263586842086108347699)
              ·
                refine ⟨9345395380263129162521549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230263586842086108347699 9345395380263129162521549)
                ·
                  refine ⟨3504523267598673435945581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9345395380263129162521549 3504523267598673435945581)
                  ·
                    refine ⟨1314196225349502538479593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504523267598673435945581 1314196225349502538479593)
                    ·
                      rfl

theorem cell22_3839082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_3839082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839082 prefixEnd_3839082 := by exact prefixLift 3839082
  have htrace : WordTrace (prefixWord ++ tailWord_3839082) baseStart_3839082 baseEnd_3839082 := by
    simpa [prefixWord, tailWord_3839082, baseEnd_3839082] using wordTrace_append hprefix tailTrace_3839082
  have hstable : (prefixWord ++ tailWord_3839082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839082).length < 2 ^ (prefixWord ++ tailWord_3839082).sum := by decide
  have hdescent : baseEnd_3839082 < baseStart_3839082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839155 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 2, 3]
def baseStart_3839155 : Nat := 118140960795 + 3839155 * 2 ^ 59
def prefixEnd_3839155 : Nat := 4983230072969 + 3 ^ 40 * 3839155 * 2
def baseEnd_3839155 : Nat := 1314221214741354681404369

theorem tailTrace_3839155 : CollatzResearch.WordTrace tailWord_3839155 prefixEnd_3839155 1314221214741354681404369 := by
  unfold tailWord_3839155
  simp only [CollatzResearch.WordTrace]
  refine ⟨140025486406404585318118919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93350324270936390212079279 140025486406404585318118919)
  ·
    refine ⟨210038229609606877977178379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140025486406404585318118919 210038229609606877977178379)
    ·
      refine ⟨315057344414410316965767569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210038229609606877977178379 315057344414410316965767569)
      ·
        refine ⟨236293008310807737724325677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315057344414410316965767569 236293008310807737724325677)
        ·
          refine ⟨88609878116552901646622129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236293008310807737724325677 88609878116552901646622129)
          ·
            refine ⟨66457408587414676234966597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88609878116552901646622129 66457408587414676234966597)
            ·
              refine ⟨12460764110140251794056237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66457408587414676234966597 12460764110140251794056237)
              ·
                refine ⟨4672786541302594422771089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12460764110140251794056237 4672786541302594422771089)
                ·
                  refine ⟨3504589905976945817078317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4672786541302594422771089 3504589905976945817078317)
                  ·
                    refine ⟨1314221214741354681404369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504589905976945817078317 1314221214741354681404369)
                    ·
                      rfl

theorem cell22_3839155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 3].length) (baseStart_3839155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839155 prefixEnd_3839155 := by exact prefixLift 3839155
  have htrace : WordTrace (prefixWord ++ tailWord_3839155) baseStart_3839155 baseEnd_3839155 := by
    simpa [prefixWord, tailWord_3839155, baseEnd_3839155] using wordTrace_append hprefix tailTrace_3839155
  have hstable : (prefixWord ++ tailWord_3839155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839155).length < 2 ^ (prefixWord ++ tailWord_3839155).sum := by decide
  have hdescent : baseEnd_3839155 < baseStart_3839155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839189 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 2, 3]
def baseStart_3839189 : Nat := 118140960795 + 3839189 * 2 ^ 59
def prefixEnd_3839189 : Nat := 4983230072969 + 3 ^ 40 * 3839189 * 2
def baseEnd_3839189 : Nat := 1314232853636189926054265

theorem tailTrace_3839189 : CollatzResearch.WordTrace tailWord_3839189 prefixEnd_3839189 1314232853636189926054265 := by
  unfold tailWord_3839189
  simp only [CollatzResearch.WordTrace]
  refine ⟨140026726488281409124856621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93351150992187606083237747 140026726488281409124856621)
  ·
    refine ⟨52510022433105528421821233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140026726488281409124856621 52510022433105528421821233)
    ·
      refine ⟨39382516824829146316365925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52510022433105528421821233 39382516824829146316365925)
      ·
        refine ⟨7384221904655464934318611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39382516824829146316365925 7384221904655464934318611)
        ·
          refine ⟨11076332856983197401477917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7384221904655464934318611 11076332856983197401477917)
          ·
            refine ⟨4153624821368699025554219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11076332856983197401477917 4153624821368699025554219)
            ·
              refine ⟨6230437232053048538331329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153624821368699025554219 6230437232053048538331329)
              ·
                refine ⟨4672827924039786403748497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6230437232053048538331329 4672827924039786403748497)
                ·
                  refine ⟨3504620943029839802811373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4672827924039786403748497 3504620943029839802811373)
                  ·
                    refine ⟨1314232853636189926054265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504620943029839802811373 1314232853636189926054265)
                    ·
                      rfl

theorem cell22_3839189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_3839189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839189 prefixEnd_3839189 := by exact prefixLift 3839189
  have htrace : WordTrace (prefixWord ++ tailWord_3839189) baseStart_3839189 baseEnd_3839189 := by
    simpa [prefixWord, tailWord_3839189, baseEnd_3839189] using wordTrace_append hprefix tailTrace_3839189
  have hstable : (prefixWord ++ tailWord_3839189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839189).length < 2 ^ (prefixWord ++ tailWord_3839189).sum := by decide
  have hdescent : baseEnd_3839189 < baseStart_3839189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839200 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 3, 3]
def baseStart_3839200 : Nat := 118140960795 + 3839200 * 2 ^ 59
def prefixEnd_3839200 : Nat := 4983230072969 + 3 ^ 40 * 3839200 * 2
def baseEnd_3839200 : Nat := 1314236619160989564029231

theorem tailTrace_3839200 : CollatzResearch.WordTrace tailWord_3839200 prefixEnd_3839200 1314236619160989564029231 := by
  unfold tailWord_3839200
  simp only [CollatzResearch.WordTrace]
  refine ⟨70013563845620779001753527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93351418460827705335671369 70013563845620779001753527)
  ·
    refine ⟨105020345768431168502630291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70013563845620779001753527 105020345768431168502630291)
    ·
      refine ⟨157530518652646752753945437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105020345768431168502630291 157530518652646752753945437)
      ·
        refine ⟨59073944494742532282729539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157530518652646752753945437 59073944494742532282729539)
        ·
          refine ⟨88610916742113798424094309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59073944494742532282729539 88610916742113798424094309)
          ·
            refine ⟨16614546889146337204517683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88610916742113798424094309 16614546889146337204517683)
            ·
              refine ⟨24921820333719505806776525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16614546889146337204517683 24921820333719505806776525)
              ·
                refine ⟨9345682625144814677541197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24921820333719505806776525 9345682625144814677541197)
                ·
                  refine ⟨3504630984429305504077949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9345682625144814677541197 3504630984429305504077949)
                  ·
                    refine ⟨1314236619160989564029231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504630984429305504077949 1314236619160989564029231)
                    ·
                      rfl

theorem cell22_3839200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3, 3].length) (baseStart_3839200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839200 prefixEnd_3839200 := by exact prefixLift 3839200
  have htrace : WordTrace (prefixWord ++ tailWord_3839200) baseStart_3839200 baseEnd_3839200 := by
    simpa [prefixWord, tailWord_3839200, baseEnd_3839200] using wordTrace_append hprefix tailTrace_3839200
  have hstable : (prefixWord ++ tailWord_3839200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839200).length < 2 ^ (prefixWord ++ tailWord_3839200).sum := by decide
  have hdescent : baseEnd_3839200 < baseStart_3839200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839230 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_3839230 : Nat := 118140960795 + 3839230 * 2 ^ 59
def prefixEnd_3839230 : Nat := 4983230072969 + 3 ^ 40 * 3839230 * 2
def baseEnd_3839230 : Nat := 438082296258026495259713

theorem tailTrace_3839230 : CollatzResearch.WordTrace tailWord_3839230 prefixEnd_3839230 438082296258026495259713 := by
  unfold tailWord_3839230
  simp only [CollatzResearch.WordTrace]
  refine ⟨17503527735141609140887393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93352147920755248751399429 17503527735141609140887393)
  ·
    refine ⟨13127645801356206855665545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17503527735141609140887393 13127645801356206855665545)
    ·
      refine ⟨9845734351017155141749159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13127645801356206855665545 9845734351017155141749159)
      ·
        refine ⟨14768601526525732712623739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9845734351017155141749159 14768601526525732712623739)
        ·
          refine ⟨22152902289788599068935609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14768601526525732712623739 22152902289788599068935609)
          ·
            refine ⟨16614676717341449301701707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22152902289788599068935609 16614676717341449301701707)
            ·
              refine ⟨24922015076012173952552561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16614676717341449301701707 24922015076012173952552561)
              ·
                refine ⟨18691511307009130464414421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24922015076012173952552561 18691511307009130464414421)
                ·
                  refine ⟨438082296258026495259713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18691511307009130464414421 438082296258026495259713)
                  ·
                    rfl

theorem cell22_3839230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_3839230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839230 prefixEnd_3839230 := by exact prefixLift 3839230
  have htrace : WordTrace (prefixWord ++ tailWord_3839230) baseStart_3839230 baseEnd_3839230 := by
    simpa [prefixWord, tailWord_3839230, baseEnd_3839230] using wordTrace_append hprefix tailTrace_3839230
  have hstable : (prefixWord ++ tailWord_3839230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839230).length < 2 ^ (prefixWord ++ tailWord_3839230).sum := by decide
  have hdescent : baseEnd_3839230 < baseStart_3839230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839264 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 5]
def baseStart_3839264 : Nat := 118140960795 + 3839264 * 2 ^ 59
def prefixEnd_3839264 : Nat := 4983230072969 + 3 ^ 40 * 3839264 * 2
def baseEnd_3839264 : Nat := 438086175889638243476345

theorem tailTrace_3839264 : CollatzResearch.WordTrace tailWord_3839264 prefixEnd_3839264 438086175889638243476345 := by
  unfold tailWord_3839264
  simp only [CollatzResearch.WordTrace]
  refine ⟨70014730981504848466918423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93352974642006464622557897 70014730981504848466918423)
  ·
    refine ⟨105022096472257272700377635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70014730981504848466918423 105022096472257272700377635)
    ·
      refine ⟨157533144708385909050566453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105022096472257272700377635 157533144708385909050566453)
      ·
        refine ⟨14768732316411178973490605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157533144708385909050566453 14768732316411178973490605)
        ·
          refine ⟨5538274618654192115058977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14768732316411178973490605 5538274618654192115058977)
          ·
            refine ⟨4153705963990644086294233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5538274618654192115058977 4153705963990644086294233)
            ·
              refine ⟨3115279472992983064720675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4153705963990644086294233 3115279472992983064720675)
              ·
                refine ⟨4672919209489474597081013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115279472992983064720675 4672919209489474597081013)
                ·
                  refine ⟨438086175889638243476345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4672919209489474597081013 438086175889638243476345)
                  ·
                    rfl

theorem cell22_3839264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 5].length) (baseStart_3839264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839264 prefixEnd_3839264 := by exact prefixLift 3839264
  have htrace : WordTrace (prefixWord ++ tailWord_3839264) baseStart_3839264 baseEnd_3839264 := by
    simpa [prefixWord, tailWord_3839264, baseEnd_3839264] using wordTrace_append hprefix tailTrace_3839264
  have hstable : (prefixWord ++ tailWord_3839264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839264).length < 2 ^ (prefixWord ++ tailWord_3839264).sum := by decide
  have hdescent : baseEnd_3839264 < baseStart_3839264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839290 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_3839290 : Nat := 118140960795 + 3839290 * 2 ^ 59
def prefixEnd_3839290 : Nat := 4983230072969 + 3 ^ 40 * 3839290 * 2
def baseEnd_3839290 : Nat := 1314267428000259329278955

theorem tailTrace_3839290 : CollatzResearch.WordTrace tailWord_3839290 prefixEnd_3839290 1314267428000259329278955 := by
  unfold tailWord_3839290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35007602565228875843570831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93353606840610335582855549 35007602565228875843570831)
  ·
    refine ⟨52511403847843313765356247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35007602565228875843570831 52511403847843313765356247)
    ·
      refine ⟨78767105771764970648034371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52511403847843313765356247 78767105771764970648034371)
      ·
        refine ⟨118150658657647455972051557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78767105771764970648034371 118150658657647455972051557)
        ·
          refine ⟨22153248498308897994759667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118150658657647455972051557 22153248498308897994759667)
          ·
            refine ⟨33229872747463346992139501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22153248498308897994759667 33229872747463346992139501)
            ·
              refine ⟨12461202280298755122052313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33229872747463346992139501 12461202280298755122052313)
              ·
                refine ⟨9345901710224066341539235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12461202280298755122052313 9345901710224066341539235)
                ·
                  refine ⟨14018852565336099512308853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9345901710224066341539235 14018852565336099512308853)
                  ·
                    refine ⟨1314267428000259329278955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14018852565336099512308853 1314267428000259329278955)
                    ·
                      rfl

theorem cell22_3839290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_3839290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839290 prefixEnd_3839290 := by exact prefixLift 3839290
  have htrace : WordTrace (prefixWord ++ tailWord_3839290) baseStart_3839290 baseEnd_3839290 := by
    simpa [prefixWord, tailWord_3839290, baseEnd_3839290] using wordTrace_append hprefix tailTrace_3839290
  have hstable : (prefixWord ++ tailWord_3839290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839290).length < 2 ^ (prefixWord ++ tailWord_3839290).sum := by decide
  have hdescent : baseEnd_3839290 < baseStart_3839290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839294 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3839294 : Nat := 118140960795 + 3839294 * 2 ^ 59
def prefixEnd_3839294 : Nat := 4983230072969 + 3 ^ 40 * 3839294 * 2
def baseEnd_3839294 : Nat := 1314268797282004652178943

theorem tailTrace_3839294 : CollatzResearch.WordTrace tailWord_3839294 prefixEnd_3839294 1314268797282004652178943 := by
  unfold tailWord_3839294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17503819519112626507178617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93353704101934008038285957 17503819519112626507178617)
  ·
    refine ⟨13127864639334469880383963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17503819519112626507178617 13127864639334469880383963)
    ·
      refine ⟨19691796959001704820575945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13127864639334469880383963 19691796959001704820575945)
      ·
        refine ⟨14768847719251278615431959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19691796959001704820575945 14768847719251278615431959)
        ·
          refine ⟨22153271578876917923147939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14768847719251278615431959 22153271578876917923147939)
          ·
            refine ⟨33229907368315376884721909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22153271578876917923147939 33229907368315376884721909)
            ·
              refine ⟨3115303815779566582942679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33229907368315376884721909 3115303815779566582942679)
              ·
                refine ⟨4672955723669349874414019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115303815779566582942679 4672955723669349874414019)
                ·
                  refine ⟨7009433585504024811621029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4672955723669349874414019 7009433585504024811621029)
                  ·
                    refine ⟨1314268797282004652178943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009433585504024811621029 1314268797282004652178943)
                    ·
                      rfl

theorem cell22_3839294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3839294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839294 prefixEnd_3839294 := by exact prefixLift 3839294
  have htrace : WordTrace (prefixWord ++ tailWord_3839294) baseStart_3839294 baseEnd_3839294 := by
    simpa [prefixWord, tailWord_3839294, baseEnd_3839294] using wordTrace_append hprefix tailTrace_3839294
  have hstable : (prefixWord ++ tailWord_3839294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839294).length < 2 ^ (prefixWord ++ tailWord_3839294).sum := by decide
  have hdescent : baseEnd_3839294 < baseStart_3839294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839302 : List Nat := [6, 1, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3839302 : Nat := 118140960795 + 3839302 * 2 ^ 59
def prefixEnd_3839302 : Nat := 4983230072969 + 3 ^ 40 * 3839302 * 2
def baseEnd_3839302 : Nat := 1314271535845495297978919

theorem tailTrace_3839302 : CollatzResearch.WordTrace tailWord_3839302 prefixEnd_3839302 1314271535845495297978919 := by
  unfold tailWord_3839302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375963998027250919491255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93353898624581352949146773 4375963998027250919491255)
  ·
    refine ⟨6563945997040876379236883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4375963998027250919491255 6563945997040876379236883)
    ·
      refine ⟨9845918995561314568855325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6563945997040876379236883 9845918995561314568855325)
      ·
        refine ⟨3692219623335492963320747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9845918995561314568855325 3692219623335492963320747)
        ·
          refine ⟨5538329435003239444981121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692219623335492963320747 5538329435003239444981121)
          ·
            refine ⟨4153747076252429583735841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5538329435003239444981121 4153747076252429583735841)
            ·
              refine ⟨3115310307189322187801881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4153747076252429583735841 3115310307189322187801881)
              ·
                refine ⟨2336482730391991640851411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3115310307189322187801881 2336482730391991640851411)
                ·
                  refine ⟨3504724095587987461277117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336482730391991640851411 3504724095587987461277117)
                  ·
                    refine ⟨1314271535845495297978919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504724095587987461277117 1314271535845495297978919)
                    ·
                      rfl

theorem cell22_3839302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3839302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839302 prefixEnd_3839302 := by exact prefixLift 3839302
  have htrace : WordTrace (prefixWord ++ tailWord_3839302) baseStart_3839302 baseEnd_3839302 := by
    simpa [prefixWord, tailWord_3839302, baseEnd_3839302] using wordTrace_append hprefix tailTrace_3839302
  have hstable : (prefixWord ++ tailWord_3839302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839302).length < 2 ^ (prefixWord ++ tailWord_3839302).sum := by decide
  have hdescent : baseEnd_3839302 < baseStart_3839302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839303 : List Nat := [1, 1, 4, 1, 2, 13]
def baseStart_3839303 : Nat := 118140960795 + 3839303 * 2 ^ 59
def prefixEnd_3839303 : Nat := 4983230072969 + 3 ^ 40 * 3839303 * 2
def baseEnd_3839303 : Nat := 16225578742789279366715

theorem tailTrace_3839303 : CollatzResearch.WordTrace tailWord_3839303 prefixEnd_3839303 16225578742789279366715 := by
  unfold tailWord_3839303
  simp only [CollatzResearch.WordTrace]
  refine ⟨140030884409868406594506563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93353922939912271063004375 140030884409868406594506563)
  ·
    refine ⟨210046326614802609891759845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140030884409868406594506563 210046326614802609891759845)
    ·
      refine ⟨39383686240275489354704971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210046326614802609891759845 39383686240275489354704971)
      ·
        refine ⟨59075529360413234032057457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39383686240275489354704971 59075529360413234032057457)
        ·
          refine ⟨44306647020309925524043093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59075529360413234032057457 44306647020309925524043093)
          ·
            refine ⟨16225578742789279366715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 44306647020309925524043093 16225578742789279366715)
            ·
              rfl

theorem cell22_3839303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 13].length) (baseStart_3839303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839303 prefixEnd_3839303 := by exact prefixLift 3839303
  have htrace : WordTrace (prefixWord ++ tailWord_3839303) baseStart_3839303 baseEnd_3839303 := by
    simpa [prefixWord, tailWord_3839303, baseEnd_3839303] using wordTrace_append hprefix tailTrace_3839303
  have hstable : (prefixWord ++ tailWord_3839303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839303).length < 2 ^ (prefixWord ++ tailWord_3839303).sum := by decide
  have hdescent : baseEnd_3839303 < baseStart_3839303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839305 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_3839305 : Nat := 118140960795 + 3839305 * 2 ^ 59
def prefixEnd_3839305 : Nat := 4983230072969 + 3 ^ 40 * 3839305 * 2
def baseEnd_3839305 : Nat := 1314272562806804290153909

theorem tailTrace_3839305 : CollatzResearch.WordTrace tailWord_3839305 prefixEnd_3839305 1314272562806804290153909 := by
  unfold tailWord_3839305
  simp only [CollatzResearch.WordTrace]
  refine ⟨140030957355861160936079369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93353971570574107290719579 140030957355861160936079369)
  ·
    refine ⟨105023218016895870702059527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140030957355861160936079369 105023218016895870702059527)
    ·
      refine ⟨157534827025343806053089291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105023218016895870702059527 157534827025343806053089291)
      ·
        refine ⟨236302240538015709079633937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157534827025343806053089291 236302240538015709079633937)
        ·
          refine ⟨177226680403511781809725453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236302240538015709079633937 177226680403511781809725453)
          ·
            refine ⟨66460005151316918178647045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177226680403511781809725453 66460005151316918178647045)
            ·
              refine ⟨12461250965871922158496321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66460005151316918178647045 12461250965871922158496321)
              ·
                refine ⟨9345938224403941618872241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12461250965871922158496321 9345938224403941618872241)
                ·
                  refine ⟨7009453668302956214154181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9345938224403941618872241 7009453668302956214154181)
                  ·
                    refine ⟨1314272562806804290153909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009453668302956214154181 1314272562806804290153909)
                    ·
                      rfl

theorem cell22_3839305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_3839305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839305 prefixEnd_3839305 := by exact prefixLift 3839305
  have htrace : WordTrace (prefixWord ++ tailWord_3839305) baseStart_3839305 baseEnd_3839305 := by
    simpa [prefixWord, tailWord_3839305, baseEnd_3839305] using wordTrace_append hprefix tailTrace_3839305
  have hstable : (prefixWord ++ tailWord_3839305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839305).length < 2 ^ (prefixWord ++ tailWord_3839305).sum := by decide
  have hdescent : baseEnd_3839305 < baseStart_3839305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839369 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 3, 3]
def baseStart_3839369 : Nat := 118140960795 + 3839369 * 2 ^ 59
def prefixEnd_3839369 : Nat := 4983230072969 + 3 ^ 40 * 3839369 * 2
def baseEnd_3839369 : Nat := 1314294471314729456553713

theorem tailTrace_3839369 : CollatzResearch.WordTrace tailWord_3839369 prefixEnd_3839369 1314294471314729456553713 := by
  unfold tailWord_3839369
  simp only [CollatzResearch.WordTrace]
  refine ⟨140033291627629299866409161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93355527751752866577606107 140033291627629299866409161)
  ·
    refine ⟨105024968720721974899806871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140033291627629299866409161 105024968720721974899806871)
    ·
      refine ⟨157537453081082962349710307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105024968720721974899806871 157537453081082962349710307)
      ·
        refine ⟨236306179621624443524565461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157537453081082962349710307 236306179621624443524565461)
        ·
          refine ⟨5538426084881822895107003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 236306179621624443524565461 5538426084881822895107003)
          ·
            refine ⟨8307639127322734342660505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5538426084881822895107003 8307639127322734342660505)
            ·
              refine ⟨6230729345492050756995379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8307639127322734342660505 6230729345492050756995379)
              ·
                refine ⟨9346094018238076135493069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230729345492050756995379 9346094018238076135493069)
                ·
                  refine ⟨3504785256839278550809901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9346094018238076135493069 3504785256839278550809901)
                  ·
                    refine ⟨1314294471314729456553713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504785256839278550809901 1314294471314729456553713)
                    ·
                      rfl

theorem cell22_3839369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 3].length) (baseStart_3839369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839369 prefixEnd_3839369 := by exact prefixLift 3839369
  have htrace : WordTrace (prefixWord ++ tailWord_3839369) baseStart_3839369 baseEnd_3839369 := by
    simpa [prefixWord, tailWord_3839369, baseEnd_3839369] using wordTrace_append hprefix tailTrace_3839369
  have hstable : (prefixWord ++ tailWord_3839369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839369).length < 2 ^ (prefixWord ++ tailWord_3839369).sum := by decide
  have hdescent : baseEnd_3839369 < baseStart_3839369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839427 : List Nat := [1, 1, 1, 3, 1, 1, 4, 6, 4]
def baseStart_3839427 : Nat := 118140960795 + 3839427 * 2 ^ 59
def prefixEnd_3839427 : Nat := 4983230072969 + 3 ^ 40 * 3839427 * 2
def baseEnd_3839427 : Nat := 438104775300012212867845

theorem tailTrace_3839427 : CollatzResearch.WordTrace tailWord_3839427 prefixEnd_3839427 438104775300012212867845 := by
  unfold tailWord_3839427
  simp only [CollatzResearch.WordTrace]
  refine ⟨140035407061419175772020535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93356938040946117181347023 140035407061419175772020535)
  ·
    refine ⟨210053110592128763658030803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140035407061419175772020535 210053110592128763658030803)
    ·
      refine ⟨315079665888193145487046205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210053110592128763658030803 315079665888193145487046205)
      ·
        refine ⟨118154874708072429557642327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315079665888193145487046205 118154874708072429557642327)
        ·
          refine ⟨177232312062108644336463491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118154874708072429557642327 177232312062108644336463491)
          ·
            refine ⟨265848468093162966504695237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177232312062108644336463491 265848468093162966504695237)
            ·
              refine ⟨49846587767468056219630357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265848468093162966504695237 49846587767468056219630357)
              ·
                refine ⟨2336558801600065135295173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49846587767468056219630357 2336558801600065135295173)
                ·
                  refine ⟨438104775300012212867845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336558801600065135295173 438104775300012212867845)
                  ·
                    rfl

theorem cell22_3839427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 4].length) (baseStart_3839427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839427 prefixEnd_3839427 := by exact prefixLift 3839427
  have htrace : WordTrace (prefixWord ++ tailWord_3839427) baseStart_3839427 baseEnd_3839427 := by
    simpa [prefixWord, tailWord_3839427, baseEnd_3839427] using wordTrace_append hprefix tailTrace_3839427
  have hstable : (prefixWord ++ tailWord_3839427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839427).length < 2 ^ (prefixWord ++ tailWord_3839427).sum := by decide
  have hdescent : baseEnd_3839427 < baseStart_3839427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839446 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3839446 : Nat := 118140960795 + 3839446 * 2 ^ 59
def prefixEnd_3839446 : Nat := 4983230072969 + 3 ^ 40 * 3839446 * 2
def baseEnd_3839446 : Nat := 1314320829988326922378477

theorem tailTrace_3839446 : CollatzResearch.WordTrace tailWord_3839446 prefixEnd_3839446 1314320829988326922378477 := by
  unfold tailWord_3839446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8752256253021896376060137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93357400032233561344641461 8752256253021896376060137)
  ·
    refine ⟨6564192189766422282045103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8752256253021896376060137 6564192189766422282045103)
    ·
      refine ⟨9846288284649633423067655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6564192189766422282045103 9846288284649633423067655)
      ·
        refine ⟨14769432426974450134601483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9846288284649633423067655 14769432426974450134601483)
        ·
          refine ⟨22154148640461675201902225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14769432426974450134601483 22154148640461675201902225)
          ·
            refine ⟨16615611480346256401426669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22154148640461675201902225 16615611480346256401426669)
            ·
              refine ⟨6230854305129846150535001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16615611480346256401426669 6230854305129846150535001)
              ·
                refine ⟨4673140728847384612901251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6230854305129846150535001 4673140728847384612901251)
                ·
                  refine ⟨7009711093271076919351877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673140728847384612901251 7009711093271076919351877)
                  ·
                    refine ⟨1314320829988326922378477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009711093271076919351877 1314320829988326922378477)
                    ·
                      rfl

theorem cell22_3839446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3839446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839446 prefixEnd_3839446 := by exact prefixLift 3839446
  have htrace : WordTrace (prefixWord ++ tailWord_3839446) baseStart_3839446 baseEnd_3839446 := by
    simpa [prefixWord, tailWord_3839446, baseEnd_3839446] using wordTrace_append hprefix tailTrace_3839446
  have hstable : (prefixWord ++ tailWord_3839446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839446).length < 2 ^ (prefixWord ++ tailWord_3839446).sum := by decide
  have hdescent : baseEnd_3839446 < baseStart_3839446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839455 : List Nat := [1, 1, 2, 3, 3, 1, 1, 10]
def baseStart_3839455 : Nat := 118140960795 + 3839455 * 2 ^ 59
def prefixEnd_3839455 : Nat := 4983230072969 + 3 ^ 40 * 3839455 * 2
def baseEnd_3839455 : Nat := 146035990096917099878161

theorem tailTrace_3839455 : CollatzResearch.WordTrace tailWord_3839455 prefixEnd_3839455 146035990096917099878161 := by
  unfold tailWord_3839455
  simp only [CollatzResearch.WordTrace]
  refine ⟨140036428305317736554039819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93357618870211824369359879 140036428305317736554039819)
  ·
    refine ⟨210054642457976604831059729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140036428305317736554039819 210054642457976604831059729)
    ·
      refine ⟨157540981843482453623294797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210054642457976604831059729 157540981843482453623294797)
      ·
        refine ⟨59077868191305920108735549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157540981843482453623294797 59077868191305920108735549)
        ·
          refine ⟨22154200571739720040775831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59077868191305920108735549 22154200571739720040775831)
          ·
            refine ⟨33231300857609580061163747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22154200571739720040775831 33231300857609580061163747)
            ·
              refine ⟨49846951286414370091745621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33231300857609580061163747 49846951286414370091745621)
              ·
                refine ⟨146035990096917099878161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49846951286414370091745621 146035990096917099878161)
                ·
                  rfl

theorem cell22_3839455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 10].length) (baseStart_3839455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839455 prefixEnd_3839455 := by exact prefixLift 3839455
  have htrace : WordTrace (prefixWord ++ tailWord_3839455) baseStart_3839455 baseEnd_3839455 := by
    simpa [prefixWord, tailWord_3839455, baseEnd_3839455] using wordTrace_append hprefix tailTrace_3839455
  have hstable : (prefixWord ++ tailWord_3839455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839455).length < 2 ^ (prefixWord ++ tailWord_3839455).sum := by decide
  have hdescent : baseEnd_3839455 < baseStart_3839455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839457 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3839457 : Nat := 118140960795 + 3839457 * 2 ^ 59
def prefixEnd_3839457 : Nat := 4983230072969 + 3 ^ 40 * 3839457 * 2
def baseEnd_3839457 : Nat := 1314324595513126560353443

theorem tailTrace_3839457 : CollatzResearch.WordTrace tailWord_3839457 prefixEnd_3839457 1314324595513126560353443 := by
  unfold tailWord_3839457
  simp only [CollatzResearch.WordTrace]
  refine ⟨140036501251310490895612625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93357667500873660597075083 140036501251310490895612625)
  ·
    refine ⟨105027375938482868171709469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140036501251310490895612625 105027375938482868171709469)
    ·
      refine ⟨39385265976931075564391051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105027375938482868171709469 39385265976931075564391051)
      ·
        refine ⟨59077898965396613346586577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39385265976931075564391051 59077898965396613346586577)
        ·
          refine ⟨44308424224047460009939933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59077898965396613346586577 44308424224047460009939933)
          ·
            refine ⟨16615659084017797503727475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44308424224047460009939933 16615659084017797503727475)
            ·
              refine ⟨24923488626026696255591213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16615659084017797503727475 24923488626026696255591213)
              ·
                refine ⟨9346308234760011095846705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24923488626026696255591213 9346308234760011095846705)
                ·
                  refine ⟨7009731176070008321885029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9346308234760011095846705 7009731176070008321885029)
                  ·
                    refine ⟨1314324595513126560353443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009731176070008321885029 1314324595513126560353443)
                    ·
                      rfl

theorem cell22_3839457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3839457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839457 prefixEnd_3839457 := by exact prefixLift 3839457
  have htrace : WordTrace (prefixWord ++ tailWord_3839457) baseStart_3839457 baseEnd_3839457 := by
    simpa [prefixWord, tailWord_3839457, baseEnd_3839457] using wordTrace_append hprefix tailTrace_3839457
  have hstable : (prefixWord ++ tailWord_3839457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839457).length < 2 ^ (prefixWord ++ tailWord_3839457).sum := by decide
  have hdescent : baseEnd_3839457 < baseStart_3839457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839474 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_3839474 : Nat := 118140960795 + 3839474 * 2 ^ 59
def prefixEnd_3839474 : Nat := 4983230072969 + 3 ^ 40 * 3839474 * 2
def baseEnd_3839474 : Nat := 1314330414960544182678391

theorem tailTrace_3839474 : CollatzResearch.WordTrace tailWord_3839474 prefixEnd_3839474 1314330414960544182678391 := by
  unfold tailWord_3839474
  simp only [CollatzResearch.WordTrace]
  refine ⟨35009280323062225699745369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93358080861499268532654317 35009280323062225699745369)
  ·
    refine ⟨26256960242296669274809027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35009280323062225699745369 26256960242296669274809027)
    ·
      refine ⟨39385440363445003912213541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26256960242296669274809027 39385440363445003912213541)
      ·
        refine ⟨7384770068145938233540039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39385440363445003912213541 7384770068145938233540039)
        ·
          refine ⟨11077155102218907350310059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7384770068145938233540039 11077155102218907350310059)
          ·
            refine ⟨16615732653328361025465089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11077155102218907350310059 16615732653328361025465089)
            ·
              refine ⟨12461799489996270769098817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16615732653328361025465089 12461799489996270769098817)
              ·
                refine ⟨9346349617497203076824113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12461799489996270769098817 9346349617497203076824113)
                ·
                  refine ⟨7009762213122902307618085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9346349617497203076824113 7009762213122902307618085)
                  ·
                    refine ⟨1314330414960544182678391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009762213122902307618085 1314330414960544182678391)
                    ·
                      rfl

theorem cell22_3839474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_3839474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839474 prefixEnd_3839474 := by exact prefixLift 3839474
  have htrace : WordTrace (prefixWord ++ tailWord_3839474) baseStart_3839474 baseEnd_3839474 := by
    simpa [prefixWord, tailWord_3839474, baseEnd_3839474] using wordTrace_append hprefix tailTrace_3839474
  have hstable : (prefixWord ++ tailWord_3839474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839474).length < 2 ^ (prefixWord ++ tailWord_3839474).sum := by decide
  have hdescent : baseEnd_3839474 < baseStart_3839474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839478 : List Nat := [5, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_3839478 : Nat := 118140960795 + 3839478 * 2 ^ 59
def prefixEnd_3839478 : Nat := 4983230072969 + 3 ^ 40 * 3839478 * 2
def baseEnd_3839478 : Nat := 438110594747429835192793

theorem tailTrace_3839478 : CollatzResearch.WordTrace tailWord_3839478 prefixEnd_3839478 438110594747429835192793 := by
  unfold tailWord_3839478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8752329199014650717632943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93358178122822940988084725 8752329199014650717632943)
  ·
    refine ⟨13128493798521976076449415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8752329199014650717632943 13128493798521976076449415)
    ·
      refine ⟨19692740697782964114674123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13128493798521976076449415 19692740697782964114674123)
      ·
        refine ⟨29539111046674446172011185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19692740697782964114674123 29539111046674446172011185)
        ·
          refine ⟨22154333285005834629008389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29539111046674446172011185 22154333285005834629008389)
          ·
            refine ⟨4153937490938593992939073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22154333285005834629008389 4153937490938593992939073)
            ·
              refine ⟨3115453118203945494704305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4153937490938593992939073 3115453118203945494704305)
              ·
                refine ⟨2336589838652959121028229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3115453118203945494704305 2336589838652959121028229)
                ·
                  refine ⟨438110594747429835192793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336589838652959121028229 438110594747429835192793)
                  ·
                    rfl

theorem cell22_3839478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_3839478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839478 prefixEnd_3839478 := by exact prefixLift 3839478
  have htrace : WordTrace (prefixWord ++ tailWord_3839478) baseStart_3839478 baseEnd_3839478 := by
    simpa [prefixWord, tailWord_3839478, baseEnd_3839478] using wordTrace_append hprefix tailTrace_3839478
  have hstable : (prefixWord ++ tailWord_3839478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839478).length < 2 ^ (prefixWord ++ tailWord_3839478).sum := by decide
  have hdescent : baseEnd_3839478 < baseStart_3839478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839489 : List Nat := [1, 2, 4, 1, 4, 2, 1, 7]
def baseStart_3839489 : Nat := 118140960795 + 3839489 * 2 ^ 59
def prefixEnd_3839489 : Nat := 4983230072969 + 3 ^ 40 * 3839489 * 2
def baseEnd_3839489 : Nat := 146037283307454349283705

theorem tailTrace_3839489 : CollatzResearch.WordTrace tailWord_3839489 prefixEnd_3839489 146037283307454349283705 := by
  unfold tailWord_3839489
  simp only [CollatzResearch.WordTrace]
  refine ⟨140037668387194560360777521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93358445591463040240518347 140037668387194560360777521)
  ·
    refine ⟨105028251290395920270583141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140037668387194560360777521 105028251290395920270583141)
    ·
      refine ⟨19692797116949235050734339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105028251290395920270583141 19692797116949235050734339)
      ·
        refine ⟨29539195675423852576101509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19692797116949235050734339 29539195675423852576101509)
        ·
          refine ⟨5538599189141972358019033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29539195675423852576101509 5538599189141972358019033)
          ·
            refine ⟨4153949391856479268514275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5538599189141972358019033 4153949391856479268514275)
            ·
              refine ⟨6230924087784718902771413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153949391856479268514275 6230924087784718902771413)
              ·
                refine ⟨146037283307454349283705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6230924087784718902771413 146037283307454349283705)
                ·
                  rfl

theorem cell22_3839489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 7].length) (baseStart_3839489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839489 prefixEnd_3839489 := by exact prefixLift 3839489
  have htrace : WordTrace (prefixWord ++ tailWord_3839489) baseStart_3839489 baseEnd_3839489 := by
    simpa [prefixWord, tailWord_3839489, baseEnd_3839489] using wordTrace_append hprefix tailTrace_3839489
  have hstable : (prefixWord ++ tailWord_3839489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839489).length < 2 ^ (prefixWord ++ tailWord_3839489).sum := by decide
  have hdescent : baseEnd_3839489 < baseStart_3839489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839508 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3839508 : Nat := 118140960795 + 3839508 * 2 ^ 59
def prefixEnd_3839508 : Nat := 4983230072969 + 3 ^ 40 * 3839508 * 2
def baseEnd_3839508 : Nat := 1314342053855379427328287

theorem tailTrace_3839508 : CollatzResearch.WordTrace tailWord_3839508 prefixEnd_3839508 1314342053855379427328287 := by
  unfold tailWord_3839508
  simp only [CollatzResearch.WordTrace]
  refine ⟨70019180687062863302859589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93358907582750484403812785 70019180687062863302859589)
  ·
    refine ⟨13128596378824286869286173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70019180687062863302859589 13128596378824286869286173)
    ·
      refine ⟨4923223642059107575982315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13128596378824286869286173 4923223642059107575982315)
      ·
        refine ⟨7384835463088661363973473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4923223642059107575982315 7384835463088661363973473)
        ·
          refine ⟨5538626597316496022980105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7384835463088661363973473 5538626597316496022980105)
          ·
            refine ⟨4153969947987372017235079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5538626597316496022980105 4153969947987372017235079)
            ·
              refine ⟨6230954921981058025852619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153969947987372017235079 6230954921981058025852619)
              ·
                refine ⟨9346432382971587038778929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230954921981058025852619 9346432382971587038778929)
                ·
                  refine ⟨7009824287228690279084197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9346432382971587038778929 7009824287228690279084197)
                  ·
                    refine ⟨1314342053855379427328287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009824287228690279084197 1314342053855379427328287)
                    ·
                      rfl

theorem cell22_3839508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3839508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839508 prefixEnd_3839508 := by exact prefixLift 3839508
  have htrace : WordTrace (prefixWord ++ tailWord_3839508) baseStart_3839508 baseEnd_3839508 := by
    simpa [prefixWord, tailWord_3839508, baseEnd_3839508] using wordTrace_append hprefix tailTrace_3839508
  have hstable : (prefixWord ++ tailWord_3839508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839508).length < 2 ^ (prefixWord ++ tailWord_3839508).sum := by decide
  have hdescent : baseEnd_3839508 < baseStart_3839508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839517 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 7]
def baseStart_3839517 : Nat := 118140960795 + 3839517 * 2 ^ 59
def prefixEnd_3839517 : Nat := 4983230072969 + 3 ^ 40 * 3839517 * 2
def baseEnd_3839517 : Nat := 438115044913102134617753

theorem tailTrace_3839517 : CollatzResearch.WordTrace tailWord_3839517 prefixEnd_3839517 438115044913102134617753 := by
  unfold tailWord_3839517
  simp only [CollatzResearch.WordTrace]
  refine ⟨140038689631093121142796805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93359126420728747428531203 140038689631093121142796805)
  ·
    refine ⟨26257254305829960214274401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140038689631093121142796805 26257254305829960214274401)
    ·
      refine ⟨19692940729372470160705801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26257254305829960214274401 19692940729372470160705801)
      ·
        refine ⟨14769705547029352620529351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19692940729372470160705801 14769705547029352620529351)
        ·
          refine ⟨22154558320544028930794027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14769705547029352620529351 22154558320544028930794027)
          ·
            refine ⟨33231837480816043396191041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22154558320544028930794027 33231837480816043396191041)
            ·
              refine ⟨24923878110612032547143281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33231837480816043396191041 24923878110612032547143281)
              ·
                refine ⟨18692908582959024410357461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24923878110612032547143281 18692908582959024410357461)
                ·
                  refine ⟨438115044913102134617753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18692908582959024410357461 438115044913102134617753)
                  ·
                    rfl

theorem cell22_3839517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_3839517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839517 prefixEnd_3839517 := by exact prefixLift 3839517
  have htrace : WordTrace (prefixWord ++ tailWord_3839517) baseStart_3839517 baseEnd_3839517 := by
    simpa [prefixWord, tailWord_3839517, baseEnd_3839517] using wordTrace_append hprefix tailTrace_3839517
  have hstable : (prefixWord ++ tailWord_3839517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839517).length < 2 ^ (prefixWord ++ tailWord_3839517).sum := by decide
  have hdescent : baseEnd_3839517 < baseStart_3839517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839521 : List Nat := [1, 2, 3, 2, 2, 2, 1, 5, 1, 3]
def baseStart_3839521 : Nat := 118140960795 + 3839521 * 2 ^ 59
def prefixEnd_3839521 : Nat := 4983230072969 + 3 ^ 40 * 3839521 * 2
def baseEnd_3839521 : Nat := 1314346504021051726753247

theorem tailTrace_3839521 : CollatzResearch.WordTrace tailWord_3839521 prefixEnd_3839521 1314346504021051726753247 := by
  unfold tailWord_3839521
  simp only [CollatzResearch.WordTrace]
  refine ⟨140038835523078629825942417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93359223682052419883961611 140038835523078629825942417)
  ·
    refine ⟨105029126642308972369456813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140038835523078629825942417 105029126642308972369456813)
    ·
      refine ⟨39385922490865864638546305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105029126642308972369456813 39385922490865864638546305)
      ·
        refine ⟨29539441868149398478909729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39385922490865864638546305 29539441868149398478909729)
        ·
          refine ⟨22154581401112048859182297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29539441868149398478909729 22154581401112048859182297)
          ·
            refine ⟨16615936050834036644386723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22154581401112048859182297 16615936050834036644386723)
            ·
              refine ⟨24923904076251054966580085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16615936050834036644386723 24923904076251054966580085)
              ·
                refine ⟨2336616007148536403116883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24923904076251054966580085 2336616007148536403116883)
                ·
                  refine ⟨3504924010722804604675325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336616007148536403116883 3504924010722804604675325)
                  ·
                    refine ⟨1314346504021051726753247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504924010722804604675325 1314346504021051726753247)
                    ·
                      rfl

theorem cell22_3839521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_3839521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839521 prefixEnd_3839521 := by exact prefixLift 3839521
  have htrace : WordTrace (prefixWord ++ tailWord_3839521) baseStart_3839521 baseEnd_3839521 := by
    simpa [prefixWord, tailWord_3839521, baseEnd_3839521] using wordTrace_append hprefix tailTrace_3839521
  have hstable : (prefixWord ++ tailWord_3839521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839521).length < 2 ^ (prefixWord ++ tailWord_3839521).sum := by decide
  have hdescent : baseEnd_3839521 < baseStart_3839521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839534 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_3839534 : Nat := 118140960795 + 3839534 * 2 ^ 59
def prefixEnd_3839534 : Nat := 4983230072969 + 3 ^ 40 * 3839534 * 2
def baseEnd_3839534 : Nat := 438116984728908008726069

theorem tailTrace_3839534 : CollatzResearch.WordTrace tailWord_3839534 prefixEnd_3839534 438116984728908008726069 := by
  unfold tailWord_3839534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17504913709003941630770707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93359539781354355364110437 17504913709003941630770707)
  ·
    refine ⟨26257370563505912446156061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17504913709003941630770707 26257370563505912446156061)
    ·
      refine ⟨9846513961314717167308523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26257370563505912446156061 9846513961314717167308523)
      ·
        refine ⟨14769770941972075750962785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9846513961314717167308523 14769770941972075750962785)
        ·
          refine ⟨11077328206479056813222089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14769770941972075750962785 11077328206479056813222089)
          ·
            refine ⟨8307996154859292609916567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11077328206479056813222089 8307996154859292609916567)
            ·
              refine ⟨12461994232288938914874851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8307996154859292609916567 12461994232288938914874851)
              ·
                refine ⟨18692991348433408372312277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12461994232288938914874851 18692991348433408372312277)
                ·
                  refine ⟨438116984728908008726069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18692991348433408372312277 438116984728908008726069)
                  ·
                    rfl

theorem cell22_3839534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_3839534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839534 prefixEnd_3839534 := by exact prefixLift 3839534
  have htrace : WordTrace (prefixWord ++ tailWord_3839534) baseStart_3839534 baseEnd_3839534 := by
    simpa [prefixWord, tailWord_3839534, baseEnd_3839534] using wordTrace_append hprefix tailTrace_3839534
  have hstable : (prefixWord ++ tailWord_3839534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839534).length < 2 ^ (prefixWord ++ tailWord_3839534).sum := by decide
  have hdescent : baseEnd_3839534 < baseStart_3839534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839562 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_3839562 : Nat := 118140960795 + 3839562 * 2 ^ 59
def prefixEnd_3839562 : Nat := 4983230072969 + 3 ^ 40 * 3839562 * 2
def baseEnd_3839562 : Nat := 438120179719647095492707

theorem tailTrace_3839562 : CollatzResearch.WordTrace tailWord_3839562 prefixEnd_3839562 438120179719647095492707 := by
  unfold tailWord_3839562
  simp only [CollatzResearch.WordTrace]
  refine ⟨35010082728982523457046235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93360220610620062552123293 35010082728982523457046235)
  ·
    refine ⟨52515124093473785185569353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35010082728982523457046235 52515124093473785185569353)
    ·
      refine ⟨39386343070105338889177015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52515124093473785185569353 39386343070105338889177015)
      ·
        refine ⟨59079514605158008333765523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39386343070105338889177015 59079514605158008333765523)
        ·
          refine ⟨88619271907737012500648285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59079514605158008333765523 88619271907737012500648285)
          ·
            refine ⟨33232226965401379687743107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88619271907737012500648285 33232226965401379687743107)
            ·
              refine ⟨49848340448102069531614661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33232226965401379687743107 49848340448102069531614661)
              ·
                refine ⟨9346563834019138037177749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49848340448102069531614661 9346563834019138037177749)
                ·
                  refine ⟨438120179719647095492707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9346563834019138037177749 438120179719647095492707)
                  ·
                    rfl

theorem cell22_3839562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_3839562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839562 prefixEnd_3839562 := by exact prefixLift 3839562
  have htrace : WordTrace (prefixWord ++ tailWord_3839562) baseStart_3839562 baseEnd_3839562 := by
    simpa [prefixWord, tailWord_3839562, baseEnd_3839562] using wordTrace_append hprefix tailTrace_3839562
  have hstable : (prefixWord ++ tailWord_3839562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839562).length < 2 ^ (prefixWord ++ tailWord_3839562).sum := by decide
  have hdescent : baseEnd_3839562 < baseStart_3839562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839564 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_3839564 : Nat := 118140960795 + 3839564 * 2 ^ 59
def prefixEnd_3839564 : Nat := 4983230072969 + 3 ^ 40 * 3839564 * 2
def baseEnd_3839564 : Nat := 1314361223799813947928115

theorem tailTrace_3839564 : CollatzResearch.WordTrace tailWord_3839564 prefixEnd_3839564 1314361223799813947928115 := by
  unfold tailWord_3839564
  simp only [CollatzResearch.WordTrace]
  refine ⟨70020201930961424084878873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93360269241281898779838497 70020201930961424084878873)
  ·
    refine ⟨52515151448221068063659155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70020201930961424084878873 52515151448221068063659155)
    ·
      refine ⟨78772727172331602095488733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52515151448221068063659155 78772727172331602095488733)
      ·
        refine ⟨29539772689624350785808275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78772727172331602095488733 29539772689624350785808275)
        ·
          refine ⟨44309659034436526178712413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29539772689624350785808275 44309659034436526178712413)
          ·
            refine ⟨16616122137913697317017155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44309659034436526178712413 16616122137913697317017155)
            ·
              refine ⟨24924183206870545975525733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16616122137913697317017155 24924183206870545975525733)
              ·
                refine ⟨4673284351288227370411075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24924183206870545975525733 4673284351288227370411075)
                ·
                  refine ⟨7009926526932341055616613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673284351288227370411075 7009926526932341055616613)
                  ·
                    refine ⟨1314361223799813947928115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009926526932341055616613 1314361223799813947928115)
                    ·
                      rfl

theorem cell22_3839564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_3839564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839564 prefixEnd_3839564 := by exact prefixLift 3839564
  have htrace : WordTrace (prefixWord ++ tailWord_3839564) baseStart_3839564 baseEnd_3839564 := by
    simpa [prefixWord, tailWord_3839564, baseEnd_3839564] using wordTrace_append hprefix tailTrace_3839564
  have hstable : (prefixWord ++ tailWord_3839564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839564).length < 2 ^ (prefixWord ++ tailWord_3839564).sum := by decide
  have hdescent : baseEnd_3839564 < baseStart_3839564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839577 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_3839577 : Nat := 118140960795 + 3839577 * 2 ^ 59
def prefixEnd_3839577 : Nat := 4983230072969 + 3 ^ 40 * 3839577 * 2
def baseEnd_3839577 : Nat := 1314365673965486247353075

theorem tailTrace_3839577 : CollatzResearch.WordTrace tailWord_3839577 prefixEnd_3839577 1314365673965486247353075 := by
  unfold tailWord_3839577
  simp only [CollatzResearch.WordTrace]
  refine ⟨140040878010875751389980985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93360585340583834259987323 140040878010875751389980985)
  ·
    refine ⟨105030658508156813542485739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140040878010875751389980985 105030658508156813542485739)
    ·
      refine ⟨157545987762235220313728609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105030658508156813542485739 157545987762235220313728609)
      ·
        refine ⟨118159490821676415235296457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157545987762235220313728609 118159490821676415235296457)
        ·
          refine ⟨88619618116257311426472343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118159490821676415235296457 88619618116257311426472343)
          ·
            refine ⟨132929427174385967139708515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88619618116257311426472343 132929427174385967139708515)
            ·
              refine ⟨199394140761578950709562773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132929427174385967139708515 199394140761578950709562773)
              ·
                refine ⟨9346600348199013314510755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199394140761578950709562773 9346600348199013314510755)
                ·
                  refine ⟨14019900522298519971766133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9346600348199013314510755 14019900522298519971766133)
                  ·
                    refine ⟨1314365673965486247353075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14019900522298519971766133 1314365673965486247353075)
                    ·
                      rfl

theorem cell22_3839577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_3839577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839577 prefixEnd_3839577 := by exact prefixLift 3839577
  have htrace : WordTrace (prefixWord ++ tailWord_3839577) baseStart_3839577 baseEnd_3839577 := by
    simpa [prefixWord, tailWord_3839577, baseEnd_3839577] using wordTrace_append hprefix tailTrace_3839577
  have hstable : (prefixWord ++ tailWord_3839577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839577).length < 2 ^ (prefixWord ++ tailWord_3839577).sum := by decide
  have hdescent : baseEnd_3839577 < baseStart_3839577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839626 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_3839626 : Nat := 118140960795 + 3839626 * 2 ^ 59
def prefixEnd_3839626 : Nat := 4983230072969 + 3 ^ 40 * 3839626 * 2
def baseEnd_3839626 : Nat := 1314382447666866452877925

theorem tailTrace_3839626 : CollatzResearch.WordTrace tailWord_3839626 prefixEnd_3839626 1314382447666866452877925 := by
  unfold tailWord_3839626
  simp only [CollatzResearch.WordTrace]
  refine ⟨35010666296924558189628683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93361776791798821839009821 35010666296924558189628683)
  ·
    refine ⟨52515999445386837284443025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35010666296924558189628683 52515999445386837284443025)
    ·
      refine ⟨39386999584040127963332269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52515999445386837284443025 39386999584040127963332269)
      ·
        refine ⟨14770124844015047986249601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39386999584040127963332269 14770124844015047986249601)
        ·
          refine ⟨11077593633011285989687201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14770124844015047986249601 11077593633011285989687201)
          ·
            refine ⟨8308195224758464492265401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11077593633011285989687201 8308195224758464492265401)
            ·
              refine ⟨6231146418568848369199051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8308195224758464492265401 6231146418568848369199051)
              ·
                refine ⟨9346719627853272553798577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231146418568848369199051 9346719627853272553798577)
                ·
                  refine ⟨7010039720889954415348933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9346719627853272553798577 7010039720889954415348933)
                  ·
                    refine ⟨1314382447666866452877925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7010039720889954415348933 1314382447666866452877925)
                    ·
                      rfl

theorem cell22_3839626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_3839626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839626 prefixEnd_3839626 := by exact prefixLift 3839626
  have htrace : WordTrace (prefixWord ++ tailWord_3839626) baseStart_3839626 baseEnd_3839626 := by
    simpa [prefixWord, tailWord_3839626, baseEnd_3839626] using wordTrace_append hprefix tailTrace_3839626
  have hstable : (prefixWord ++ tailWord_3839626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839626).length < 2 ^ (prefixWord ++ tailWord_3839626).sum := by decide
  have hdescent : baseEnd_3839626 < baseStart_3839626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839637 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_3839637 : Nat := 118140960795 + 3839637 * 2 ^ 59
def prefixEnd_3839637 : Nat := 4983230072969 + 3 ^ 40 * 3839637 * 2
def baseEnd_3839637 : Nat := 1314386213191666090852891

theorem tailTrace_3839637 : CollatzResearch.WordTrace tailWord_3839637 prefixEnd_3839637 1314386213191666090852891 := by
  unfold tailWord_3839637
  simp only [CollatzResearch.WordTrace]
  refine ⟨140043066390658381637165165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93362044260438921091443443 140043066390658381637165165)
  ·
    refine ⟨52516149896496893113936937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140043066390658381637165165 52516149896496893113936937)
    ·
      refine ⟨39387112422372669835452703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52516149896496893113936937 39387112422372669835452703)
      ·
        refine ⟨59080668633559004753179055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39387112422372669835452703 59080668633559004753179055)
        ·
          refine ⟨88621002950338507129768583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59080668633559004753179055 88621002950338507129768583)
          ·
            refine ⟨132931504425507760694652875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88621002950338507129768583 132931504425507760694652875)
            ·
              refine ⟨199397256638261641041979313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132931504425507760694652875 199397256638261641041979313)
              ·
                refine ⟨149547942478696230781484485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199397256638261641041979313 149547942478696230781484485)
                ·
                  refine ⟨28040239214755543271528341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149547942478696230781484485 28040239214755543271528341)
                  ·
                    refine ⟨1314386213191666090852891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28040239214755543271528341 1314386213191666090852891)
                    ·
                      rfl

theorem cell22_3839637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_3839637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839637 prefixEnd_3839637 := by exact prefixLift 3839637
  have htrace : WordTrace (prefixWord ++ tailWord_3839637) baseStart_3839637 baseEnd_3839637 := by
    simpa [prefixWord, tailWord_3839637, baseEnd_3839637] using wordTrace_append hprefix tailTrace_3839637
  have hstable : (prefixWord ++ tailWord_3839637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839637).length < 2 ^ (prefixWord ++ tailWord_3839637).sum := by decide
  have hdescent : baseEnd_3839637 < baseStart_3839637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839647 : List Nat := [1, 1, 2, 7, 2, 1, 2, 2, 4]
def baseStart_3839647 : Nat := 118140960795 + 3839647 * 2 ^ 59
def prefixEnd_3839647 : Nat := 4983230072969 + 3 ^ 40 * 3839647 * 2
def baseEnd_3839647 : Nat := 438129878798676466034287

theorem tailTrace_3839647 : CollatzResearch.WordTrace tailWord_3839647 prefixEnd_3839647 438129878798676466034287 := by
  unfold tailWord_3839647
  simp only [CollatzResearch.WordTrace]
  refine ⟨140043431120622153345029195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93362287413748102230019463 140043431120622153345029195)
  ·
    refine ⟨210065146680933230017543793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140043431120622153345029195 210065146680933230017543793)
    ·
      refine ⟨157548860010699922513157845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210065146680933230017543793 157548860010699922513157845)
      ·
        refine ⟨3692551406500779433902137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 157548860010699922513157845 3692551406500779433902137)
        ·
          refine ⟨2769413554875584575426603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3692551406500779433902137 2769413554875584575426603)
          ·
            refine ⟨4154120332313376863139905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769413554875584575426603 4154120332313376863139905)
            ·
              refine ⟨3115590249235032647354929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4154120332313376863139905 3115590249235032647354929)
              ·
                refine ⟨2336692686926274485516197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3115590249235032647354929 2336692686926274485516197)
                ·
                  refine ⟨438129878798676466034287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336692686926274485516197 438129878798676466034287)
                  ·
                    rfl

theorem cell22_3839647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 4].length) (baseStart_3839647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839647 prefixEnd_3839647 := by exact prefixLift 3839647
  have htrace : WordTrace (prefixWord ++ tailWord_3839647) baseStart_3839647 baseEnd_3839647 := by
    simpa [prefixWord, tailWord_3839647, baseEnd_3839647] using wordTrace_append hprefix tailTrace_3839647
  have hstable : (prefixWord ++ tailWord_3839647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839647).length < 2 ^ (prefixWord ++ tailWord_3839647).sum := by decide
  have hdescent : baseEnd_3839647 < baseStart_3839647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839684 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3839684 : Nat := 118140960795 + 3839684 * 2 ^ 59
def prefixEnd_3839684 : Nat := 4983230072969 + 3 ^ 40 * 3839684 * 2
def baseEnd_3839684 : Nat := 1314402302252173634927747

theorem tailTrace_3839684 : CollatzResearch.WordTrace tailWord_3839684 prefixEnd_3839684 1314402302252173634927747 := by
  unfold tailWord_3839684
  simp only [CollatzResearch.WordTrace]
  refine ⟨70022390310744054332063053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93363187080992072442750737 70022390310744054332063053)
  ·
    refine ⟨26258396366529020374523645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70022390310744054332063053 26258396366529020374523645)
    ·
      refine ⟨9846898637448382640446367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26258396366529020374523645 9846898637448382640446367)
      ·
        refine ⟨14770347956172573960669551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9846898637448382640446367 14770347956172573960669551)
        ·
          refine ⟨22155521934258860941004327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14770347956172573960669551 22155521934258860941004327)
          ·
            refine ⟨33233282901388291411506491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22155521934258860941004327 33233282901388291411506491)
            ·
              refine ⟨49849924352082437117259737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33233282901388291411506491 49849924352082437117259737)
              ·
                refine ⟨37387443264061827837944803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49849924352082437117259737 37387443264061827837944803)
                ·
                  refine ⟨56081164896092741756917205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37387443264061827837944803 56081164896092741756917205)
                  ·
                    refine ⟨1314402302252173634927747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56081164896092741756917205 1314402302252173634927747)
                    ·
                      rfl

theorem cell22_3839684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3839684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839684 prefixEnd_3839684 := by exact prefixLift 3839684
  have htrace : WordTrace (prefixWord ++ tailWord_3839684) baseStart_3839684 baseEnd_3839684 := by
    simpa [prefixWord, tailWord_3839684, baseEnd_3839684] using wordTrace_append hprefix tailTrace_3839684
  have hstable : (prefixWord ++ tailWord_3839684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839684).length < 2 ^ (prefixWord ++ tailWord_3839684).sum := by decide
  have hdescent : baseEnd_3839684 < baseStart_3839684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839690 : List Nat := [3, 1, 2, 1, 5, 1, 2, 3, 1, 3]
def baseStart_3839690 : Nat := 118140960795 + 3839690 * 2 ^ 59
def prefixEnd_3839690 : Nat := 4983230072969 + 3 ^ 40 * 3839690 * 2
def baseEnd_3839690 : Nat := 1314404356174791619277729

theorem tailTrace_3839690 : CollatzResearch.WordTrace tailWord_3839690 prefixEnd_3839690 1314404356174791619277729 := by
  unfold tailWord_3839690
  simp only [CollatzResearch.WordTrace]
  refine ⟨35011249864866592922211131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93363332972977581125896349 35011249864866592922211131)
  ·
    refine ⟨52516874797299889383316697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35011249864866592922211131 52516874797299889383316697)
    ·
      refine ⟨39387656097974917037487523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52516874797299889383316697 39387656097974917037487523)
      ·
        refine ⟨59081484146962375556231285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39387656097974917037487523 59081484146962375556231285)
        ·
          refine ⟨5538889138777722708396683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59081484146962375556231285 5538889138777722708396683)
          ·
            refine ⟨8308333708166584062595025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5538889138777722708396683 8308333708166584062595025)
            ·
              refine ⟨6231250281124938046946269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8308333708166584062595025 6231250281124938046946269)
              ·
                refine ⟨2336718855421851767604851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6231250281124938046946269 2336718855421851767604851)
                ·
                  refine ⟨3505078283132777651407277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336718855421851767604851 3505078283132777651407277)
                  ·
                    refine ⟨1314404356174791619277729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3505078283132777651407277 1314404356174791619277729)
                    ·
                      rfl

theorem cell22_3839690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_3839690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839690 prefixEnd_3839690 := by exact prefixLift 3839690
  have htrace : WordTrace (prefixWord ++ tailWord_3839690) baseStart_3839690 baseEnd_3839690 := by
    simpa [prefixWord, tailWord_3839690, baseEnd_3839690] using wordTrace_append hprefix tailTrace_3839690
  have hstable : (prefixWord ++ tailWord_3839690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839690).length < 2 ^ (prefixWord ++ tailWord_3839690).sum := by decide
  have hdescent : baseEnd_3839690 < baseStart_3839690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839746 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3839746 : Nat := 118140960795 + 3839746 * 2 ^ 59
def prefixEnd_3839746 : Nat := 4983230072969 + 3 ^ 40 * 3839746 * 2
def baseEnd_3839746 : Nat := 1314423526119226139877557

theorem tailTrace_3839746 : CollatzResearch.WordTrace tailWord_3839746 prefixEnd_3839746 1314423526119226139877557 := by
  unfold tailWord_3839746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35011760486815873313220773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93364694631508995501922061 35011760486815873313220773)
  ·
    refine ⟨6564705091277976246228895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35011760486815873313220773 6564705091277976246228895)
    ·
      refine ⟨9847057636916964369343343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6564705091277976246228895 9847057636916964369343343)
      ·
        refine ⟨14770586455375446554015015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9847057636916964369343343 14770586455375446554015015)
        ·
          refine ⟨22155879683063169831022523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14770586455375446554015015 22155879683063169831022523)
          ·
            refine ⟨33233819524594754746533785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22155879683063169831022523 33233819524594754746533785)
            ·
              refine ⟨24925364643446066059900339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33233819524594754746533785 24925364643446066059900339)
              ·
                refine ⟨37388046965169099089850509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24925364643446066059900339 37388046965169099089850509)
                ·
                  refine ⟨14020517611938412158693941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37388046965169099089850509 14020517611938412158693941)
                  ·
                    refine ⟨1314423526119226139877557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14020517611938412158693941 1314423526119226139877557)
                    ·
                      rfl

theorem cell22_3839746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3839746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839746 prefixEnd_3839746 := by exact prefixLift 3839746
  have htrace : WordTrace (prefixWord ++ tailWord_3839746) baseStart_3839746 baseEnd_3839746 := by
    simpa [prefixWord, tailWord_3839746, baseEnd_3839746] using wordTrace_append hprefix tailTrace_3839746
  have hstable : (prefixWord ++ tailWord_3839746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839746).length < 2 ^ (prefixWord ++ tailWord_3839746).sum := by decide
  have hdescent : baseEnd_3839746 < baseStart_3839746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839748 : List Nat := [2, 3, 2, 2, 1, 2, 3, 3, 4]
def baseStart_3839748 : Nat := 118140960795 + 3839748 * 2 ^ 59
def prefixEnd_3839748 : Nat := 4983230072969 + 3 ^ 40 * 3839748 * 2
def baseEnd_3839748 : Nat := 438141403586699600442517

theorem tailTrace_3839748 : CollatzResearch.WordTrace tailWord_3839748 prefixEnd_3839748 438141403586699600442517 := by
  unfold tailWord_3839748
  simp only [CollatzResearch.WordTrace]
  refine ⟨70023557446628123797227949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93364743262170831729637265 70023557446628123797227949)
  ·
    refine ⟨26258834042485546423960481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70023557446628123797227949 26258834042485546423960481)
    ·
      refine ⟨19694125531864159817970361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26258834042485546423960481 19694125531864159817970361)
      ·
        refine ⟨14770594148898119863477771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19694125531864159817970361 14770594148898119863477771)
        ·
          refine ⟨22155891223347179795216657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14770594148898119863477771 22155891223347179795216657)
          ·
            refine ⟨16616918417510384846412493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22155891223347179795216657 16616918417510384846412493)
            ·
              refine ⟨6231344406566394317404685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16616918417510384846412493 6231344406566394317404685)
              ·
                refine ⟨2336754152462397869026757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6231344406566394317404685 2336754152462397869026757)
                ·
                  refine ⟨438141403586699600442517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336754152462397869026757 438141403586699600442517)
                  ·
                    rfl

theorem cell22_3839748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_3839748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839748 prefixEnd_3839748 := by exact prefixLift 3839748
  have htrace : WordTrace (prefixWord ++ tailWord_3839748) baseStart_3839748 baseEnd_3839748 := by
    simpa [prefixWord, tailWord_3839748, baseEnd_3839748] using wordTrace_append hprefix tailTrace_3839748
  have hstable : (prefixWord ++ tailWord_3839748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839748).length < 2 ^ (prefixWord ++ tailWord_3839748).sum := by decide
  have hdescent : baseEnd_3839748 < baseStart_3839748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839780 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_3839780 : Nat := 118140960795 + 3839780 * 2 ^ 59
def prefixEnd_3839780 : Nat := 4983230072969 + 3 ^ 40 * 3839780 * 2
def baseEnd_3839780 : Nat := 1314435165014061384527453

theorem tailTrace_3839780 : CollatzResearch.WordTrace tailWord_3839780 prefixEnd_3839780 1314435165014061384527453 := by
  unfold tailWord_3839780
  simp only [CollatzResearch.WordTrace]
  refine ⟨70024141014570158529810397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93365521352760211373080529 70024141014570158529810397)
  ·
    refine ⟨26259052880463809448678899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70024141014570158529810397 26259052880463809448678899)
    ·
      refine ⟨39388579320695714173018349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26259052880463809448678899 39388579320695714173018349)
      ·
        refine ⟨14770717245260892814881881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39388579320695714173018349 14770717245260892814881881)
        ·
          refine ⟨11078037933945669611161411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14770717245260892814881881 11078037933945669611161411)
          ·
            refine ⟨16617056900918504416742117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11078037933945669611161411 16617056900918504416742117)
            ·
              refine ⟨3115698168922219578139147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16617056900918504416742117 3115698168922219578139147)
              ·
                refine ⟨4673547253383329367208721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115698168922219578139147 4673547253383329367208721)
                ·
                  refine ⟨3505160440037497025406541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4673547253383329367208721 3505160440037497025406541)
                  ·
                    refine ⟨1314435165014061384527453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3505160440037497025406541 1314435165014061384527453)
                    ·
                      rfl

theorem cell22_3839780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_3839780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839780 prefixEnd_3839780 := by exact prefixLift 3839780
  have htrace : WordTrace (prefixWord ++ tailWord_3839780) baseStart_3839780 baseEnd_3839780 := by
    simpa [prefixWord, tailWord_3839780, baseEnd_3839780] using wordTrace_append hprefix tailTrace_3839780
  have hstable : (prefixWord ++ tailWord_3839780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839780).length < 2 ^ (prefixWord ++ tailWord_3839780).sum := by decide
  have hdescent : baseEnd_3839780 < baseStart_3839780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839804 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 9]
def baseStart_3839804 : Nat := 118140960795 + 3839804 * 2 ^ 59
def prefixEnd_3839804 : Nat := 4983230072969 + 3 ^ 40 * 3839804 * 2
def baseEnd_3839804 : Nat := 438147793568177773975793

theorem tailTrace_3839804 : CollatzResearch.WordTrace tailWord_3839804 prefixEnd_3839804 438147793568177773975793 := by
  unfold tailWord_3839804
  simp only [CollatzResearch.WordTrace]
  refine ⟨70024578690526684579247233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93366104920702246105662977 70024578690526684579247233)
  ·
    refine ⟨52518434017895013434435425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70024578690526684579247233 52518434017895013434435425)
    ·
      refine ⟨39388825513421260075826569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52518434017895013434435425 39388825513421260075826569)
      ·
        refine ⟨29541619135065945056869927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39388825513421260075826569 29541619135065945056869927)
        ·
          refine ⟨44312428702598917585304891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29541619135065945056869927 44312428702598917585304891)
          ·
            refine ⟨66468643053898376377957337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44312428702598917585304891 66468643053898376377957337)
            ·
              refine ⟨49851482290423782283468003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66468643053898376377957337 49851482290423782283468003)
              ·
                refine ⟨74777223435635673425202005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49851482290423782283468003 74777223435635673425202005)
                ·
                  refine ⟨438147793568177773975793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74777223435635673425202005 438147793568177773975793)
                  ·
                    rfl

theorem cell22_3839804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_3839804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839804 prefixEnd_3839804 := by exact prefixLift 3839804
  have htrace : WordTrace (prefixWord ++ tailWord_3839804) baseStart_3839804 baseEnd_3839804 := by
    simpa [prefixWord, tailWord_3839804, baseEnd_3839804] using wordTrace_append hprefix tailTrace_3839804
  have hstable : (prefixWord ++ tailWord_3839804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839804).length < 2 ^ (prefixWord ++ tailWord_3839804).sum := by decide
  have hdescent : baseEnd_3839804 < baseStart_3839804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839825 : List Nat := [1, 2, 2, 1, 5, 2, 1, 4, 1, 3]
def baseStart_3839825 : Nat := 118140960795 + 3839825 * 2 ^ 59
def prefixEnd_3839825 : Nat := 4983230072969 + 3 ^ 40 * 3839825 * 2
def baseEnd_3839825 : Nat := 1314450569433696267152315

theorem tailTrace_3839825 : CollatzResearch.WordTrace tailWord_3839825 prefixEnd_3839825 1314450569433696267152315 := by
  unfold tailWord_3839825
  simp only [CollatzResearch.WordTrace]
  refine ⟨140049923313977289745008929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93366615542651526496672619 140049923313977289745008929)
  ·
    refine ⟨105037442485482967308756697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140049923313977289745008929 105037442485482967308756697)
    ·
      refine ⟨78778081864112225481567523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105037442485482967308756697 78778081864112225481567523)
      ·
        refine ⟨118167122796168338222351285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78778081864112225481567523 118167122796168338222351285)
        ·
          refine ⟨11078167762140781708345433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118167122796168338222351285 11078167762140781708345433)
          ·
            refine ⟨8308625821605586281259075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11078167762140781708345433 8308625821605586281259075)
            ·
              refine ⟨12462938732408379421888613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8308625821605586281259075 12462938732408379421888613)
              ·
                refine ⟨2336801012326571141604115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12462938732408379421888613 2336801012326571141604115)
                ·
                  refine ⟨3505201518489856712406173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336801012326571141604115 3505201518489856712406173)
                  ·
                    refine ⟨1314450569433696267152315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3505201518489856712406173 1314450569433696267152315)
                    ·
                      rfl

theorem cell22_3839825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_3839825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839825 prefixEnd_3839825 := by exact prefixLift 3839825
  have htrace : WordTrace (prefixWord ++ tailWord_3839825) baseStart_3839825 baseEnd_3839825 := by
    simpa [prefixWord, tailWord_3839825, baseEnd_3839825] using wordTrace_append hprefix tailTrace_3839825
  have hstable : (prefixWord ++ tailWord_3839825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839825).length < 2 ^ (prefixWord ++ tailWord_3839825).sum := by decide
  have hdescent : baseEnd_3839825 < baseStart_3839825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839851 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 1, 4]
def baseStart_3839851 : Nat := 118140960795 + 3839851 * 2 ^ 59
def prefixEnd_3839851 : Nat := 4983230072969 + 3 ^ 40 * 3839851 * 2
def baseEnd_3839851 : Nat := 1314459469765040866002235

theorem tailTrace_3839851 : CollatzResearch.WordTrace tailWord_3839851 prefixEnd_3839851 1314459469765040866002235 := by
  unfold tailWord_3839851
  simp only [CollatzResearch.WordTrace]
  refine ⟨140050871611883096185455407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93367247741255397456970271 140050871611883096185455407)
  ·
    refine ⟨210076307417824644278183111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140050871611883096185455407 210076307417824644278183111)
    ·
      refine ⟨315114461126736966417274667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210076307417824644278183111 315114461126736966417274667)
      ·
        refine ⟨472671691690105449625912001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315114461126736966417274667 472671691690105449625912001)
        ·
          refine ⟨354503768767579087219434001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472671691690105449625912001 354503768767579087219434001)
          ·
            refine ⟨265877826575684315414575501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354503768767579087219434001 265877826575684315414575501)
            ·
              refine ⟨99704184965881618280465813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265877826575684315414575501 99704184965881618280465813)
              ·
                refine ⟨4673633670275700856896835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99704184965881618280465813 4673633670275700856896835)
                ·
                  refine ⟨7010450505413551285345253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673633670275700856896835 7010450505413551285345253)
                  ·
                    refine ⟨1314459469765040866002235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7010450505413551285345253 1314459469765040866002235)
                    ·
                      rfl

theorem cell22_3839851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 4].length) (baseStart_3839851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839851 prefixEnd_3839851 := by exact prefixLift 3839851
  have htrace : WordTrace (prefixWord ++ tailWord_3839851) baseStart_3839851 baseEnd_3839851 := by
    simpa [prefixWord, tailWord_3839851, baseEnd_3839851] using wordTrace_append hprefix tailTrace_3839851
  have hstable : (prefixWord ++ tailWord_3839851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839851).length < 2 ^ (prefixWord ++ tailWord_3839851).sum := by decide
  have hdescent : baseEnd_3839851 < baseStart_3839851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839864 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_3839864 : Nat := 118140960795 + 3839864 * 2 ^ 59
def prefixEnd_3839864 : Nat := 4983230072969 + 3 ^ 40 * 3839864 * 2
def baseEnd_3839864 : Nat := 1314463919930713165427195

theorem tailTrace_3839864 : CollatzResearch.WordTrace tailWord_3839864 prefixEnd_3839864 1314463919930713165427195 := by
  unfold tailWord_3839864
  simp only [CollatzResearch.WordTrace]
  refine ⟨70025672880417999702839323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93367563840557332937119097 70025672880417999702839323)
  ·
    refine ⟨105038509320626999554258985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70025672880417999702839323 105038509320626999554258985)
    ·
      refine ⟨78778881990470249665694239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105038509320626999554258985 78778881990470249665694239)
      ·
        refine ⟨118168322985705374498541359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78778881990470249665694239 118168322985705374498541359)
        ·
          refine ⟨177252484478558061747812039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118168322985705374498541359 177252484478558061747812039)
          ·
            refine ⟨265878726717837092621718059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177252484478558061747812039 265878726717837092621718059)
            ·
              refine ⟨398818090076755638932577089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265878726717837092621718059 398818090076755638932577089)
              ·
                refine ⟨299113567557566729199432817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398818090076755638932577089 299113567557566729199432817)
                ·
                  refine ⟨224335175668175046899574613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299113567557566729199432817 224335175668175046899574613)
                  ·
                    refine ⟨1314463919930713165427195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 224335175668175046899574613 1314463919930713165427195)
                    ·
                      rfl

theorem cell22_3839864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_3839864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839864 prefixEnd_3839864 := by exact prefixLift 3839864
  have htrace : WordTrace (prefixWord ++ tailWord_3839864) baseStart_3839864 baseEnd_3839864 := by
    simpa [prefixWord, tailWord_3839864, baseEnd_3839864] using wordTrace_append hprefix tailTrace_3839864
  have hstable : (prefixWord ++ tailWord_3839864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839864).length < 2 ^ (prefixWord ++ tailWord_3839864).sum := by decide
  have hdescent : baseEnd_3839864 < baseStart_3839864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839898 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_3839898 : Nat := 118140960795 + 3839898 * 2 ^ 59
def prefixEnd_3839898 : Nat := 4983230072969 + 3 ^ 40 * 3839898 * 2
def baseEnd_3839898 : Nat := 1314475558825548410077091

theorem tailTrace_3839898 : CollatzResearch.WordTrace tailWord_3839898 prefixEnd_3839898 1314475558825548410077091 := by
  unfold tailWord_3839898
  simp only [CollatzResearch.WordTrace]
  refine ⟨35013146460678205803104087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93368390561808548808277565 35013146460678205803104087)
  ·
    refine ⟨52519719691017308704656131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35013146460678205803104087 52519719691017308704656131)
    ·
      refine ⟨78779579536525963056984197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52519719691017308704656131 78779579536525963056984197)
      ·
        refine ⟨14771171163098618073184537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78779579536525963056984197 14771171163098618073184537)
        ·
          refine ⟨11078378372323963554888403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14771171163098618073184537 11078378372323963554888403)
          ·
            refine ⟨16617567558485945332332605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11078378372323963554888403 16617567558485945332332605)
            ·
              refine ⟨6231587834432229499624727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16617567558485945332332605 6231587834432229499624727)
              ·
                refine ⟨9347381751648344249437091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231587834432229499624727 9347381751648344249437091)
                ·
                  refine ⟨14021072627472516374155637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9347381751648344249437091 14021072627472516374155637)
                  ·
                    refine ⟨1314475558825548410077091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14021072627472516374155637 1314475558825548410077091)
                    ·
                      rfl

theorem cell22_3839898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_3839898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839898 prefixEnd_3839898 := by exact prefixLift 3839898
  have htrace : WordTrace (prefixWord ++ tailWord_3839898) baseStart_3839898 baseEnd_3839898 := by
    simpa [prefixWord, tailWord_3839898, baseEnd_3839898] using wordTrace_append hprefix tailTrace_3839898
  have hstable : (prefixWord ++ tailWord_3839898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839898).length < 2 ^ (prefixWord ++ tailWord_3839898).sum := by decide
  have hdescent : baseEnd_3839898 < baseStart_3839898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839964 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3839964 : Nat := 118140960795 + 3839964 * 2 ^ 59
def prefixEnd_3839964 : Nat := 4983230072969 + 3 ^ 40 * 3839964 * 2
def baseEnd_3839964 : Nat := 1314498151974346237926889

theorem tailTrace_3839964 : CollatzResearch.WordTrace tailWord_3839964 prefixEnd_3839964 1314498151974346237926889 := by
  unfold tailWord_3839964
  simp only [CollatzResearch.WordTrace]
  refine ⟨70027496530236858242159473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93369995373649144322879297 70027496530236858242159473)
  ·
    refine ⟨52520622397677643681619605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70027496530236858242159473 52520622397677643681619605)
    ·
      refine ⟨2461904174891139547575919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52520622397677643681619605 2461904174891139547575919)
      ·
        refine ⟨3692856262336709321363879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461904174891139547575919 3692856262336709321363879)
        ·
          refine ⟨5539284393505063982045819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692856262336709321363879 5539284393505063982045819)
          ·
            refine ⟨8308926590257595973068729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539284393505063982045819 8308926590257595973068729)
            ·
              refine ⟨6231694942693196979801547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8308926590257595973068729 6231694942693196979801547)
              ·
                refine ⟨9347542414039795469702321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231694942693196979801547 9347542414039795469702321)
                ·
                  refine ⟨7010656810529846602276741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9347542414039795469702321 7010656810529846602276741)
                  ·
                    refine ⟨1314498151974346237926889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7010656810529846602276741 1314498151974346237926889)
                    ·
                      rfl

theorem cell22_3839964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3839964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3839964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3839964 prefixEnd_3839964 := by exact prefixLift 3839964
  have htrace : WordTrace (prefixWord ++ tailWord_3839964) baseStart_3839964 baseEnd_3839964 := by
    simpa [prefixWord, tailWord_3839964, baseEnd_3839964] using wordTrace_append hprefix tailTrace_3839964
  have hstable : (prefixWord ++ tailWord_3839964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839964).length < 2 ^ (prefixWord ++ tailWord_3839964).sum := by decide
  have hdescent : baseEnd_3839964 < baseStart_3839964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840016 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_3840016 : Nat := 118140960795 + 3840016 * 2 ^ 59
def prefixEnd_3840016 : Nat := 4983230072969 + 3 ^ 40 * 3840016 * 2
def baseEnd_3840016 : Nat := 1314515952637035435626729

theorem tailTrace_3840016 : CollatzResearch.WordTrace tailWord_3840016 prefixEnd_3840016 1314515952637035435626729 := by
  unfold tailWord_3840016
  simp only [CollatzResearch.WordTrace]
  refine ⟨70028444828142664682605951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93371259770856886243474601 70028444828142664682605951)
  ·
    refine ⟨105042667242213997023908927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70028444828142664682605951 105042667242213997023908927)
    ·
      refine ⟨157564000863320995535863391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105042667242213997023908927 157564000863320995535863391)
      ·
        refine ⟨236346001294981493303795087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157564000863320995535863391 236346001294981493303795087)
        ·
          refine ⟨354519001942472239955692631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236346001294981493303795087 354519001942472239955692631)
          ·
            refine ⟨531778502913708359933538947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354519001942472239955692631 531778502913708359933538947)
            ·
              refine ⟨797667754370562539900308421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531778502913708359933538947 797667754370562539900308421)
              ·
                refine ⟨149562703944480476231307829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 797667754370562539900308421 149562703944480476231307829)
                ·
                  refine ⟨14021503494795044646685109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149562703944480476231307829 14021503494795044646685109)
                  ·
                    refine ⟨1314515952637035435626729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14021503494795044646685109 1314515952637035435626729)
                    ·
                      rfl

theorem cell22_3840016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_3840016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840016 prefixEnd_3840016 := by exact prefixLift 3840016
  have htrace : WordTrace (prefixWord ++ tailWord_3840016) baseStart_3840016 baseEnd_3840016 := by
    simpa [prefixWord, tailWord_3840016, baseEnd_3840016] using wordTrace_append hprefix tailTrace_3840016
  have hstable : (prefixWord ++ tailWord_3840016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840016).length < 2 ^ (prefixWord ++ tailWord_3840016).sum := by decide
  have hdescent : baseEnd_3840016 < baseStart_3840016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840035 : List Nat := [1, 1, 1, 4, 3, 1, 4, 3, 4]
def baseStart_3840035 : Nat := 118140960795 + 3840035 * 2 ^ 59
def prefixEnd_3840035 : Nat := 4983230072969 + 3 ^ 40 * 3840035 * 2
def baseEnd_3840035 : Nat := 438174152241775239800557

theorem tailTrace_3840035 : CollatzResearch.WordTrace tailWord_3840035 prefixEnd_3840035 438174152241775239800557 := by
  unfold tailWord_3840035
  simp only [CollatzResearch.WordTrace]
  refine ⟨140057582643216495610153559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93371721762144330406769039 140057582643216495610153559)
  ·
    refine ⟨210086373964824743415230339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140057582643216495610153559 210086373964824743415230339)
    ·
      refine ⟨315129560947237115122845509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210086373964824743415230339 315129560947237115122845509)
      ·
        refine ⟨59086792677606959085533533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315129560947237115122845509 59086792677606959085533533)
        ·
          refine ⟨22157547254102609657075075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59086792677606959085533533 22157547254102609657075075)
          ·
            refine ⟨33236320881153914485612613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22157547254102609657075075 33236320881153914485612613)
            ·
              refine ⟨6231810165216358966052365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33236320881153914485612613 6231810165216358966052365)
              ·
                refine ⟨2336928811956134612269637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6231810165216358966052365 2336928811956134612269637)
                ·
                  refine ⟨438174152241775239800557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336928811956134612269637 438174152241775239800557)
                  ·
                    rfl

theorem cell22_3840035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 4].length) (baseStart_3840035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840035 prefixEnd_3840035 := by exact prefixLift 3840035
  have htrace : WordTrace (prefixWord ++ tailWord_3840035) baseStart_3840035 baseEnd_3840035 := by
    simpa [prefixWord, tailWord_3840035, baseEnd_3840035] using wordTrace_append hprefix tailTrace_3840035
  have hstable : (prefixWord ++ tailWord_3840035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840035).length < 2 ^ (prefixWord ++ tailWord_3840035).sum := by decide
  have hdescent : baseEnd_3840035 < baseStart_3840035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840037 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 1, 4]
def baseStart_3840037 : Nat := 118140960795 + 3840037 * 2 ^ 59
def prefixEnd_3840037 : Nat := 4983230072969 + 3 ^ 40 * 3840037 * 2
def baseEnd_3840037 : Nat := 1314523141366198380851665

theorem tailTrace_3840037 : CollatzResearch.WordTrace tailWord_3840037 prefixEnd_3840037 1314523141366198380851665 := by
  unfold tailWord_3840037
  simp only [CollatzResearch.WordTrace]
  refine ⟨140057655589209249951726365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93371770392806166634484243 140057655589209249951726365)
  ·
    refine ⟨52521620845953468731897387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140057655589209249951726365 52521620845953468731897387)
    ·
      refine ⟨78782431268930203097846081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52521620845953468731897387 78782431268930203097846081)
      ·
        refine ⟨59086823451697652323384561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78782431268930203097846081 59086823451697652323384561)
        ·
          refine ⟨44315117588773239242538421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59086823451697652323384561 44315117588773239242538421)
          ·
            refine ⟨4154542273947491178987977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44315117588773239242538421 4154542273947491178987977)
            ·
              refine ⟨3115906705460618384240983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4154542273947491178987977 3115906705460618384240983)
              ·
                refine ⟨4673860058190927576361475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115906705460618384240983 4673860058190927576361475)
                ·
                  refine ⟨7010790087286391364542213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673860058190927576361475 7010790087286391364542213)
                  ·
                    refine ⟨1314523141366198380851665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7010790087286391364542213 1314523141366198380851665)
                    ·
                      rfl

theorem cell22_3840037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_3840037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840037 prefixEnd_3840037 := by exact prefixLift 3840037
  have htrace : WordTrace (prefixWord ++ tailWord_3840037) baseStart_3840037 baseEnd_3840037 := by
    simpa [prefixWord, tailWord_3840037, baseEnd_3840037] using wordTrace_append hprefix tailTrace_3840037
  have hstable : (prefixWord ++ tailWord_3840037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840037).length < 2 ^ (prefixWord ++ tailWord_3840037).sum := by decide
  have hdescent : baseEnd_3840037 < baseStart_3840037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840050 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_3840050 : Nat := 118140960795 + 3840050 * 2 ^ 59
def prefixEnd_3840050 : Nat := 4983230072969 + 3 ^ 40 * 3840050 * 2
def baseEnd_3840050 : Nat := 1314527591531870680276625

theorem tailTrace_3840050 : CollatzResearch.WordTrace tailWord_3840050 prefixEnd_3840050 1314527591531870680276625 := by
  unfold tailWord_3840050
  simp only [CollatzResearch.WordTrace]
  refine ⟨35014532434540538292987401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93372086492108102114633069 35014532434540538292987401)
  ·
    refine ⟨26260899325905403719740551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35014532434540538292987401 26260899325905403719740551)
    ·
      refine ⟨39391348988858105579610827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26260899325905403719740551 39391348988858105579610827)
      ·
        refine ⟨59087023483287158369416241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39391348988858105579610827 59087023483287158369416241)
        ·
          refine ⟨44315267612465368777062181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59087023483287158369416241 44315267612465368777062181)
          ·
            refine ⟨8309112677337256645699159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44315267612465368777062181 8309112677337256645699159)
            ·
              refine ⟨12463669016005884968548739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8309112677337256645699159 12463669016005884968548739)
              ·
                refine ⟨18695503524008827452823109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12463669016005884968548739 18695503524008827452823109)
                ·
                  refine ⟨3505406910751655147404333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18695503524008827452823109 3505406910751655147404333)
                  ·
                    refine ⟨1314527591531870680276625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3505406910751655147404333 1314527591531870680276625)
                    ·
                      rfl

theorem cell22_3840050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_3840050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840050 prefixEnd_3840050 := by exact prefixLift 3840050
  have htrace : WordTrace (prefixWord ++ tailWord_3840050) baseStart_3840050 baseEnd_3840050 := by
    simpa [prefixWord, tailWord_3840050, baseEnd_3840050] using wordTrace_append hprefix tailTrace_3840050
  have hstable : (prefixWord ++ tailWord_3840050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840050).length < 2 ^ (prefixWord ++ tailWord_3840050).sum := by decide
  have hdescent : baseEnd_3840050 < baseStart_3840050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840052 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3840052 : Nat := 118140960795 + 3840052 * 2 ^ 59
def prefixEnd_3840052 : Nat := 4983230072969 + 3 ^ 40 * 3840052 * 2
def baseEnd_3840052 : Nat := 438176092057581113908873

theorem tailTrace_3840052 : CollatzResearch.WordTrace tailWord_3840052 prefixEnd_3840052 438176092057581113908873 := by
  unfold tailWord_3840052
  simp only [CollatzResearch.WordTrace]
  refine ⟨70029101342077453756761205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93372135122769938342348273 70029101342077453756761205)
  ·
    refine ⟨6565228250819761289696363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70029101342077453756761205 6565228250819761289696363)
    ·
      refine ⟨9847842376229641934544545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6565228250819761289696363 9847842376229641934544545)
      ·
        refine ⟨7385881782172231450908409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9847842376229641934544545 7385881782172231450908409)
        ·
          refine ⟨5539411336629173588181307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7385881782172231450908409 5539411336629173588181307)
          ·
            refine ⟨8309117004943760382271961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539411336629173588181307 8309117004943760382271961)
            ·
              refine ⟨6231837753707820286703971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8309117004943760382271961 6231837753707820286703971)
              ·
                refine ⟨9347756630561730430055957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231837753707820286703971 9347756630561730430055957)
                ·
                  refine ⟨438176092057581113908873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9347756630561730430055957 438176092057581113908873)
                  ·
                    rfl

theorem cell22_3840052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3840052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840052 prefixEnd_3840052 := by exact prefixLift 3840052
  have htrace : WordTrace (prefixWord ++ tailWord_3840052) baseStart_3840052 baseEnd_3840052 := by
    simpa [prefixWord, tailWord_3840052, baseEnd_3840052] using wordTrace_append hprefix tailTrace_3840052
  have hstable : (prefixWord ++ tailWord_3840052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840052).length < 2 ^ (prefixWord ++ tailWord_3840052).sum := by decide
  have hdescent : baseEnd_3840052 < baseStart_3840052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840086 : List Nat := [5, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_3840086 : Nat := 118140960795 + 3840086 * 2 ^ 59
def prefixEnd_3840086 : Nat := 4983230072969 + 3 ^ 40 * 3840086 * 2
def baseEnd_3840086 : Nat := 438179971689192862125505

theorem tailTrace_3840086 : CollatzResearch.WordTrace tailWord_3840086 prefixEnd_3840086 438179971689192862125505 := by
  unfold tailWord_3840086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8753715172876983207516257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93372961844021154213506741 8753715172876983207516257)
  ·
    refine ⟨6565286379657737405637193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8753715172876983207516257 6565286379657737405637193)
    ·
      refine ⟨4923964784743303054227895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6565286379657737405637193 4923964784743303054227895)
      ·
        refine ⟨7385947177114954581341843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4923964784743303054227895 7385947177114954581341843)
        ·
          refine ⟨11078920765672431872012765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7385947177114954581341843 11078920765672431872012765)
          ·
            refine ⟨4154595287127161952004787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11078920765672431872012765 4154595287127161952004787)
            ·
              refine ⟨6231892930690742928007181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154595287127161952004787 6231892930690742928007181)
              ·
                refine ⟨2336959849009028598002693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6231892930690742928007181 2336959849009028598002693)
                ·
                  refine ⟨438179971689192862125505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336959849009028598002693 438179971689192862125505)
                  ·
                    rfl

theorem cell22_3840086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_3840086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840086 prefixEnd_3840086 := by exact prefixLift 3840086
  have htrace : WordTrace (prefixWord ++ tailWord_3840086) baseStart_3840086 baseEnd_3840086 := by
    simpa [prefixWord, tailWord_3840086, baseEnd_3840086] using wordTrace_append hprefix tailTrace_3840086
  have hstable : (prefixWord ++ tailWord_3840086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840086).length < 2 ^ (prefixWord ++ tailWord_3840086).sum := by decide
  have hdescent : baseEnd_3840086 < baseStart_3840086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840108 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 7]
def baseStart_3840108 : Nat := 118140960795 + 3840108 * 2 ^ 59
def prefixEnd_3840108 : Nat := 4983230072969 + 3 ^ 40 * 3840108 * 2
def baseEnd_3840108 : Nat := 438182482039059287442149

theorem tailTrace_3840108 : CollatzResearch.WordTrace tailWord_3840108 prefixEnd_3840108 438182482039059287442149 := by
  unfold tailWord_3840108
  simp only [CollatzResearch.WordTrace]
  refine ⟨70030122585976014538780489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93373496781301352718373985 70030122585976014538780489)
  ·
    refine ⟨52522591939482010904085367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70030122585976014538780489 52522591939482010904085367)
    ·
      refine ⟨78783887909223016356128051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52522591939482010904085367 78783887909223016356128051)
      ·
        refine ⟨118175831863834524534192077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78783887909223016356128051 118175831863834524534192077)
        ·
          refine ⟨44315936948937946700322029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118175831863834524534192077 44315936948937946700322029)
          ·
            refine ⟨16618476355851730012620761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44315936948937946700322029 16618476355851730012620761)
            ·
              refine ⟨12463857266888797509465571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16618476355851730012620761 12463857266888797509465571)
              ·
                refine ⟨18695785900333196264198357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12463857266888797509465571 18695785900333196264198357)
                ·
                  refine ⟨438182482039059287442149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18695785900333196264198357 438182482039059287442149)
                  ·
                    rfl

theorem cell22_3840108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_3840108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840108 prefixEnd_3840108 := by exact prefixLift 3840108
  have htrace : WordTrace (prefixWord ++ tailWord_3840108) baseStart_3840108 baseEnd_3840108 := by
    simpa [prefixWord, tailWord_3840108, baseEnd_3840108] using wordTrace_append hprefix tailTrace_3840108
  have hstable : (prefixWord ++ tailWord_3840108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840108).length < 2 ^ (prefixWord ++ tailWord_3840108).sum := by decide
  have hdescent : baseEnd_3840108 < baseStart_3840108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840112 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 3, 3]
def baseStart_3840112 : Nat := 118140960795 + 3840112 * 2 ^ 59
def prefixEnd_3840112 : Nat := 4983230072969 + 3 ^ 40 * 3840112 * 2
def baseEnd_3840112 : Nat := 1314548815398923185226435

theorem tailTrace_3840112 : CollatzResearch.WordTrace tailWord_3840112 prefixEnd_3840112 1314548815398923185226435 := by
  unfold tailWord_3840112
  simp only [CollatzResearch.WordTrace]
  refine ⟨70030195531968768880353295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93373594042625025173804393 70030195531968768880353295)
  ·
    refine ⟨105045293297953153320529943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70030195531968768880353295 105045293297953153320529943)
    ·
      refine ⟨157567939946929729980794915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105045293297953153320529943 157567939946929729980794915)
      ·
        refine ⟨236351909920394594971192373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157567939946929729980794915 236351909920394594971192373)
        ·
          refine ⟨22157991555036993278549285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236351909920394594971192373 22157991555036993278549285)
          ·
            refine ⟨4154623416569436239727991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22157991555036993278549285 4154623416569436239727991)
            ·
              refine ⟨6231935124854154359591987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154623416569436239727991 6231935124854154359591987)
              ·
                refine ⟨9347902687281231539387981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231935124854154359591987 9347902687281231539387981)
                ·
                  refine ⟨3505463507730461827270493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9347902687281231539387981 3505463507730461827270493)
                  ·
                    refine ⟨1314548815398923185226435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3505463507730461827270493 1314548815398923185226435)
                    ·
                      rfl

theorem cell22_3840112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3, 3].length) (baseStart_3840112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840112 prefixEnd_3840112 := by exact prefixLift 3840112
  have htrace : WordTrace (prefixWord ++ tailWord_3840112) baseStart_3840112 baseEnd_3840112 := by
    simpa [prefixWord, tailWord_3840112, baseEnd_3840112] using wordTrace_append hprefix tailTrace_3840112
  have hstable : (prefixWord ++ tailWord_3840112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840112).length < 2 ^ (prefixWord ++ tailWord_3840112).sum := by decide
  have hdescent : baseEnd_3840112 < baseStart_3840112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840125 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 5]
def baseStart_3840125 : Nat := 118140960795 + 3840125 * 2 ^ 59
def prefixEnd_3840125 : Nat := 4983230072969 + 3 ^ 40 * 3840125 * 2
def baseEnd_3840125 : Nat := 438184421854865161550465

theorem tailTrace_3840125 : CollatzResearch.WordTrace tailWord_3840125 prefixEnd_3840125 438184421854865161550465 := by
  unfold tailWord_3840125
  simp only [CollatzResearch.WordTrace]
  refine ⟨140060865212890440980929829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93373910141926960653953219 140060865212890440980929829)
  ·
    refine ⟨26261412227416957683924343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140060865212890440980929829 26261412227416957683924343)
    ·
      refine ⟨39392118341125436525886515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26261412227416957683924343 39392118341125436525886515)
      ·
        refine ⟨59088177511688154788829773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39392118341125436525886515 59088177511688154788829773)
        ·
          refine ⟨22158066566883058045811165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59088177511688154788829773 22158066566883058045811165)
          ·
            refine ⟨8309274962581146767179187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22158066566883058045811165 8309274962581146767179187)
            ·
              refine ⟨12463912443871720150768781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8309274962581146767179187 12463912443871720150768781)
              ·
                refine ⟨4673967166451895056538293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12463912443871720150768781 4673967166451895056538293)
                ·
                  refine ⟨438184421854865161550465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4673967166451895056538293 438184421854865161550465)
                  ·
                    rfl

theorem cell22_3840125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_3840125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840125 prefixEnd_3840125 := by exact prefixLift 3840125
  have htrace : WordTrace (prefixWord ++ tailWord_3840125) baseStart_3840125 baseEnd_3840125 := by
    simpa [prefixWord, tailWord_3840125, baseEnd_3840125] using wordTrace_append hprefix tailTrace_3840125
  have hstable : (prefixWord ++ tailWord_3840125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840125).length < 2 ^ (prefixWord ++ tailWord_3840125).sum := by decide
  have hdescent : baseEnd_3840125 < baseStart_3840125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840174 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3840174 : Nat := 118140960795 + 3840174 * 2 ^ 59
def prefixEnd_3840174 : Nat := 4983230072969 + 3 ^ 40 * 3840174 * 2
def baseEnd_3840174 : Nat := 1314570039265975690176245

theorem tailTrace_3840174 : CollatzResearch.WordTrace tailWord_3840174 prefixEnd_3840174 1314570039265975690176245 := by
  unfold tailWord_3840174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17507831548714115293682947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93375101593141948232975717 17507831548714115293682947)
  ·
    refine ⟨26261747323071172940524421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17507831548714115293682947 26261747323071172940524421)
    ·
      refine ⟨4924077623075844926348329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26261747323071172940524421 4924077623075844926348329)
      ·
        refine ⟨3693058217306883694761247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4924077623075844926348329 3693058217306883694761247)
        ·
          refine ⟨5539587325960325542141871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3693058217306883694761247 5539587325960325542141871)
          ·
            refine ⟨8309380988940488313212807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539587325960325542141871 8309380988940488313212807)
            ·
              refine ⟨12464071483410732469819211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8309380988940488313212807 12464071483410732469819211)
              ·
                refine ⟨18696107225116098704728817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12464071483410732469819211 18696107225116098704728817)
                ·
                  refine ⟨14022080418837074028546613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18696107225116098704728817 14022080418837074028546613)
                  ·
                    refine ⟨1314570039265975690176245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14022080418837074028546613 1314570039265975690176245)
                    ·
                      rfl

theorem cell22_3840174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3840174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840174 prefixEnd_3840174 := by exact prefixLift 3840174
  have htrace : WordTrace (prefixWord ++ tailWord_3840174) baseStart_3840174 baseEnd_3840174 := by
    simpa [prefixWord, tailWord_3840174, baseEnd_3840174] using wordTrace_append hprefix tailTrace_3840174
  have hstable : (prefixWord ++ tailWord_3840174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840174).length < 2 ^ (prefixWord ++ tailWord_3840174).sum := by decide
  have hdescent : baseEnd_3840174 < baseStart_3840174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840185 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 1, 5]
def baseStart_3840185 : Nat := 118140960795 + 3840185 * 2 ^ 59
def prefixEnd_3840185 : Nat := 4983230072969 + 3 ^ 40 * 3840185 * 2
def baseEnd_3840185 : Nat := 1314573804790775328151211

theorem tailTrace_3840185 : CollatzResearch.WordTrace tailWord_3840185 prefixEnd_3840185 1314573804790775328151211 := by
  unfold tailWord_3840185
  simp only [CollatzResearch.WordTrace]
  refine ⟨140063053592673071228114009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93375369061782047485409339 140063053592673071228114009)
  ·
    refine ⟨105047290194504803421085507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140063053592673071228114009 105047290194504803421085507)
    ·
      refine ⟨157570935291757205131628261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105047290194504803421085507 157570935291757205131628261)
      ·
        refine ⟨29544550367204475962180299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157570935291757205131628261 29544550367204475962180299)
        ·
          refine ⟨44316825550806713943270449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29544550367204475962180299 44316825550806713943270449)
          ·
            refine ⟨33237619163105035457452837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44316825550806713943270449 33237619163105035457452837)
            ·
              refine ⟨6232053593082194148272407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33237619163105035457452837 6232053593082194148272407)
              ·
                refine ⟨9348080389623291222408611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6232053593082194148272407 9348080389623291222408611)
                ·
                  refine ⟨14022120584434936833612917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9348080389623291222408611 14022120584434936833612917)
                  ·
                    refine ⟨1314573804790775328151211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14022120584434936833612917 1314573804790775328151211)
                    ·
                      rfl

theorem cell22_3840185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_3840185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840185 prefixEnd_3840185 := by exact prefixLift 3840185
  have htrace : WordTrace (prefixWord ++ tailWord_3840185) baseStart_3840185 baseEnd_3840185 := by
    simpa [prefixWord, tailWord_3840185, baseEnd_3840185] using wordTrace_append hprefix tailTrace_3840185
  have hstable : (prefixWord ++ tailWord_3840185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840185).length < 2 ^ (prefixWord ++ tailWord_3840185).sum := by decide
  have hdescent : baseEnd_3840185 < baseStart_3840185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840335 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 4, 4]
def baseStart_3840335 : Nat := 118140960795 + 3840335 * 2 ^ 59
def prefixEnd_3840335 : Nat := 4983230072969 + 3 ^ 40 * 3840335 * 2
def baseEnd_3840335 : Nat := 1314625152856224936900751

theorem tailTrace_3840335 : CollatzResearch.WordTrace tailWord_3840335 prefixEnd_3840335 1314625152856224936900751 := by
  unfold tailWord_3840335
  simp only [CollatzResearch.WordTrace]
  refine ⟨140068524542129646846074459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93379016361419764564049639 140068524542129646846074459)
  ·
    refine ⟨210102786813194470269111689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140068524542129646846074459 210102786813194470269111689)
    ·
      refine ⟨157577090109895852701833767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210102786813194470269111689 157577090109895852701833767)
      ·
        refine ⟨236365635164843779052750651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157577090109895852701833767 236365635164843779052750651)
        ·
          refine ⟨354548452747265668579125977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236365635164843779052750651 354548452747265668579125977)
          ·
            refine ⟨265911339560449251434344483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354548452747265668579125977 265911339560449251434344483)
            ·
              refine ⟨398867009340673877151516725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265911339560449251434344483 398867009340673877151516725)
              ·
                refine ⟨37393782125688175982954693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398867009340673877151516725 37393782125688175982954693)
                ·
                  refine ⟨7011334148566532996804005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37393782125688175982954693 7011334148566532996804005)
                  ·
                    refine ⟨1314625152856224936900751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7011334148566532996804005 1314625152856224936900751)
                    ·
                      rfl

theorem cell22_3840335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_3840335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840335 prefixEnd_3840335 := by exact prefixLift 3840335
  have htrace : WordTrace (prefixWord ++ tailWord_3840335) baseStart_3840335 baseEnd_3840335 := by
    simpa [prefixWord, tailWord_3840335, baseEnd_3840335] using wordTrace_append hprefix tailTrace_3840335
  have hstable : (prefixWord ++ tailWord_3840335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840335).length < 2 ^ (prefixWord ++ tailWord_3840335).sum := by decide
  have hdescent : baseEnd_3840335 < baseStart_3840335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840354 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3840354 : Nat := 118140960795 + 3840354 * 2 ^ 59
def prefixEnd_3840354 : Nat := 4983230072969 + 3 ^ 40 * 3840354 * 2
def baseEnd_3840354 : Nat := 1314631656944515220675693

theorem tailTrace_3840354 : CollatzResearch.WordTrace tailWord_3840354 prefixEnd_3840354 1314631656944515220675693 := by
  unfold tailWord_3840354
  simp only [CollatzResearch.WordTrace]
  refine ⟨35017304382265203272754029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93379478352707208727344077 35017304382265203272754029)
  ·
    refine ⟨13131489143349451227282761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35017304382265203272754029 13131489143349451227282761)
    ·
      refine ⟨9848616857512088420462071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13131489143349451227282761 9848616857512088420462071)
      ·
        refine ⟨14772925286268132630693107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9848616857512088420462071 14772925286268132630693107)
        ·
          refine ⟨22159387929402198946039661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14772925286268132630693107 22159387929402198946039661)
          ·
            refine ⟨8309770473525824604764873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22159387929402198946039661 8309770473525824604764873)
            ·
              refine ⟨6232327855144368453573655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8309770473525824604764873 6232327855144368453573655)
              ·
                refine ⟨9348491782716552680360483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6232327855144368453573655 9348491782716552680360483)
                ·
                  refine ⟨14022737674074829020540725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9348491782716552680360483 14022737674074829020540725)
                  ·
                    refine ⟨1314631656944515220675693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14022737674074829020540725 1314631656944515220675693)
                    ·
                      rfl

theorem cell22_3840354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3840354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840354 prefixEnd_3840354 := by exact prefixLift 3840354
  have htrace : WordTrace (prefixWord ++ tailWord_3840354) baseStart_3840354 baseEnd_3840354 := by
    simpa [prefixWord, tailWord_3840354, baseEnd_3840354] using wordTrace_append hprefix tailTrace_3840354
  have hstable : (prefixWord ++ tailWord_3840354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840354).length < 2 ^ (prefixWord ++ tailWord_3840354).sum := by decide
  have hdescent : baseEnd_3840354 < baseStart_3840354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840380 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_3840380 : Nat := 118140960795 + 3840380 * 2 ^ 59
def prefixEnd_3840380 : Nat := 4983230072969 + 3 ^ 40 * 3840380 * 2
def baseEnd_3840380 : Nat := 1314640557275859819525613

theorem tailTrace_3840380 : CollatzResearch.WordTrace tailWord_3840380 prefixEnd_3840380 1314640557275859819525613 := by
  unfold tailWord_3840380
  simp only [CollatzResearch.WordTrace]
  refine ⟨70035082913483309765731297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93380110551311079687641729 70035082913483309765731297)
  ·
    refine ⟨52526312185112482324298473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70035082913483309765731297 52526312185112482324298473)
    ·
      refine ⟨39394734138834361743223855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52526312185112482324298473 39394734138834361743223855)
      ·
        refine ⟨59092101208251542614835783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39394734138834361743223855 59092101208251542614835783)
        ·
          refine ⟨88638151812377313922253675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59092101208251542614835783 88638151812377313922253675)
          ·
            refine ⟨132957227718565970883380513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88638151812377313922253675 132957227718565970883380513)
            ·
              refine ⟨99717920788924478162535385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132957227718565970883380513 99717920788924478162535385)
              ·
                refine ⟨74788440591693358621901539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99717920788924478162535385 74788440591693358621901539)
                ·
                  refine ⟨112182660887540037932852309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74788440591693358621901539 112182660887540037932852309)
                  ·
                    refine ⟨1314640557275859819525613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112182660887540037932852309 1314640557275859819525613)
                    ·
                      rfl

theorem cell22_3840380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_3840380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840380 prefixEnd_3840380 := by exact prefixLift 3840380
  have htrace : WordTrace (prefixWord ++ tailWord_3840380) baseStart_3840380 baseEnd_3840380 := by
    simpa [prefixWord, tailWord_3840380, baseEnd_3840380] using wordTrace_append hprefix tailTrace_3840380
  have hstable : (prefixWord ++ tailWord_3840380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840380).length < 2 ^ (prefixWord ++ tailWord_3840380).sum := by decide
  have hdescent : baseEnd_3840380 < baseStart_3840380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840425 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_3840425 : Nat := 118140960795 + 3840425 * 2 ^ 59
def prefixEnd_3840425 : Nat := 4983230072969 + 3 ^ 40 * 3840425 * 2
def baseEnd_3840425 : Nat := 1314655961695494702150475

theorem tailTrace_3840425 : CollatzResearch.WordTrace tailWord_3840425 prefixEnd_3840425 1314655961695494702150475 := by
  unfold tailWord_3840425
  simp only [CollatzResearch.WordTrace]
  refine ⟨140071807111803592216850729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93381204741202394811233819 140071807111803592216850729)
  ·
    refine ⟨105053855333852694162638047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140071807111803592216850729 105053855333852694162638047)
    ·
      refine ⟨157580783000779041243957071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105053855333852694162638047 157580783000779041243957071)
      ·
        refine ⟨236371174501168561865935607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157580783000779041243957071 236371174501168561865935607)
        ·
          refine ⟨354556761751752842798903411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236371174501168561865935607 354556761751752842798903411)
          ·
            refine ⟨531835142627629264198355117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354556761751752842798903411 531835142627629264198355117)
            ·
              refine ⟨199438178485360974074383169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531835142627629264198355117 199438178485360974074383169)
              ·
                refine ⟨149578633864020730555787377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199438178485360974074383169 149578633864020730555787377)
                ·
                  refine ⟨112183975398015547916840533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149578633864020730555787377 112183975398015547916840533)
                  ·
                    refine ⟨1314655961695494702150475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112183975398015547916840533 1314655961695494702150475)
                    ·
                      rfl

theorem cell22_3840425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_3840425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840425 prefixEnd_3840425 := by exact prefixLift 3840425
  have htrace : WordTrace (prefixWord ++ tailWord_3840425) baseStart_3840425 baseEnd_3840425 := by
    simpa [prefixWord, tailWord_3840425, baseEnd_3840425] using wordTrace_append hprefix tailTrace_3840425
  have hstable : (prefixWord ++ tailWord_3840425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840425).length < 2 ^ (prefixWord ++ tailWord_3840425).sum := by decide
  have hdescent : baseEnd_3840425 < baseStart_3840425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840433 : List Nat := [1, 2, 2, 4, 1, 4, 1, 3, 1, 3]
def baseStart_3840433 : Nat := 118140960795 + 3840433 * 2 ^ 59
def prefixEnd_3840433 : Nat := 4983230072969 + 3 ^ 40 * 3840433 * 2
def baseEnd_3840433 : Nat := 1314658700258985347950451

theorem tailTrace_3840433 : CollatzResearch.WordTrace tailWord_3840433 prefixEnd_3840433 1314658700258985347950451 := by
  unfold tailWord_3840433
  simp only [CollatzResearch.WordTrace]
  refine ⟨140072098895774609583141953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93381399263849739722094635 140072098895774609583141953)
  ·
    refine ⟨105054074171830957187356465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140072098895774609583141953 105054074171830957187356465)
    ·
      refine ⟨78790555628873217890517349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105054074171830957187356465 78790555628873217890517349)
      ·
        refine ⟨14773229180413728354472003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78790555628873217890517349 14773229180413728354472003)
        ·
          refine ⟨22159843770620592531708005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14773229180413728354472003 22159843770620592531708005)
          ·
            refine ⟨4154970706991361099695251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22159843770620592531708005 4154970706991361099695251)
            ·
              refine ⟨6232456060487041649542877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154970706991361099695251 6232456060487041649542877)
              ·
                refine ⟨2337171022682640618578579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6232456060487041649542877 2337171022682640618578579)
                ·
                  refine ⟨3505756534023960927867869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2337171022682640618578579 3505756534023960927867869)
                  ·
                    refine ⟨1314658700258985347950451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3505756534023960927867869 1314658700258985347950451)
                    ·
                      rfl

theorem cell22_3840433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_3840433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840433 prefixEnd_3840433 := by exact prefixLift 3840433
  have htrace : WordTrace (prefixWord ++ tailWord_3840433) baseStart_3840433 baseEnd_3840433 := by
    simpa [prefixWord, tailWord_3840433, baseEnd_3840433] using wordTrace_append hprefix tailTrace_3840433
  have hstable : (prefixWord ++ tailWord_3840433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840433).length < 2 ^ (prefixWord ++ tailWord_3840433).sum := by decide
  have hdescent : baseEnd_3840433 < baseStart_3840433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840457 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 6]
def baseStart_3840457 : Nat := 118140960795 + 3840457 * 2 ^ 59
def prefixEnd_3840457 : Nat := 4983230072969 + 3 ^ 40 * 3840457 * 2
def baseEnd_3840457 : Nat := 438222305316485761783459

theorem tailTrace_3840457 : CollatzResearch.WordTrace tailWord_3840457 prefixEnd_3840457 438222305316485761783459 := by
  unfold tailWord_3840457
  simp only [CollatzResearch.WordTrace]
  refine ⟨140072974247687661682015625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93381982831791774454677083 140072974247687661682015625)
  ·
    refine ⟨105054730685765746261511719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140072974247687661682015625 105054730685765746261511719)
    ·
      refine ⟨157582096028648619392267579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105054730685765746261511719 157582096028648619392267579)
      ·
        refine ⟨236373144042972929088401369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157582096028648619392267579 236373144042972929088401369)
        ·
          refine ⟨177279858032229696816301027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236373144042972929088401369 177279858032229696816301027)
          ·
            refine ⟨265919787048344545224451541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177279858032229696816301027 265919787048344545224451541)
            ·
              refine ⟨6232495008945575278698083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 265919787048344545224451541 6232495008945575278698083)
              ·
                refine ⟨9348742513418362918047125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6232495008945575278698083 9348742513418362918047125)
                ·
                  refine ⟨438222305316485761783459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9348742513418362918047125 438222305316485761783459)
                  ·
                    rfl

theorem cell22_3840457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_3840457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840457 prefixEnd_3840457 := by exact prefixLift 3840457
  have htrace : WordTrace (prefixWord ++ tailWord_3840457) baseStart_3840457 baseEnd_3840457 := by
    simpa [prefixWord, tailWord_3840457, baseEnd_3840457] using wordTrace_append hprefix tailTrace_3840457
  have hstable : (prefixWord ++ tailWord_3840457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840457).length < 2 ^ (prefixWord ++ tailWord_3840457).sum := by decide
  have hdescent : baseEnd_3840457 < baseStart_3840457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840472 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_3840472 : Nat := 118140960795 + 3840472 * 2 ^ 59
def prefixEnd_3840472 : Nat := 4983230072969 + 3 ^ 40 * 3840472 * 2
def baseEnd_3840472 : Nat := 1314672050756002246225331

theorem tailTrace_3840472 : CollatzResearch.WordTrace tailWord_3840472 prefixEnd_3840472 1314672050756002246225331 := by
  unfold tailWord_3840472
  simp only [CollatzResearch.WordTrace]
  refine ⟨70036760671316659621905835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93382347561755546162541113 70036760671316659621905835)
  ·
    refine ⟨105055141006974989432858753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70036760671316659621905835 105055141006974989432858753)
    ·
      refine ⟨78791355755231242074644065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105055141006974989432858753 78791355755231242074644065)
      ·
        refine ⟨59093516816423431555983049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78791355755231242074644065 59093516816423431555983049)
        ·
          refine ⟨44320137612317573666987287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59093516816423431555983049 44320137612317573666987287)
          ·
            refine ⟨66480206418476360500480931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44320137612317573666987287 66480206418476360500480931)
            ·
              refine ⟨99720309627714540750721397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66480206418476360500480931 99720309627714540750721397)
              ·
                refine ⟨9348779027598238195380131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99720309627714540750721397 9348779027598238195380131)
                ·
                  refine ⟨14023168541397357293070197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9348779027598238195380131 14023168541397357293070197)
                  ·
                    refine ⟨1314672050756002246225331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14023168541397357293070197 1314672050756002246225331)
                    ·
                      rfl

theorem cell22_3840472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_3840472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840472 prefixEnd_3840472 := by exact prefixLift 3840472
  have htrace : WordTrace (prefixWord ++ tailWord_3840472) baseStart_3840472 baseEnd_3840472 := by
    simpa [prefixWord, tailWord_3840472, baseEnd_3840472] using wordTrace_append hprefix tailTrace_3840472
  have hstable : (prefixWord ++ tailWord_3840472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840472).length < 2 ^ (prefixWord ++ tailWord_3840472).sum := by decide
  have hdescent : baseEnd_3840472 < baseStart_3840472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840493 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_3840493 : Nat := 118140960795 + 3840493 * 2 ^ 59
def prefixEnd_3840493 : Nat := 4983230072969 + 3 ^ 40 * 3840493 * 2
def baseEnd_3840493 : Nat := 1314679239485165191450267

theorem tailTrace_3840493 : CollatzResearch.WordTrace tailWord_3840493 prefixEnd_3840493 1314679239485165191450267 := by
  unfold tailWord_3840493
  simp only [CollatzResearch.WordTrace]
  refine ⟨140074287275557239830326133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93382858183704826553550755 140074287275557239830326133)
  ·
    refine ⟨13131964432083491234093075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140074287275557239830326133 13131964432083491234093075)
    ·
      refine ⟨19697946648125236851139613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13131964432083491234093075 19697946648125236851139613)
      ·
        refine ⟨7386729993046963819177355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19697946648125236851139613 7386729993046963819177355)
        ·
          refine ⟨11080094989570445728766033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7386729993046963819177355 11080094989570445728766033)
          ·
            refine ⟨8310071242177834296574525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11080094989570445728766033 8310071242177834296574525)
            ·
              refine ⟨3116276715816687861215447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8310071242177834296574525 3116276715816687861215447)
              ·
                refine ⟨4674415073725031791823171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116276715816687861215447 4674415073725031791823171)
                ·
                  refine ⟨7011622610587547687734757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674415073725031791823171 7011622610587547687734757)
                  ·
                    refine ⟨1314679239485165191450267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7011622610587547687734757 1314679239485165191450267)
                    ·
                      rfl

theorem cell22_3840493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_3840493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840493 prefixEnd_3840493 := by exact prefixLift 3840493
  have htrace : WordTrace (prefixWord ++ tailWord_3840493) baseStart_3840493 baseEnd_3840493 := by
    simpa [prefixWord, tailWord_3840493, baseEnd_3840493] using wordTrace_append hprefix tailTrace_3840493
  have hstable : (prefixWord ++ tailWord_3840493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840493).length < 2 ^ (prefixWord ++ tailWord_3840493).sum := by decide
  have hdescent : baseEnd_3840493 < baseStart_3840493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840581 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 5]
def baseStart_3840581 : Nat := 118140960795 + 3840581 * 2 ^ 59
def prefixEnd_3840581 : Nat := 4983230072969 + 3 ^ 40 * 3840581 * 2
def baseEnd_3840581 : Nat := 438236454561187431749999

theorem tailTrace_3840581 : CollatzResearch.WordTrace tailWord_3840581 prefixEnd_3840581 438236454561187431749999 := by
  unfold tailWord_3840581
  simp only [CollatzResearch.WordTrace]
  refine ⟨140077496899238430859529597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93384997932825620573019731 140077496899238430859529597)
  ·
    refine ⟨52529061337214411572323599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140077496899238430859529597 52529061337214411572323599)
    ·
      refine ⟨78793592005821617358485399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52529061337214411572323599 78793592005821617358485399)
      ·
        refine ⟨118190388008732426037728099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78793592005821617358485399 118190388008732426037728099)
        ·
          refine ⟨177285582013098639056592149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118190388008732426037728099 177285582013098639056592149)
          ·
            refine ⟨8310261656863998705777757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177285582013098639056592149 8310261656863998705777757)
            ·
              refine ⟨3116348121323999514666659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8310261656863998705777757 3116348121323999514666659)
              ·
                refine ⟨4674522181985999271999989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116348121323999514666659 4674522181985999271999989)
                ·
                  refine ⟨438236454561187431749999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4674522181985999271999989 438236454561187431749999)
                  ·
                    rfl

theorem cell22_3840581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_3840581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840581 prefixEnd_3840581 := by exact prefixLift 3840581
  have htrace : WordTrace (prefixWord ++ tailWord_3840581) baseStart_3840581 baseEnd_3840581 := by
    simpa [prefixWord, tailWord_3840581, baseEnd_3840581] using wordTrace_append hprefix tailTrace_3840581
  have hstable : (prefixWord ++ tailWord_3840581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840581).length < 2 ^ (prefixWord ++ tailWord_3840581).sum := by decide
  have hdescent : baseEnd_3840581 < baseStart_3840581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840592 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 8]
def baseStart_3840592 : Nat := 118140960795 + 3840592 * 2 ^ 59
def prefixEnd_3840592 : Nat := 4983230072969 + 3 ^ 40 * 3840592 * 2
def baseEnd_3840592 : Nat := 438237709736120644408321

theorem tailTrace_3840592 : CollatzResearch.WordTrace tailWord_3840592 prefixEnd_3840592 438237709736120644408321 := by
  unfold tailWord_3840592
  simp only [CollatzResearch.WordTrace]
  refine ⟨70038949051099289869090015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93385265401465719825453353 70038949051099289869090015)
  ·
    refine ⟨105058423576648934803635023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70038949051099289869090015 105058423576648934803635023)
    ·
      refine ⟨157587635364973402205452535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105058423576648934803635023 157587635364973402205452535)
      ·
        refine ⟨236381453047460103308178803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157587635364973402205452535 236381453047460103308178803)
        ·
          refine ⟨354572179571190154962268205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236381453047460103308178803 354572179571190154962268205)
          ·
            refine ⟨132964567339196308110850577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354572179571190154962268205 132964567339196308110850577)
            ·
              refine ⟨99723425504397231083137933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132964567339196308110850577 99723425504397231083137933)
              ·
                refine ⟨37396284564148961656176725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99723425504397231083137933 37396284564148961656176725)
                ·
                  refine ⟨438237709736120644408321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37396284564148961656176725 438237709736120644408321)
                  ·
                    rfl

theorem cell22_3840592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_3840592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840592 prefixEnd_3840592 := by exact prefixLift 3840592
  have htrace : WordTrace (prefixWord ++ tailWord_3840592) baseStart_3840592 baseEnd_3840592 := by
    simpa [prefixWord, tailWord_3840592, baseEnd_3840592] using wordTrace_append hprefix tailTrace_3840592
  have hstable : (prefixWord ++ tailWord_3840592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840592).length < 2 ^ (prefixWord ++ tailWord_3840592).sum := by decide
  have hdescent : baseEnd_3840592 < baseStart_3840592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840654 : List Nat := [4, 1, 1, 3, 1, 1, 1, 10]
def baseStart_3840654 : Nat := 118140960795 + 3840654 * 2 ^ 59
def prefixEnd_3840654 : Nat := 4983230072969 + 3 ^ 40 * 3840654 * 2
def baseEnd_3840654 : Nat := 146081594786157159797197

theorem tailTrace_3840654 : CollatzResearch.WordTrace tailWord_3840654 prefixEnd_3840654 146081594786157159797197 := by
  unfold tailWord_3840654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17510019928496745540867127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93386772951982642884624677 17510019928496745540867127)
  ·
    refine ⟨26265029892745118311300691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17510019928496745540867127 26265029892745118311300691)
    ·
      refine ⟨39397544839117677466951037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26265029892745118311300691 39397544839117677466951037)
      ·
        refine ⟨14774079314669129050106639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39397544839117677466951037 14774079314669129050106639)
        ·
          refine ⟨22161118972003693575159959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14774079314669129050106639 22161118972003693575159959)
          ·
            refine ⟨33241678458005540362739939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22161118972003693575159959 33241678458005540362739939)
            ·
              refine ⟨49862517687008310544109909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33241678458005540362739939 49862517687008310544109909)
              ·
                refine ⟨146081594786157159797197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49862517687008310544109909 146081594786157159797197)
                ·
                  rfl

theorem cell22_3840654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_3840654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840654 prefixEnd_3840654 := by exact prefixLift 3840654
  have htrace : WordTrace (prefixWord ++ tailWord_3840654) baseStart_3840654 baseEnd_3840654 := by
    simpa [prefixWord, tailWord_3840654, baseEnd_3840654] using wordTrace_append hprefix tailTrace_3840654
  have hstable : (prefixWord ++ tailWord_3840654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840654).length < 2 ^ (prefixWord ++ tailWord_3840654).sum := by decide
  have hdescent : baseEnd_3840654 < baseStart_3840654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840705 : List Nat := [1, 2, 6, 2, 1, 1, 3, 6]
def baseStart_3840705 : Nat := 118140960795 + 3840705 * 2 ^ 59
def prefixEnd_3840705 : Nat := 4983230072969 + 3 ^ 40 * 3840705 * 2
def baseEnd_3840705 : Nat := 146083534601963033905513

theorem tailTrace_3840705 : CollatzResearch.WordTrace tailWord_3840705 prefixEnd_3840705 146083534601963033905513 := by
  unfold tailWord_3840705
  simp only [CollatzResearch.WordTrace]
  refine ⟨140082019550789200037043569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93388013033859466691362379 140082019550789200037043569)
  ·
    refine ⟨105061514663091900027782677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140082019550789200037043569 105061514663091900027782677)
    ·
      refine ⟨4924758499832432813802313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105061514663091900027782677 4924758499832432813802313)
      ·
        refine ⟨3693568874874324610351735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4924758499832432813802313 3693568874874324610351735)
        ·
          refine ⟨5540353312311486915527603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3693568874874324610351735 5540353312311486915527603)
          ·
            refine ⟨8310529968467230373291405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5540353312311486915527603 8310529968467230373291405)
            ·
              refine ⟨3116448738175211389984277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8310529968467230373291405 3116448738175211389984277)
              ·
                refine ⟨146083534601963033905513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3116448738175211389984277 146083534601963033905513)
                ·
                  rfl

theorem cell22_3840705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 6].length) (baseStart_3840705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840705 prefixEnd_3840705 := by exact prefixLift 3840705
  have htrace : WordTrace (prefixWord ++ tailWord_3840705) baseStart_3840705 baseEnd_3840705 := by
    simpa [prefixWord, tailWord_3840705, baseEnd_3840705] using wordTrace_append hprefix tailTrace_3840705
  have hstable : (prefixWord ++ tailWord_3840705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840705).length < 2 ^ (prefixWord ++ tailWord_3840705).sum := by decide
  have hdescent : baseEnd_3840705 < baseStart_3840705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840868 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 5]
def baseStart_3840868 : Nat := 118140960795 + 3840868 * 2 ^ 59
def prefixEnd_3840868 : Nat := 4983230072969 + 3 ^ 40 * 3840868 * 2
def baseEnd_3840868 : Nat := 438269203216263071108039

theorem tailTrace_3840868 : CollatzResearch.WordTrace tailWord_3840868 prefixEnd_3840868 438269203216263071108039 := by
  unfold tailWord_3840868
  simp only [CollatzResearch.WordTrace]
  refine ⟨70043982324599339437613629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93391976432799119250151505 70043982324599339437613629)
  ·
    refine ⟨26266493371724752289105111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70043982324599339437613629 26266493371724752289105111)
    ·
      refine ⟨39399740057587128433657667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26266493371724752289105111 39399740057587128433657667)
      ·
        refine ⟨59099610086380692650486501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39399740057587128433657667 59099610086380692650486501)
        ·
          refine ⟨11081176891196379871966219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59099610086380692650486501 11081176891196379871966219)
          ·
            refine ⟨16621765336794569807949329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11081176891196379871966219 16621765336794569807949329)
            ·
              refine ⟨12466324002595927355961997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16621765336794569807949329 12466324002595927355961997)
              ·
                refine ⟨4674871500973472758485749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12466324002595927355961997 4674871500973472758485749)
                ·
                  refine ⟨438269203216263071108039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4674871500973472758485749 438269203216263071108039)
                  ·
                    rfl

theorem cell22_3840868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_3840868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840868 prefixEnd_3840868 := by exact prefixLift 3840868
  have htrace : WordTrace (prefixWord ++ tailWord_3840868) baseStart_3840868 baseEnd_3840868 := by
    simpa [prefixWord, tailWord_3840868, baseEnd_3840868] using wordTrace_append hprefix tailTrace_3840868
  have hstable : (prefixWord ++ tailWord_3840868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840868).length < 2 ^ (prefixWord ++ tailWord_3840868).sum := by decide
  have hdescent : baseEnd_3840868 < baseStart_3840868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840928 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 1, 5]
def baseStart_3840928 : Nat := 118140960795 + 3840928 * 2 ^ 59
def prefixEnd_3840928 : Nat := 4983230072969 + 3 ^ 40 * 3840928 * 2
def baseEnd_3840928 : Nat := 1314828148874969056823933

theorem tailTrace_3840928 : CollatzResearch.WordTrace tailWord_3840928 prefixEnd_3840928 1314828148874969056823933 := by
  unfold tailWord_3840928
  simp only [CollatzResearch.WordTrace]
  refine ⟨70045076514490654561205719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93393435352654206081607625 70045076514490654561205719)
  ·
    refine ⟨105067614771735981841808579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70045076514490654561205719 105067614771735981841808579)
    ·
      refine ⟨157601422157603972762712869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105067614771735981841808579 157601422157603972762712869)
      ·
        refine ⟨29550266654550744893008663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157601422157603972762712869 29550266654550744893008663)
        ·
          refine ⟨44325399981826117339512995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29550266654550744893008663 44325399981826117339512995)
          ·
            refine ⟨66488099972739176009269493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44325399981826117339512995 66488099972739176009269493)
            ·
              refine ⟨6233259372444297750869015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66488099972739176009269493 6233259372444297750869015)
              ·
                refine ⟨9349889058666446626303523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6233259372444297750869015 9349889058666446626303523)
                ·
                  refine ⟨14024833587999669939455285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9349889058666446626303523 14024833587999669939455285)
                  ·
                    refine ⟨1314828148874969056823933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14024833587999669939455285 1314828148874969056823933)
                    ·
                      rfl

theorem cell22_3840928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_3840928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840928 prefixEnd_3840928 := by exact prefixLift 3840928
  have htrace : WordTrace (prefixWord ++ tailWord_3840928) baseStart_3840928 baseEnd_3840928 := by
    simpa [prefixWord, tailWord_3840928, baseEnd_3840928] using wordTrace_append hprefix tailTrace_3840928
  have hstable : (prefixWord ++ tailWord_3840928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840928).length < 2 ^ (prefixWord ++ tailWord_3840928).sum := by decide
  have hdescent : baseEnd_3840928 < baseStart_3840928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840964 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 6]
def baseStart_3840964 : Nat := 118140960795 + 3840964 * 2 ^ 59
def prefixEnd_3840964 : Nat := 4983230072969 + 3 ^ 40 * 3840964 * 2
def baseEnd_3840964 : Nat := 438280157470225654307941

theorem tailTrace_3840964 : CollatzResearch.WordTrace tailWord_3840964 prefixEnd_3840964 438280157470225654307941 := by
  unfold tailWord_3840964
  simp only [CollatzResearch.WordTrace]
  refine ⟨70045733028425443635360973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93394310704567258180481297 70045733028425443635360973)
  ·
    refine ⟨26267149885659541363260365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70045733028425443635360973 26267149885659541363260365)
    ·
      refine ⟨9850181207122328011222637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26267149885659541363260365 9850181207122328011222637)
      ·
        refine ⟨3693817952670873004208489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9850181207122328011222637 3693817952670873004208489)
        ·
          refine ⟨2770363464503154753156367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3693817952670873004208489 2770363464503154753156367)
          ·
            refine ⟨4155545196754732129734551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770363464503154753156367 4155545196754732129734551)
            ·
              refine ⟨6233317795132098194601827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155545196754732129734551 6233317795132098194601827)
              ·
                refine ⟨9349976692698147291902741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6233317795132098194601827 9349976692698147291902741)
                ·
                  refine ⟨438280157470225654307941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9349976692698147291902741 438280157470225654307941)
                  ·
                    rfl

theorem cell22_3840964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_3840964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3840964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3840964 prefixEnd_3840964 := by exact prefixLift 3840964
  have htrace : WordTrace (prefixWord ++ tailWord_3840964) baseStart_3840964 baseEnd_3840964 := by
    simpa [prefixWord, tailWord_3840964, baseEnd_3840964] using wordTrace_append hprefix tailTrace_3840964
  have hstable : (prefixWord ++ tailWord_3840964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840964).length < 2 ^ (prefixWord ++ tailWord_3840964).sum := by decide
  have hdescent : baseEnd_3840964 < baseStart_3840964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841020 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 5]
def baseStart_3841020 : Nat := 118140960795 + 3841020 * 2 ^ 59
def prefixEnd_3841020 : Nat := 4983230072969 + 3 ^ 40 * 3841020 * 2
def baseEnd_3841020 : Nat := 438286547451703827841217

theorem tailTrace_3841020 : CollatzResearch.WordTrace tailWord_3841020 prefixEnd_3841020 438286547451703827841217 := by
  unfold tailWord_3841020
  simp only [CollatzResearch.WordTrace]
  refine ⟨70046754272324004417380257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93395672363098672556507009 70046754272324004417380257)
  ·
    refine ⟨52535065704243003313035193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70046754272324004417380257 52535065704243003313035193)
    ·
      refine ⟨39401299278182252484776395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52535065704243003313035193 39401299278182252484776395)
      ·
        refine ⟨59101948917273378727164593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39401299278182252484776395 59101948917273378727164593)
        ·
          refine ⟨44326461687955034045373445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59101948917273378727164593 44326461687955034045373445)
          ·
            refine ⟨8311211566491568883507521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44326461687955034045373445 8311211566491568883507521)
            ·
              refine ⟨6233408674868676662630641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8311211566491568883507521 6233408674868676662630641)
              ·
                refine ⟨4675056506151507496972981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6233408674868676662630641 4675056506151507496972981)
                ·
                  refine ⟨438286547451703827841217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4675056506151507496972981 438286547451703827841217)
                  ·
                    rfl

theorem cell22_3841020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_3841020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841020 prefixEnd_3841020 := by exact prefixLift 3841020
  have htrace : WordTrace (prefixWord ++ tailWord_3841020) baseStart_3841020 baseEnd_3841020 := by
    simpa [prefixWord, tailWord_3841020, baseEnd_3841020] using wordTrace_append hprefix tailTrace_3841020
  have hstable : (prefixWord ++ tailWord_3841020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841020).length < 2 ^ (prefixWord ++ tailWord_3841020).sum := by decide
  have hdescent : baseEnd_3841020 < baseStart_3841020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841048 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 8]
def baseStart_3841048 : Nat := 118140960795 + 3841048 * 2 ^ 59
def prefixEnd_3841048 : Nat := 4983230072969 + 3 ^ 40 * 3841048 * 2
def baseEnd_3841048 : Nat := 438289742442442914607855

theorem tailTrace_3841048 : CollatzResearch.WordTrace tailWord_3841048 prefixEnd_3841048 438289742442442914607855 := by
  unfold tailWord_3841048
  simp only [CollatzResearch.WordTrace]
  refine ⟨70047264894273284808389899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93396353192364379744519865 70047264894273284808389899)
  ·
    refine ⟨105070897341409927212584849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70047264894273284808389899 105070897341409927212584849)
    ·
      refine ⟨78803173006057445409438637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105070897341409927212584849 78803173006057445409438637)
      ·
        refine ⟨29551189877271542028539489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78803173006057445409438637 29551189877271542028539489)
        ·
          refine ⟨22163392407953656521404617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29551189877271542028539489 22163392407953656521404617)
          ·
            refine ⟨16622544305965242391053463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22163392407953656521404617 16622544305965242391053463)
            ·
              refine ⟨24933816458947863586580195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16622544305965242391053463 24933816458947863586580195)
              ·
                refine ⟨37400724688421795379870293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24933816458947863586580195 37400724688421795379870293)
                ·
                  refine ⟨438289742442442914607855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37400724688421795379870293 438289742442442914607855)
                  ·
                    rfl

theorem cell22_3841048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_3841048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841048 prefixEnd_3841048 := by exact prefixLift 3841048
  have htrace : WordTrace (prefixWord ++ tailWord_3841048) baseStart_3841048 baseEnd_3841048 := by
    simpa [prefixWord, tailWord_3841048, baseEnd_3841048] using wordTrace_append hprefix tailTrace_3841048
  have hstable : (prefixWord ++ tailWord_3841048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841048).length < 2 ^ (prefixWord ++ tailWord_3841048).sum := by decide
  have hdescent : baseEnd_3841048 < baseStart_3841048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841050 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_3841050 : Nat := 118140960795 + 3841050 * 2 ^ 59
def prefixEnd_3841050 : Nat := 4983230072969 + 3 ^ 40 * 3841050 * 2
def baseEnd_3841050 : Nat := 1314869911968201405273559

theorem tailTrace_3841050 : CollatzResearch.WordTrace tailWord_3841050 prefixEnd_3841050 1314869911968201405273559 := by
  unfold tailWord_3841050
  simp only [CollatzResearch.WordTrace]
  refine ⟨35023650683634830989588151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93396401823026215972235069 35023650683634830989588151)
  ·
    refine ⟨52535476025452246484382227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35023650683634830989588151 52535476025452246484382227)
    ·
      refine ⟨78803214038178369726573341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52535476025452246484382227 78803214038178369726573341)
      ·
        refine ⟨29551205264316888647465003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78803214038178369726573341 29551205264316888647465003)
        ·
          refine ⟨44326807896475332971197505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29551205264316888647465003 44326807896475332971197505)
          ·
            refine ⟨33245105922356499728398129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44326807896475332971197505 33245105922356499728398129)
            ·
              refine ⟨24933829441767374796298597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33245105922356499728398129 24933829441767374796298597)
              ·
                refine ⟨4675093020331382774305987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24933829441767374796298597 4675093020331382774305987)
                ·
                  refine ⟨7012639530497074161458981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675093020331382774305987 7012639530497074161458981)
                  ·
                    refine ⟨1314869911968201405273559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7012639530497074161458981 1314869911968201405273559)
                    ·
                      rfl

theorem cell22_3841050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_3841050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841050 prefixEnd_3841050 := by exact prefixLift 3841050
  have htrace : WordTrace (prefixWord ++ tailWord_3841050) baseStart_3841050 baseEnd_3841050 := by
    simpa [prefixWord, tailWord_3841050, baseEnd_3841050] using wordTrace_append hprefix tailTrace_3841050
  have hstable : (prefixWord ++ tailWord_3841050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841050).length < 2 ^ (prefixWord ++ tailWord_3841050).sum := by decide
  have hdescent : baseEnd_3841050 < baseStart_3841050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841123 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 1, 8]
def baseStart_3841123 : Nat := 118140960795 + 3841123 * 2 ^ 59
def prefixEnd_3841123 : Nat := 4983230072969 + 3 ^ 40 * 3841123 * 2
def baseEnd_3841123 : Nat := 1314894901360053548198335

theorem tailTrace_3841123 : CollatzResearch.WordTrace tailWord_3841123 prefixEnd_3841123 1314894901360053548198335 := by
  unfold tailWord_3841123
  simp only [CollatzResearch.WordTrace]
  refine ⟨140097265263274857425760023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93398176842183238283840015 140097265263274857425760023)
  ·
    refine ⟨210145897894912286138640035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140097265263274857425760023 210145897894912286138640035)
    ·
      refine ⟨315218846842368429207960053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210145897894912286138640035 315218846842368429207960053)
      ·
        refine ⟨29551766891472040238246255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 315218846842368429207960053 29551766891472040238246255)
        ·
          refine ⟨44327650337208060357369383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29551766891472040238246255 44327650337208060357369383)
          ·
            refine ⟨66491475505812090536054075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44327650337208060357369383 66491475505812090536054075)
            ·
              refine ⟨99737213258718135804081113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66491475505812090536054075 99737213258718135804081113)
              ·
                refine ⟨74802909944038601853060835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99737213258718135804081113 74802909944038601853060835)
                ·
                  refine ⟨112204364916057902779591253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74802909944038601853060835 112204364916057902779591253)
                  ·
                    refine ⟨1314894901360053548198335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112204364916057902779591253 1314894901360053548198335)
                    ·
                      rfl

theorem cell22_3841123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_3841123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841123 prefixEnd_3841123 := by exact prefixLift 3841123
  have htrace : WordTrace (prefixWord ++ tailWord_3841123) baseStart_3841123 baseEnd_3841123 := by
    simpa [prefixWord, tailWord_3841123, baseEnd_3841123] using wordTrace_append hprefix tailTrace_3841123
  have hstable : (prefixWord ++ tailWord_3841123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841123).length < 2 ^ (prefixWord ++ tailWord_3841123).sum := by decide
  have hdescent : baseEnd_3841123 < baseStart_3841123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841155 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 5]
def baseStart_3841155 : Nat := 118140960795 + 3841155 * 2 ^ 59
def prefixEnd_3841155 : Nat := 4983230072969 + 3 ^ 40 * 3841155 * 2
def baseEnd_3841155 : Nat := 438301951871338710466079

theorem tailTrace_3841155 : CollatzResearch.WordTrace tailWord_3841155 prefixEnd_3841155 438301951871338710466079 := by
  unfold tailWord_3841155
  simp only [CollatzResearch.WordTrace]
  refine ⟨140098432399158926890924919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93398954932772617927283279 140098432399158926890924919)
  ·
    refine ⟨210147648598738390336387379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140098432399158926890924919 210147648598738390336387379)
    ·
      refine ⟨315221472898107585504581069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210147648598738390336387379 315221472898107585504581069)
      ·
        refine ⟨118208052336790344564217901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315221472898107585504581069 118208052336790344564217901)
        ·
          refine ⟨44328019626296379211581713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118208052336790344564217901 44328019626296379211581713)
          ·
            refine ⟨33246014719722284408686285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44328019626296379211581713 33246014719722284408686285)
            ·
              refine ⟨12467255519895856653257357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33246014719722284408686285 12467255519895856653257357)
              ·
                refine ⟨4675220819960946244971509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12467255519895856653257357 4675220819960946244971509)
                ·
                  refine ⟨438301951871338710466079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4675220819960946244971509 438301951871338710466079)
                  ·
                    rfl

theorem cell22_3841155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 5].length) (baseStart_3841155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841155 prefixEnd_3841155 := by exact prefixLift 3841155
  have htrace : WordTrace (prefixWord ++ tailWord_3841155) baseStart_3841155 baseEnd_3841155 := by
    simpa [prefixWord, tailWord_3841155, baseEnd_3841155] using wordTrace_append hprefix tailTrace_3841155
  have hstable : (prefixWord ++ tailWord_3841155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841155).length < 2 ^ (prefixWord ++ tailWord_3841155).sum := by decide
  have hdescent : baseEnd_3841155 < baseStart_3841155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841215 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 1, 5]
def baseStart_3841215 : Nat := 118140960795 + 3841215 * 2 ^ 59
def prefixEnd_3841215 : Nat := 4983230072969 + 3 ^ 40 * 3841215 * 2
def baseEnd_3841215 : Nat := 1314926394840195974898053

theorem tailTrace_3841215 : CollatzResearch.WordTrace tailWord_3841215 prefixEnd_3841215 1314926394840195974898053 := by
  unfold tailWord_3841215
  simp only [CollatzResearch.WordTrace]
  refine ⟨140100620778941557138109099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93400413852627704758739399 140100620778941557138109099)
  ·
    refine ⟨210150931168412335707163649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140100620778941557138109099 210150931168412335707163649)
    ·
      refine ⟨157613198376309251780372737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210150931168412335707163649 157613198376309251780372737)
      ·
        refine ⟨118209898782231938835279553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157613198376309251780372737 118209898782231938835279553)
        ·
          refine ⟨88657424086673954126459665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118209898782231938835279553 88657424086673954126459665)
          ·
            refine ⟨66493068065005465594844749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88657424086673954126459665 66493068065005465594844749)
            ·
              refine ⟨24934900524377049598066781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66493068065005465594844749 24934900524377049598066781)
              ·
                refine ⟨9350587696641393599275043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24934900524377049598066781 9350587696641393599275043)
                ·
                  refine ⟨14025881544962090398912565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9350587696641393599275043 14025881544962090398912565)
                  ·
                    refine ⟨1314926394840195974898053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14025881544962090398912565 1314926394840195974898053)
                    ·
                      rfl

theorem cell22_3841215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_3841215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841215 prefixEnd_3841215 := by exact prefixLift 3841215
  have htrace : WordTrace (prefixWord ++ tailWord_3841215) baseStart_3841215 baseEnd_3841215 := by
    simpa [prefixWord, tailWord_3841215, baseEnd_3841215] using wordTrace_append hprefix tailTrace_3841215
  have hstable : (prefixWord ++ tailWord_3841215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841215).length < 2 ^ (prefixWord ++ tailWord_3841215).sum := by decide
  have hdescent : baseEnd_3841215 < baseStart_3841215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841217 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 8]
def baseStart_3841217 : Nat := 118140960795 + 3841217 * 2 ^ 59
def prefixEnd_3841217 : Nat := 4983230072969 + 3 ^ 40 * 3841217 * 2
def baseEnd_3841217 : Nat := 438309026493689545449349

theorem tailTrace_3841217 : CollatzResearch.WordTrace tailWord_3841217 prefixEnd_3841217 438309026493689545449349 := by
  unfold tailWord_3841217
  simp only [CollatzResearch.WordTrace]
  refine ⟨140100693724934311479681905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93400462483289540986454603 140100693724934311479681905)
  ·
    refine ⟨105075520293700733609761429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140100693724934311479681905 105075520293700733609761429)
    ·
      refine ⟨4925415013767221887957567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105075520293700733609761429 4925415013767221887957567)
      ·
        refine ⟨7388122520650832831936351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4925415013767221887957567 7388122520650832831936351)
        ·
          refine ⟨11082183780976249247904527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7388122520650832831936351 11082183780976249247904527)
          ·
            refine ⟨16623275671464373871856791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11082183780976249247904527 16623275671464373871856791)
            ·
              refine ⟨24934913507196560807785187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16623275671464373871856791 24934913507196560807785187)
              ·
                refine ⟨37402370260794841211677781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24934913507196560807785187 37402370260794841211677781)
                ·
                  refine ⟨438309026493689545449349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37402370260794841211677781 438309026493689545449349)
                  ·
                    rfl

theorem cell22_3841217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_3841217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841217 prefixEnd_3841217 := by exact prefixLift 3841217
  have htrace : WordTrace (prefixWord ++ tailWord_3841217) baseStart_3841217 baseEnd_3841217 := by
    simpa [prefixWord, tailWord_3841217, baseEnd_3841217] using wordTrace_append hprefix tailTrace_3841217
  have hstable : (prefixWord ++ tailWord_3841217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841217).length < 2 ^ (prefixWord ++ tailWord_3841217).sum := by decide
  have hdescent : baseEnd_3841217 < baseStart_3841217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841234 : List Nat := [3, 2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_3841234 : Nat := 118140960795 + 3841234 * 2 ^ 59
def prefixEnd_3841234 : Nat := 4983230072969 + 3 ^ 40 * 3841234 * 2
def baseEnd_3841234 : Nat := 438310966309495419557665

theorem tailTrace_3841234 : CollatzResearch.WordTrace tailWord_3841234 prefixEnd_3841234 438310966309495419557665 := by
  unfold tailWord_3841234
  simp only [CollatzResearch.WordTrace]
  refine ⟨35025328441468180845762689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93400875843915148922033837 35025328441468180845762689)
  ·
    refine ⟨26268996331101135634322017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35025328441468180845762689 26268996331101135634322017)
    ·
      refine ⟨19701747248325851725741513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26268996331101135634322017 19701747248325851725741513)
      ·
        refine ⟨14776310436244388794306135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19701747248325851725741513 14776310436244388794306135)
        ·
          refine ⟨22164465654366583191459203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14776310436244388794306135 22164465654366583191459203)
          ·
            refine ⟨33246698481549874787188805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22164465654366583191459203 33246698481549874787188805)
            ·
              refine ⟨6233755965290601522597901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33246698481549874787188805 6233755965290601522597901)
              ·
                refine ⟨2337658486983975570974213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6233755965290601522597901 2337658486983975570974213)
                ·
                  refine ⟨438310966309495419557665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2337658486983975570974213 438310966309495419557665)
                  ·
                    rfl

theorem cell22_3841234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_3841234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841234 prefixEnd_3841234 := by exact prefixLift 3841234
  have htrace : WordTrace (prefixWord ++ tailWord_3841234) baseStart_3841234 baseEnd_3841234 := by
    simpa [prefixWord, tailWord_3841234, baseEnd_3841234] using wordTrace_append hprefix tailTrace_3841234
  have hstable : (prefixWord ++ tailWord_3841234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841234).length < 2 ^ (prefixWord ++ tailWord_3841234).sum := by decide
  have hdescent : baseEnd_3841234 < baseStart_3841234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841236 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_3841236 : Nat := 118140960795 + 3841236 * 2 ^ 59
def prefixEnd_3841236 : Nat := 4983230072969 + 3 ^ 40 * 3841236 * 2
def baseEnd_3841236 : Nat := 1314933583569358920122989

theorem tailTrace_3841236 : CollatzResearch.WordTrace tailWord_3841236 prefixEnd_3841236 1314933583569358920122989 := by
  unfold tailWord_3841236
  simp only [CollatzResearch.WordTrace]
  refine ⟨70050693355932738862311781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93400924474576985149749041 70050693355932738862311781)
  ·
    refine ⟨13134505004237388536683459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70050693355932738862311781 13134505004237388536683459)
    ·
      refine ⟨19701757506356082805025189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13134505004237388536683459 19701757506356082805025189)
      ·
        refine ⟨3694079532441765525942223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19701757506356082805025189 3694079532441765525942223)
        ·
          refine ⟨5541119298662648288913335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3694079532441765525942223 5541119298662648288913335)
          ·
            refine ⟨8311678947993972433370003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541119298662648288913335 8311678947993972433370003)
            ·
              refine ⟨12467518421990958650055005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8311678947993972433370003 12467518421990958650055005)
              ·
                refine ⟨4675319408246609493770627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12467518421990958650055005 4675319408246609493770627)
                ·
                  refine ⟨7012979112369914240655941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675319408246609493770627 7012979112369914240655941)
                  ·
                    refine ⟨1314933583569358920122989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7012979112369914240655941 1314933583569358920122989)
                    ·
                      rfl

theorem cell22_3841236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_3841236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841236 prefixEnd_3841236 := by exact prefixLift 3841236
  have htrace : WordTrace (prefixWord ++ tailWord_3841236) baseStart_3841236 baseEnd_3841236 := by
    simpa [prefixWord, tailWord_3841236, baseEnd_3841236] using wordTrace_append hprefix tailTrace_3841236
  have hstable : (prefixWord ++ tailWord_3841236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841236).length < 2 ^ (prefixWord ++ tailWord_3841236).sum := by decide
  have hdescent : baseEnd_3841236 < baseStart_3841236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841249 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 2, 3]
def baseStart_3841249 : Nat := 118140960795 + 3841249 * 2 ^ 59
def prefixEnd_3841249 : Nat := 4983230072969 + 3 ^ 40 * 3841249 * 2
def baseEnd_3841249 : Nat := 1314938033735031219547949

theorem tailTrace_3841249 : CollatzResearch.WordTrace tailWord_3841249 prefixEnd_3841249 1314938033735031219547949 := by
  unfold tailWord_3841249
  simp only [CollatzResearch.WordTrace]
  refine ⟨140101860860818380944846801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93401240573878920629897867 140101860860818380944846801)
  ·
    refine ⟨105076395645613785708635101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140101860860818380944846801 105076395645613785708635101)
    ·
      refine ⟨39403648367105169640738163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105076395645613785708635101 39403648367105169640738163)
      ·
        refine ⟨59105472550657754461107245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39403648367105169640738163 59105472550657754461107245)
        ·
          refine ⟨22164552206496657922915217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59105472550657754461107245 22164552206496657922915217)
          ·
            refine ⟨16623414154872493442186413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22164552206496657922915217 16623414154872493442186413)
            ·
              refine ⟨6233780308077185040819905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16623414154872493442186413 6233780308077185040819905)
              ·
                refine ⟨4675335231057888780614929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6233780308077185040819905 4675335231057888780614929)
                ·
                  refine ⟨3506501423293416585461197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4675335231057888780614929 3506501423293416585461197)
                  ·
                    refine ⟨1314938033735031219547949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3506501423293416585461197 1314938033735031219547949)
                    ·
                      rfl

theorem cell22_3841249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_3841249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841249 prefixEnd_3841249 := by exact prefixLift 3841249
  have htrace : WordTrace (prefixWord ++ tailWord_3841249) baseStart_3841249 baseEnd_3841249 := by
    simpa [prefixWord, tailWord_3841249, baseEnd_3841249] using wordTrace_append hprefix tailTrace_3841249
  have hstable : (prefixWord ++ tailWord_3841249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841249).length < 2 ^ (prefixWord ++ tailWord_3841249).sum := by decide
  have hdescent : baseEnd_3841249 < baseStart_3841249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841266 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_3841266 : Nat := 118140960795 + 3841266 * 2 ^ 59
def prefixEnd_3841266 : Nat := 4983230072969 + 3 ^ 40 * 3841266 * 2
def baseEnd_3841266 : Nat := 1314943853182448841872897

theorem tailTrace_3841266 : CollatzResearch.WordTrace tailWord_3841266 prefixEnd_3841266 1314943853182448841872897 := by
  unfold tailWord_3841266
  simp only [CollatzResearch.WordTrace]
  refine ⟨35025620225439198212053913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93401653934504528565477101 35025620225439198212053913)
  ·
    refine ⟨26269215169079398659040435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35025620225439198212053913 26269215169079398659040435)
    ·
      refine ⟨39403822753619097988560653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26269215169079398659040435 39403822753619097988560653)
      ·
        refine ⟨14776433532607161745710245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39403822753619097988560653 14776433532607161745710245)
        ·
          refine ⟨2770581287363842827320671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14776433532607161745710245 2770581287363842827320671)
          ·
            refine ⟨4155871931045764240981007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770581287363842827320671 4155871931045764240981007)
            ·
              refine ⟨6233807896568646361471511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155871931045764240981007 6233807896568646361471511)
              ·
                refine ⟨9350711844852969542207267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6233807896568646361471511 9350711844852969542207267)
                ·
                  refine ⟨14026067767279454313310901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9350711844852969542207267 14026067767279454313310901)
                  ·
                    refine ⟨1314943853182448841872897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14026067767279454313310901 1314943853182448841872897)
                    ·
                      rfl

theorem cell22_3841266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_3841266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841266 prefixEnd_3841266 := by exact prefixLift 3841266
  have htrace : WordTrace (prefixWord ++ tailWord_3841266) baseStart_3841266 baseEnd_3841266 := by
    simpa [prefixWord, tailWord_3841266, baseEnd_3841266] using wordTrace_append hprefix tailTrace_3841266
  have hstable : (prefixWord ++ tailWord_3841266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841266).length < 2 ^ (prefixWord ++ tailWord_3841266).sum := by decide
  have hdescent : baseEnd_3841266 < baseStart_3841266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841311 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 3, 3]
def baseStart_3841311 : Nat := 118140960795 + 3841311 * 2 ^ 59
def prefixEnd_3841311 : Nat := 4983230072969 + 3 ^ 40 * 3841311 * 2
def baseEnd_3841311 : Nat := 1314959257602083724497759

theorem tailTrace_3841311 : CollatzResearch.WordTrace tailWord_3841311 prefixEnd_3841311 1314959257602083724497759 := by
  unfold tailWord_3841311
  simp only [CollatzResearch.WordTrace]
  refine ⟨140104122186593765533603787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93402748124395843689069191 140104122186593765533603787)
  ·
    refine ⟨210156183279890648300405681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140104122186593765533603787 210156183279890648300405681)
    ·
      refine ⟨157617137459917986225304261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210156183279890648300405681 157617137459917986225304261)
      ·
        refine ⟨29553213273734622417244549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157617137459917986225304261 29553213273734622417244549)
        ·
          refine ⟨5541227488825241703233353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29553213273734622417244549 5541227488825241703233353)
          ·
            refine ⟨4155920616618931277425015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5541227488825241703233353 4155920616618931277425015)
            ·
              refine ⟨6233880924928396916137523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155920616618931277425015 6233880924928396916137523)
              ·
                refine ⟨9350821387392595374206285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6233880924928396916137523 9350821387392595374206285)
                ·
                  refine ⟨3506558020272223265327357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9350821387392595374206285 3506558020272223265327357)
                  ·
                    refine ⟨1314959257602083724497759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3506558020272223265327357 1314959257602083724497759)
                    ·
                      rfl

theorem cell22_3841311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 3].length) (baseStart_3841311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841311 prefixEnd_3841311 := by exact prefixLift 3841311
  have htrace : WordTrace (prefixWord ++ tailWord_3841311) baseStart_3841311 baseEnd_3841311 := by
    simpa [prefixWord, tailWord_3841311, baseEnd_3841311] using wordTrace_append hprefix tailTrace_3841311
  have hstable : (prefixWord ++ tailWord_3841311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841311).length < 2 ^ (prefixWord ++ tailWord_3841311).sum := by decide
  have hdescent : baseEnd_3841311 < baseStart_3841311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841373 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3841373 : Nat := 118140960795 + 3841373 * 2 ^ 59
def prefixEnd_3841373 : Nat := 4983230072969 + 3 ^ 40 * 3841373 * 2
def baseEnd_3841373 : Nat := 1314980481469136229447569

theorem tailTrace_3841373 : CollatzResearch.WordTrace tailWord_3841373 prefixEnd_3841373 1314980481469136229447569 := by
  unfold tailWord_3841373
  simp only [CollatzResearch.WordTrace]
  refine ⟨140106383512369150122360773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93404255674912766748240515 140106383512369150122360773)
  ·
    refine ⟨26269946908569215647942645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140106383512369150122360773 26269946908569215647942645)
    ·
      refine ⟨2462807522678363966994623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26269946908569215647942645 2462807522678363966994623)
      ·
        refine ⟨3694211284017545950491935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462807522678363966994623 3694211284017545950491935)
        ·
          refine ⟨5541316926026318925737903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3694211284017545950491935 5541316926026318925737903)
          ·
            refine ⟨8311975389039478388606855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541316926026318925737903 8311975389039478388606855)
            ·
              refine ⟨12467963083559217582910283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8311975389039478388606855 12467963083559217582910283)
              ·
                refine ⟨18701944625338826374365425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12467963083559217582910283 18701944625338826374365425)
                ·
                  refine ⟨14026458469004119780774069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18701944625338826374365425 14026458469004119780774069)
                  ·
                    refine ⟨1314980481469136229447569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14026458469004119780774069 1314980481469136229447569)
                    ·
                      rfl

theorem cell22_3841373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3841373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841373 prefixEnd_3841373 := by exact prefixLift 3841373
  have htrace : WordTrace (prefixWord ++ tailWord_3841373) baseStart_3841373 baseEnd_3841373 := by
    simpa [prefixWord, tailWord_3841373, baseEnd_3841373] using wordTrace_append hprefix tailTrace_3841373
  have hstable : (prefixWord ++ tailWord_3841373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841373).length < 2 ^ (prefixWord ++ tailWord_3841373).sum := by decide
  have hdescent : baseEnd_3841373 < baseStart_3841373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841429 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 3, 3]
def baseStart_3841429 : Nat := 118140960795 + 3841429 * 2 ^ 59
def prefixEnd_3841429 : Nat := 4983230072969 + 3 ^ 40 * 3841429 * 2
def baseEnd_3841429 : Nat := 1314999651413570750047397

theorem tailTrace_3841429 : CollatzResearch.WordTrace tailWord_3841429 prefixEnd_3841429 1314999651413570750047397 := by
  unfold tailWord_3841429
  simp only [CollatzResearch.WordTrace]
  refine ⟨140108426000166271686399341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93405617333444181124266227 140108426000166271686399341)
  ·
    refine ⟨52540659750062351882399753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140108426000166271686399341 52540659750062351882399753)
    ·
      refine ⟨39405494812546763911799815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52540659750062351882399753 39405494812546763911799815)
      ·
        refine ⟨59108242218820145867699723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39405494812546763911799815 59108242218820145867699723)
        ·
          refine ⟨88662363328230218801549585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59108242218820145867699723 88662363328230218801549585)
          ·
            refine ⟨66496772496172664101162189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88662363328230218801549585 66496772496172664101162189)
            ·
              refine ⟨24936289686064749037935821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66496772496172664101162189 24936289686064749037935821)
              ·
                refine ⟨9351108632274280889225933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24936289686064749037935821 9351108632274280889225933)
                ·
                  refine ⟨3506665737102855333459725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9351108632274280889225933 3506665737102855333459725)
                  ·
                    refine ⟨1314999651413570750047397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3506665737102855333459725 1314999651413570750047397)
                    ·
                      rfl

theorem cell22_3841429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_3841429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841429 prefixEnd_3841429 := by exact prefixLift 3841429
  have htrace : WordTrace (prefixWord ++ tailWord_3841429) baseStart_3841429 baseEnd_3841429 := by
    simpa [prefixWord, tailWord_3841429, baseEnd_3841429] using wordTrace_append hprefix tailTrace_3841429
  have hstable : (prefixWord ++ tailWord_3841429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841429).length < 2 ^ (prefixWord ++ tailWord_3841429).sum := by decide
  have hdescent : baseEnd_3841429 < baseStart_3841429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841448 : List Nat := [2, 1, 6, 1, 2, 2, 2, 6]
def baseStart_3841448 : Nat := 118140960795 + 3841448 * 2 ^ 59
def prefixEnd_3841448 : Nat := 4983230072969 + 3 ^ 40 * 3841448 * 2
def baseEnd_3841448 : Nat := 146111795055762337091371

theorem tailTrace_3841448 : CollatzResearch.WordTrace tailWord_3841448 prefixEnd_3841448 146111795055762337091371 := by
  unfold tailWord_3841448
  simp only [CollatzResearch.WordTrace]
  refine ⟨70054559493548718965670499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93406079324731625287560665 70054559493548718965670499)
  ·
    refine ⟨105081839240323078448505749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70054559493548718965670499 105081839240323078448505749)
    ·
      refine ⟨4925711214390144302273707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105081839240323078448505749 4925711214390144302273707)
      ·
        refine ⟨7388566821585216453410561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4925711214390144302273707 7388566821585216453410561)
        ·
          refine ⟨5541425116188912340057921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7388566821585216453410561 5541425116188912340057921)
          ·
            refine ⟨4156068837141684255043441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5541425116188912340057921 4156068837141684255043441)
            ·
              refine ⟨3117051627856263191282581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4156068837141684255043441 3117051627856263191282581)
              ·
                refine ⟨146111795055762337091371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3117051627856263191282581 146111795055762337091371)
                ·
                  rfl

theorem cell22_3841448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 6].length) (baseStart_3841448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841448 prefixEnd_3841448 := by exact prefixLift 3841448
  have htrace : WordTrace (prefixWord ++ tailWord_3841448) baseStart_3841448 baseEnd_3841448 := by
    simpa [prefixWord, tailWord_3841448, baseEnd_3841448] using wordTrace_append hprefix tailTrace_3841448
  have hstable : (prefixWord ++ tailWord_3841448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841448).length < 2 ^ (prefixWord ++ tailWord_3841448).sum := by decide
  have hdescent : baseEnd_3841448 < baseStart_3841448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841519 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 6, 3]
def baseStart_3841519 : Nat := 118140960795 + 3841519 * 2 ^ 59
def prefixEnd_3841519 : Nat := 4983230072969 + 3 ^ 40 * 3841519 * 2
def baseEnd_3841519 : Nat := 1315030460252840515297121

theorem tailTrace_3841519 : CollatzResearch.WordTrace tailWord_3841519 prefixEnd_3841519 1315030460252840515297121 := by
  unfold tailWord_3841519
  simp only [CollatzResearch.WordTrace]
  refine ⟨140111708569840217057175611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93407805713226811371450407 140111708569840217057175611)
  ·
    refine ⟨210167562854760325585763417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140111708569840217057175611 210167562854760325585763417)
    ·
      refine ⟨157625672141070244189322563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210167562854760325585763417 157625672141070244189322563)
      ·
        refine ⟨236438508211605366283983845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157625672141070244189322563 236438508211605366283983845)
        ·
          refine ⟨44332220289676006178246971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236438508211605366283983845 44332220289676006178246971)
          ·
            refine ⟨66498330434514009267370457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44332220289676006178246971 66498330434514009267370457)
            ·
              refine ⟨49873747825885506950527843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66498330434514009267370457 49873747825885506950527843)
              ·
                refine ⟨74810621738828260425791765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49873747825885506950527843 74810621738828260425791765)
                ·
                  refine ⟨3506747894007574707458989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74810621738828260425791765 3506747894007574707458989)
                  ·
                    refine ⟨1315030460252840515297121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3506747894007574707458989 1315030460252840515297121)
                    ·
                      rfl

theorem cell22_3841519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 3].length) (baseStart_3841519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841519 prefixEnd_3841519 := by exact prefixLift 3841519
  have htrace : WordTrace (prefixWord ++ tailWord_3841519) baseStart_3841519 baseEnd_3841519 := by
    simpa [prefixWord, tailWord_3841519, baseEnd_3841519] using wordTrace_append hprefix tailTrace_3841519
  have hstable : (prefixWord ++ tailWord_3841519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841519).length < 2 ^ (prefixWord ++ tailWord_3841519).sum := by decide
  have hdescent : baseEnd_3841519 < baseStart_3841519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841568 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 2, 4]
def baseStart_3841568 : Nat := 118140960795 + 3841568 * 2 ^ 59
def prefixEnd_3841568 : Nat := 4983230072969 + 3 ^ 40 * 3841568 * 2
def baseEnd_3841568 : Nat := 1315047233954220720821971

theorem tailTrace_3841568 : CollatzResearch.WordTrace tailWord_3841568 prefixEnd_3841568 1315047233954220720821971 := by
  unfold tailWord_3841568
  simp only [CollatzResearch.WordTrace]
  refine ⟨70056747873331349212854679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93408997164441798950472905 70056747873331349212854679)
  ·
    refine ⟨105085121809997023819282019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70056747873331349212854679 105085121809997023819282019)
    ·
      refine ⟨157627682714995535728923029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105085121809997023819282019 157627682714995535728923029)
      ·
        refine ⟨7388797627265415737293267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157627682714995535728923029 7388797627265415737293267)
        ·
          refine ⟨11083196440898123605939901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7388797627265415737293267 11083196440898123605939901)
          ·
            refine ⟨4156198665336796352227463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11083196440898123605939901 4156198665336796352227463)
            ·
              refine ⟨6234297998005194528341195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4156198665336796352227463 6234297998005194528341195)
              ·
                refine ⟨9351446997007791792511793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234297998005194528341195 9351446997007791792511793)
                ·
                  refine ⟨7013585247755843844383845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9351446997007791792511793 7013585247755843844383845)
                  ·
                    refine ⟨1315047233954220720821971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7013585247755843844383845 1315047233954220720821971)
                    ·
                      rfl

theorem cell22_3841568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 4].length) (baseStart_3841568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841568 prefixEnd_3841568 := by exact prefixLift 3841568
  have htrace : WordTrace (prefixWord ++ tailWord_3841568) baseStart_3841568 baseEnd_3841568 := by
    simpa [prefixWord, tailWord_3841568, baseEnd_3841568] using wordTrace_append hprefix tailTrace_3841568
  have hstable : (prefixWord ++ tailWord_3841568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841568).length < 2 ^ (prefixWord ++ tailWord_3841568).sum := by decide
  have hdescent : baseEnd_3841568 < baseStart_3841568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841594 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_3841594 : Nat := 118140960795 + 3841594 * 2 ^ 59
def prefixEnd_3841594 : Nat := 4983230072969 + 3 ^ 40 * 3841594 * 2
def baseEnd_3841594 : Nat := 438352044761855106557297

theorem tailTrace_3841594 : CollatzResearch.WordTrace tailWord_3841594 prefixEnd_3841594 438352044761855106557297 := by
  unfold tailWord_3841594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35028611011142126216538959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93409629363045669910770557 35028611011142126216538959)
  ·
    refine ⟨52542916516713189324808439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35028611011142126216538959 52542916516713189324808439)
    ·
      refine ⟨78814374775069783987212659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52542916516713189324808439 78814374775069783987212659)
      ·
        refine ⟨118221562162604675980818989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78814374775069783987212659 118221562162604675980818989)
        ·
          refine ⟨44333085810976753492807121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118221562162604675980818989 44333085810976753492807121)
          ·
            refine ⟨33249814358232565119605341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44333085810976753492807121 33249814358232565119605341)
            ·
              refine ⟨12468680384337211919852003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33249814358232565119605341 12468680384337211919852003)
              ·
                refine ⟨18703020576505817879778005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12468680384337211919852003 18703020576505817879778005)
                ·
                  refine ⟨438352044761855106557297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18703020576505817879778005 438352044761855106557297)
                  ·
                    rfl

theorem cell22_3841594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_3841594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841594 prefixEnd_3841594 := by exact prefixLift 3841594
  have htrace : WordTrace (prefixWord ++ tailWord_3841594) baseStart_3841594 baseEnd_3841594 := by
    simpa [prefixWord, tailWord_3841594, baseEnd_3841594] using wordTrace_append hprefix tailTrace_3841594
  have hstable : (prefixWord ++ tailWord_3841594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841594).length < 2 ^ (prefixWord ++ tailWord_3841594).sum := by decide
  have hdescent : baseEnd_3841594 < baseStart_3841594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841639 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 8]
def baseStart_3841639 : Nat := 118140960795 + 3841639 * 2 ^ 59
def prefixEnd_3841639 : Nat := 4983230072969 + 3 ^ 40 * 3841639 * 2
def baseEnd_3841639 : Nat := 438357179568400067432251

theorem tailTrace_3841639 : CollatzResearch.WordTrace tailWord_3841639 prefixEnd_3841639 438357179568400067432251 := by
  unfold tailWord_3841639
  simp only [CollatzResearch.WordTrace]
  refine ⟨140116085329405477551543971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93410723552936985034362647 140116085329405477551543971)
  ·
    refine ⟨210174127994108216327315957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140116085329405477551543971 210174127994108216327315957)
    ·
      refine ⟨19703824499447645280685871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210174127994108216327315957 19703824499447645280685871)
      ·
        refine ⟨29555736749171467921028807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19703824499447645280685871 29555736749171467921028807)
        ·
          refine ⟨44333605123757201881543211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29555736749171467921028807 44333605123757201881543211)
          ·
            refine ⟨66500407685635802822314817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44333605123757201881543211 66500407685635802822314817)
            ·
              refine ⟨49875305764226852116736113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66500407685635802822314817 49875305764226852116736113)
              ·
                refine ⟨37406479323170139087552085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49875305764226852116736113 37406479323170139087552085)
                ·
                  refine ⟨438357179568400067432251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37406479323170139087552085 438357179568400067432251)
                  ·
                    rfl

theorem cell22_3841639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 8].length) (baseStart_3841639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841639 prefixEnd_3841639 := by exact prefixLift 3841639
  have htrace : WordTrace (prefixWord ++ tailWord_3841639) baseStart_3841639 baseEnd_3841639 := by
    simpa [prefixWord, tailWord_3841639, baseEnd_3841639] using wordTrace_append hprefix tailTrace_3841639
  have hstable : (prefixWord ++ tailWord_3841639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841639).length < 2 ^ (prefixWord ++ tailWord_3841639).sum := by decide
  have hdescent : baseEnd_3841639 < baseStart_3841639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841641 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 1, 4]
def baseStart_3841641 : Nat := 118140960795 + 3841641 * 2 ^ 59
def prefixEnd_3841641 : Nat := 4983230072969 + 3 ^ 40 * 3841641 * 2
def baseEnd_3841641 : Nat := 1315072223346072863746747

theorem tailTrace_3841641 : CollatzResearch.WordTrace tailWord_3841641 prefixEnd_3841641 1315072223346072863746747 := by
  unfold tailWord_3841641
  simp only [CollatzResearch.WordTrace]
  refine ⟨140116158275398231893116777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93410772183598821262077851 140116158275398231893116777)
  ·
    refine ⟨105087118706548673919837583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140116158275398231893116777 105087118706548673919837583)
    ·
      refine ⟨157630678059823010879756375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105087118706548673919837583 157630678059823010879756375)
      ·
        refine ⟨236446017089734516319634563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157630678059823010879756375 236446017089734516319634563)
        ·
          refine ⟨354669025634601774479451845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236446017089734516319634563 354669025634601774479451845)
          ·
            refine ⟨66500442306487832714897221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354669025634601774479451845 66500442306487832714897221)
            ·
              refine ⟨12468832932466468634043229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66500442306487832714897221 12468832932466468634043229)
              ·
                refine ⟨4675812349674925737766211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12468832932466468634043229 4675812349674925737766211)
                ·
                  refine ⟨7013718524512388606649317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675812349674925737766211 7013718524512388606649317)
                  ·
                    refine ⟨1315072223346072863746747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7013718524512388606649317 1315072223346072863746747)
                    ·
                      rfl

theorem cell22_3841641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_3841641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841641 prefixEnd_3841641 := by exact prefixLift 3841641
  have htrace : WordTrace (prefixWord ++ tailWord_3841641) baseStart_3841641 baseEnd_3841641 := by
    simpa [prefixWord, tailWord_3841641, baseEnd_3841641] using wordTrace_append hprefix tailTrace_3841641
  have hstable : (prefixWord ++ tailWord_3841641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841641).length < 2 ^ (prefixWord ++ tailWord_3841641).sum := by decide
  have hdescent : baseEnd_3841641 < baseStart_3841641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841763 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 7]
def baseStart_3841763 : Nat := 118140960795 + 3841763 * 2 ^ 59
def prefixEnd_3841763 : Nat := 4983230072969 + 3 ^ 40 * 3841763 * 2
def baseEnd_3841763 : Nat := 438371328813101737398791

theorem tailTrace_3841763 : CollatzResearch.WordTrace tailWord_3841763 prefixEnd_3841763 438371328813101737398791 := by
  unfold tailWord_3841763
  simp only [CollatzResearch.WordTrace]
  refine ⟨140120607980956246729057943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93413738653970831152705295 140120607980956246729057943)
  ·
    refine ⟨210180911971434370093586915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140120607980956246729057943 210180911971434370093586915)
    ·
      refine ⟨315271367957151555140380373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210180911971434370093586915 315271367957151555140380373)
      ·
        refine ⟨7389172686495739573602665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 315271367957151555140380373 7389172686495739573602665)
        ·
          refine ⟨5541879514871804680201999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7389172686495739573602665 5541879514871804680201999)
          ·
            refine ⟨8312819272307707020302999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541879514871804680201999 8312819272307707020302999)
            ·
              refine ⟨12469228908461560530454499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8312819272307707020302999 12469228908461560530454499)
              ·
                refine ⟨18703843362692340795681749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12469228908461560530454499 18703843362692340795681749)
                ·
                  refine ⟨438371328813101737398791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18703843362692340795681749 438371328813101737398791)
                  ·
                    rfl

theorem cell22_3841763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 7].length) (baseStart_3841763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841763 prefixEnd_3841763 := by exact prefixLift 3841763
  have htrace : WordTrace (prefixWord ++ tailWord_3841763) baseStart_3841763 baseEnd_3841763 := by
    simpa [prefixWord, tailWord_3841763, baseEnd_3841763] using wordTrace_append hprefix tailTrace_3841763
  have hstable : (prefixWord ++ tailWord_3841763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841763).length < 2 ^ (prefixWord ++ tailWord_3841763).sum := by decide
  have hdescent : baseEnd_3841763 < baseStart_3841763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841767 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 3, 3]
def baseStart_3841767 : Nat := 118140960795 + 3841767 * 2 ^ 59
def prefixEnd_3841767 : Nat := 4983230072969 + 3 ^ 40 * 3841767 * 2
def baseEnd_3841767 : Nat := 1315115355721050535096361

theorem tailTrace_3841767 : CollatzResearch.WordTrace tailWord_3841767 prefixEnd_3841767 1315115355721050535096361 := by
  unfold tailWord_3841767
  simp only [CollatzResearch.WordTrace]
  refine ⟨140120753872941755412203555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93413835915294503608135703 140120753872941755412203555)
  ·
    refine ⟨210181130809412633118305333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140120753872941755412203555 210181130809412633118305333)
    ·
      refine ⟨19704481013382434354841125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210181130809412633118305333 19704481013382434354841125)
      ·
        refine ⟨3694590190009206441532711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19704481013382434354841125 3694590190009206441532711)
        ·
          refine ⟨5541885285013809662299067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3694590190009206441532711 5541885285013809662299067)
          ·
            refine ⟨8312827927520714493448601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541885285013809662299067 8312827927520714493448601)
            ·
              refine ⟨6234620945640535870086451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8312827927520714493448601 6234620945640535870086451)
              ·
                refine ⟨9351931418460803805129677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234620945640535870086451 9351931418460803805129677)
                ·
                  refine ⟨3506974281922801426923629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9351931418460803805129677 3506974281922801426923629)
                  ·
                    refine ⟨1315115355721050535096361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3506974281922801426923629 1315115355721050535096361)
                    ·
                      rfl

theorem cell22_3841767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_3841767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841767 prefixEnd_3841767 := by exact prefixLift 3841767
  have htrace : WordTrace (prefixWord ++ tailWord_3841767) baseStart_3841767 baseEnd_3841767 := by
    simpa [prefixWord, tailWord_3841767, baseEnd_3841767] using wordTrace_append hprefix tailTrace_3841767
  have hstable : (prefixWord ++ tailWord_3841767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841767).length < 2 ^ (prefixWord ++ tailWord_3841767).sum := by decide
  have hdescent : baseEnd_3841767 < baseStart_3841767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841776 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_3841776 : Nat := 118140960795 + 3841776 * 2 ^ 59
def prefixEnd_3841776 : Nat := 4983230072969 + 3 ^ 40 * 3841776 * 2
def baseEnd_3841776 : Nat := 1315118436604977511621333

theorem tailTrace_3841776 : CollatzResearch.WordTrace tailWord_3841776 prefixEnd_3841776 1315118436604977511621333 := by
  unfold tailWord_3841776
  simp only [CollatzResearch.WordTrace]
  refine ⟨70060541064954574974640591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93414054753272766632854121 70060541064954574974640591)
  ·
    refine ⟨105090811597431862461960887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70060541064954574974640591 105090811597431862461960887)
    ·
      refine ⟨157636217396147793692941331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105090811597431862461960887 157636217396147793692941331)
      ·
        refine ⟨236454326094221690539411997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157636217396147793692941331 236454326094221690539411997)
        ·
          refine ⟨88670372285333133952279499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236454326094221690539411997 88670372285333133952279499)
          ·
            refine ⟨133005558427999700928419249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88670372285333133952279499 133005558427999700928419249)
            ·
              refine ⟨99754168820999775696314437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133005558427999700928419249 99754168820999775696314437)
              ·
                refine ⟨18703906653937457943058957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99754168820999775696314437 18703906653937457943058957)
                ·
                  refine ⟨7013964995226546728647109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18703906653937457943058957 7013964995226546728647109)
                  ·
                    refine ⟨1315118436604977511621333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7013964995226546728647109 1315118436604977511621333)
                    ·
                      rfl

theorem cell22_3841776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_3841776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841776 prefixEnd_3841776 := by exact prefixLift 3841776
  have htrace : WordTrace (prefixWord ++ tailWord_3841776) baseStart_3841776 baseEnd_3841776 := by
    simpa [prefixWord, tailWord_3841776, baseEnd_3841776] using wordTrace_append hprefix tailTrace_3841776
  have hstable : (prefixWord ++ tailWord_3841776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841776).length < 2 ^ (prefixWord ++ tailWord_3841776).sum := by decide
  have hdescent : baseEnd_3841776 < baseStart_3841776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841791 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 6]
def baseStart_3841791 : Nat := 118140960795 + 3841791 * 2 ^ 59
def prefixEnd_3841791 : Nat := 4983230072969 + 3 ^ 40 * 3841791 * 2
def baseEnd_3841791 : Nat := 438374523803840824165429

theorem tailTrace_3841791 : CollatzResearch.WordTrace tailWord_3841791 prefixEnd_3841791 438374523803840824165429 := by
  unfold tailWord_3841791
  simp only [CollatzResearch.WordTrace]
  refine ⟨140121629224854807511077227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93414419483236538340718151 140121629224854807511077227)
  ·
    refine ⟨210182443837282211266615841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140121629224854807511077227 210182443837282211266615841)
    ·
      refine ⟨157636832877961658449961881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210182443837282211266615841 157636832877961658449961881)
      ·
        refine ⟨118227624658471243837471411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157636832877961658449961881 118227624658471243837471411)
        ·
          refine ⟨177341436987706865756207117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118227624658471243837471411 177341436987706865756207117)
          ·
            refine ⟨66503038870390074658577669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177341436987706865756207117 66503038870390074658577669)
            ·
              refine ⟨12469319788198138998483313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66503038870390074658577669 12469319788198138998483313)
              ·
                refine ⟨9351989841148604248862485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12469319788198138998483313 9351989841148604248862485)
                ·
                  refine ⟨438374523803840824165429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9351989841148604248862485 438374523803840824165429)
                  ·
                    rfl

theorem cell22_3841791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 6].length) (baseStart_3841791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841791 prefixEnd_3841791 := by exact prefixLift 3841791
  have htrace : WordTrace (prefixWord ++ tailWord_3841791) baseStart_3841791 baseEnd_3841791 := by
    simpa [prefixWord, tailWord_3841791, baseEnd_3841791] using wordTrace_append hprefix tailTrace_3841791
  have hstable : (prefixWord ++ tailWord_3841791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841791).length < 2 ^ (prefixWord ++ tailWord_3841791).sum := by decide
  have hdescent : baseEnd_3841791 < baseStart_3841791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841793 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 1, 4]
def baseStart_3841793 : Nat := 118140960795 + 3841793 * 2 ^ 59
def prefixEnd_3841793 : Nat := 4983230072969 + 3 ^ 40 * 3841793 * 2
def baseEnd_3841793 : Nat := 1315124256052395133946281

theorem tailTrace_3841793 : CollatzResearch.WordTrace tailWord_3841793 prefixEnd_3841793 1315124256052395133946281 := by
  unfold tailWord_3841793
  simp only [CollatzResearch.WordTrace]
  refine ⟨140121702170847561852650033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93414468113898374568433355 140121702170847561852650033)
  ·
    refine ⟨105091276628135671389487525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140121702170847561852650033 105091276628135671389487525)
    ·
      refine ⟨19704614367775438385528911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105091276628135671389487525 19704614367775438385528911)
      ·
        refine ⟨29556921551663157578293367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19704614367775438385528911 29556921551663157578293367)
        ·
          refine ⟨44335382327494736367440051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29556921551663157578293367 44335382327494736367440051)
          ·
            refine ⟨66503073491242104551160077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44335382327494736367440051 66503073491242104551160077)
            ·
              refine ⟨24938652559215789206685029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66503073491242104551160077 24938652559215789206685029)
              ·
                refine ⟨4675997354852960476253443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24938652559215789206685029 4675997354852960476253443)
                ·
                  refine ⟨7013996032279440714380165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675997354852960476253443 7013996032279440714380165)
                  ·
                    refine ⟨1315124256052395133946281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7013996032279440714380165 1315124256052395133946281)
                    ·
                      rfl

theorem cell22_3841793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_3841793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841793 prefixEnd_3841793 := by exact prefixLift 3841793
  have htrace : WordTrace (prefixWord ++ tailWord_3841793) baseStart_3841793 baseEnd_3841793 := by
    simpa [prefixWord, tailWord_3841793, baseEnd_3841793] using wordTrace_append hprefix tailTrace_3841793
  have hstable : (prefixWord ++ tailWord_3841793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841793).length < 2 ^ (prefixWord ++ tailWord_3841793).sum := by decide
  have hdescent : baseEnd_3841793 < baseStart_3841793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841823 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 4, 3]
def baseStart_3841823 : Nat := 118140960795 + 3841823 * 2 ^ 59
def prefixEnd_3841823 : Nat := 4983230072969 + 3 ^ 40 * 3841823 * 2
def baseEnd_3841823 : Nat := 1315134525665485055696189

theorem tailTrace_3841823 : CollatzResearch.WordTrace tailWord_3841823 prefixEnd_3841823 1315134525665485055696189 := by
  unfold tailWord_3841823
  simp only [CollatzResearch.WordTrace]
  refine ⟨140122796360738876976242123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93415197573825917984161415 140122796360738876976242123)
  ·
    refine ⟨210184194541108315464363185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140122796360738876976242123 210184194541108315464363185)
    ·
      refine ⟨157638145905831236598272389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210184194541108315464363185 157638145905831236598272389)
      ·
        refine ⟨29557152357343356862176073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157638145905831236598272389 29557152357343356862176073)
        ·
          refine ⟨22167864268007517646632055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29557152357343356862176073 22167864268007517646632055)
          ·
            refine ⟨33251796402011276469948083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22167864268007517646632055 33251796402011276469948083)
            ·
              refine ⟨49877694603016914704922125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33251796402011276469948083 49877694603016914704922125)
              ·
                refine ⟨18704135476131343014345797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49877694603016914704922125 18704135476131343014345797)
                ·
                  refine ⟨3507025401774626815189837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18704135476131343014345797 3507025401774626815189837)
                  ·
                    refine ⟨1315134525665485055696189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3507025401774626815189837 1315134525665485055696189)
                    ·
                      rfl

theorem cell22_3841823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 3].length) (baseStart_3841823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841823 prefixEnd_3841823 := by exact prefixLift 3841823
  have htrace : WordTrace (prefixWord ++ tailWord_3841823) baseStart_3841823 baseEnd_3841823 := by
    simpa [prefixWord, tailWord_3841823, baseEnd_3841823] using wordTrace_append hprefix tailTrace_3841823
  have hstable : (prefixWord ++ tailWord_3841823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841823).length < 2 ^ (prefixWord ++ tailWord_3841823).sum := by decide
  have hdescent : baseEnd_3841823 < baseStart_3841823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841836 : List Nat := [2, 2, 1, 1, 1, 5, 1, 9]
def baseStart_3841836 : Nat := 118140960795 + 3841836 * 2 ^ 59
def prefixEnd_3841836 : Nat := 4983230072969 + 3 ^ 40 * 3841836 * 2
def baseEnd_3841836 : Nat := 146126552870128595013461

theorem tailTrace_3841836 : CollatzResearch.WordTrace tailWord_3841836 prefixEnd_3841836 146126552870128595013461 := by
  unfold tailWord_3841836
  simp only [CollatzResearch.WordTrace]
  refine ⟨70061635254845890098232681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93415513673127853464310241 70061635254845890098232681)
  ·
    refine ⟨52546226441134417573674511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70061635254845890098232681 52546226441134417573674511)
    ·
      refine ⟨78819339661701626360511767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52546226441134417573674511 78819339661701626360511767)
      ·
        refine ⟨118229009492552439540767651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78819339661701626360511767 118229009492552439540767651)
        ·
          refine ⟨177343514238828659311151477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118229009492552439540767651 177343514238828659311151477)
          ·
            refine ⟨16625954459890186810420451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177343514238828659311151477 16625954459890186810420451)
            ·
              refine ⟨24938931689835280215630677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16625954459890186810420451 24938931689835280215630677)
              ·
                refine ⟨146126552870128595013461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24938931689835280215630677 146126552870128595013461)
                ·
                  rfl

theorem cell22_3841836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 9].length) (baseStart_3841836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841836 prefixEnd_3841836 := by exact prefixLift 3841836
  have htrace : WordTrace (prefixWord ++ tailWord_3841836) baseStart_3841836 baseEnd_3841836 := by
    simpa [prefixWord, tailWord_3841836, baseEnd_3841836] using wordTrace_append hprefix tailTrace_3841836
  have hstable : (prefixWord ++ tailWord_3841836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841836).length < 2 ^ (prefixWord ++ tailWord_3841836).sum := by decide
  have hdescent : baseEnd_3841836 < baseStart_3841836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841853 : List Nat := [1, 4, 1, 4, 1, 1, 2, 8]
def baseStart_3841853 : Nat := 118140960795 + 3841853 * 2 ^ 59
def prefixEnd_3841853 : Nat := 4983230072969 + 3 ^ 40 * 3841853 * 2
def baseEnd_3841853 : Nat := 146127199475397219716233

theorem tailTrace_3841853 : CollatzResearch.WordTrace tailWord_3841853 prefixEnd_3841853 146127199475397219716233 := by
  unfold tailWord_3841853
  simp only [CollatzResearch.WordTrace]
  refine ⟨140123890550630192099834213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93415927033753461399889475 140123890550630192099834213)
  ·
    refine ⟨26273229478243161018718915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140123890550630192099834213 26273229478243161018718915)
    ·
      refine ⟨39409844217364741528078373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26273229478243161018718915 39409844217364741528078373)
      ·
        refine ⟨7389345790755889036514695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39409844217364741528078373 7389345790755889036514695)
        ·
          refine ⟨11084018686133833554772043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7389345790755889036514695 11084018686133833554772043)
          ·
            refine ⟨16626028029200750332158065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11084018686133833554772043 16626028029200750332158065)
            ·
              refine ⟨12469521021900562749118549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16626028029200750332158065 12469521021900562749118549)
              ·
                refine ⟨146127199475397219716233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12469521021900562749118549 146127199475397219716233)
                ·
                  rfl

theorem cell22_3841853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 8].length) (baseStart_3841853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841853 prefixEnd_3841853 := by exact prefixLift 3841853
  have htrace : WordTrace (prefixWord ++ tailWord_3841853) baseStart_3841853 baseEnd_3841853 := by
    simpa [prefixWord, tailWord_3841853, baseEnd_3841853] using wordTrace_append hprefix tailTrace_3841853
  have hstable : (prefixWord ++ tailWord_3841853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841853).length < 2 ^ (prefixWord ++ tailWord_3841853).sum := by decide
  have hdescent : baseEnd_3841853 < baseStart_3841853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841855 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 2, 4]
def baseStart_3841855 : Nat := 118140960795 + 3841855 * 2 ^ 59
def prefixEnd_3841855 : Nat := 4983230072969 + 3 ^ 40 * 3841855 * 2
def baseEnd_3841855 : Nat := 1315145479919447638896091

theorem tailTrace_3841855 : CollatzResearch.WordTrace tailWord_3841855 prefixEnd_3841855 1315145479919447638896091 := by
  unfold tailWord_3841855
  simp only [CollatzResearch.WordTrace]
  refine ⟨140123963496622946441407019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93415975664415297627604679 140123963496622946441407019)
  ·
    refine ⟨210185945244934419662110529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140123963496622946441407019 210185945244934419662110529)
    ·
      refine ⟨157639458933700814746582897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210185945244934419662110529 157639458933700814746582897)
      ·
        refine ⟨118229594200275611059937173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157639458933700814746582897 118229594200275611059937173)
        ·
          refine ⟨5542012228137919268434555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118229594200275611059937173 5542012228137919268434555)
          ·
            refine ⟨8313018342206878902651833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542012228137919268434555 8313018342206878902651833)
            ·
              refine ⟨6234763756655159176988875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8313018342206878902651833 6234763756655159176988875)
              ·
                refine ⟨9352145634982738765483313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234763756655159176988875 9352145634982738765483313)
                ·
                  refine ⟨7014109226237054074112485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9352145634982738765483313 7014109226237054074112485)
                  ·
                    refine ⟨1315145479919447638896091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7014109226237054074112485 1315145479919447638896091)
                    ·
                      rfl

theorem cell22_3841855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_3841855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841855 prefixEnd_3841855 := by exact prefixLift 3841855
  have htrace : WordTrace (prefixWord ++ tailWord_3841855) baseStart_3841855 baseEnd_3841855 := by
    simpa [prefixWord, tailWord_3841855, baseEnd_3841855] using wordTrace_append hprefix tailTrace_3841855
  have hstable : (prefixWord ++ tailWord_3841855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841855).length < 2 ^ (prefixWord ++ tailWord_3841855).sum := by decide
  have hdescent : baseEnd_3841855 < baseStart_3841855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841902 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_3841902 : Nat := 118140960795 + 3841902 * 2 ^ 59
def prefixEnd_3841902 : Nat := 4983230072969 + 3 ^ 40 * 3841902 * 2
def baseEnd_3841902 : Nat := 1315161568979955182970947

theorem tailTrace_3841902 : CollatzResearch.WordTrace tailWord_3841902 prefixEnd_3841902 1315161568979955182970947 := by
  unfold tailWord_3841902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17515709715931584183545995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93417118484968448978911973 17515709715931584183545995)
  ·
    refine ⟨26273564573897376275318993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17515709715931584183545995 26273564573897376275318993)
    ·
      refine ⟨19705173430423032206489245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26273564573897376275318993 19705173430423032206489245)
      ·
        refine ⟨7389440036408637077433467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19705173430423032206489245 7389440036408637077433467)
        ·
          refine ⟨11084160054612955616150201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7389440036408637077433467 11084160054612955616150201)
          ·
            refine ⟨8313120040959716712112651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11084160054612955616150201 8313120040959716712112651)
            ·
              refine ⟨12469680061439575068168977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8313120040959716712112651 12469680061439575068168977)
              ·
                refine ⟨9352260046079681301126733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12469680061439575068168977 9352260046079681301126733)
                ·
                  refine ⟨3507097517279880487922525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9352260046079681301126733 3507097517279880487922525)
                  ·
                    refine ⟨1315161568979955182970947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3507097517279880487922525 1315161568979955182970947)
                    ·
                      rfl

theorem cell22_3841902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_3841902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841902 prefixEnd_3841902 := by exact prefixLift 3841902
  have htrace : WordTrace (prefixWord ++ tailWord_3841902) baseStart_3841902 baseEnd_3841902 := by
    simpa [prefixWord, tailWord_3841902, baseEnd_3841902] using wordTrace_append hprefix tailTrace_3841902
  have hstable : (prefixWord ++ tailWord_3841902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841902).length < 2 ^ (prefixWord ++ tailWord_3841902).sum := by decide
  have hdescent : baseEnd_3841902 < baseStart_3841902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841943 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 6]
def baseStart_3841943 : Nat := 118140960795 + 3841943 * 2 ^ 59
def prefixEnd_3841943 : Nat := 4983230072969 + 3 ^ 40 * 3841943 * 2
def baseEnd_3841943 : Nat := 438391868039281580898607

theorem tailTrace_3841943 : CollatzResearch.WordTrace tailWord_3841943 prefixEnd_3841943 438391868039281580898607 := by
  unfold tailWord_3841943
  simp only [CollatzResearch.WordTrace]
  refine ⟨140127173120304137470610483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93418115413536091647073655 140127173120304137470610483)
  ·
    refine ⟨210190759680456206205915725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140127173120304137470610483 210190759680456206205915725)
    ·
      refine ⟨78821534880171077327218397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210190759680456206205915725 78821534880171077327218397)
      ·
        refine ⟨29558075580064153997706899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78821534880171077327218397 29558075580064153997706899)
        ·
          refine ⟨44337113370096230996560349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29558075580064153997706899 44337113370096230996560349)
          ·
            refine ⟨16626417513786086623710131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44337113370096230996560349 16626417513786086623710131)
            ·
              refine ⟨24939626270679129935565197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16626417513786086623710131 24939626270679129935565197)
              ·
                refine ⟨9352359851504673725836949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24939626270679129935565197 9352359851504673725836949)
                ·
                  refine ⟨438391868039281580898607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9352359851504673725836949 438391868039281580898607)
                  ·
                    rfl

theorem cell22_3841943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 6].length) (baseStart_3841943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3841943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3841943 prefixEnd_3841943 := by exact prefixLift 3841943
  have htrace : WordTrace (prefixWord ++ tailWord_3841943) baseStart_3841943 baseEnd_3841943 := by
    simpa [prefixWord, tailWord_3841943, baseEnd_3841943] using wordTrace_append hprefix tailTrace_3841943
  have hstable : (prefixWord ++ tailWord_3841943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841943).length < 2 ^ (prefixWord ++ tailWord_3841943).sum := by decide
  have hdescent : baseEnd_3841943 < baseStart_3841943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842005 : List Nat := [1, 3, 2, 3, 2, 2, 2, 7]
def baseStart_3842005 : Nat := 118140960795 + 3842005 * 2 ^ 59
def prefixEnd_3842005 : Nat := 4983230072969 + 3 ^ 40 * 3842005 * 2
def baseEnd_3842005 : Nat := 146132980887210805293959

theorem tailTrace_3842005 : CollatzResearch.WordTrace tailWord_3842005 prefixEnd_3842005 146132980887210805293959 := by
  unfold tailWord_3842005
  simp only [CollatzResearch.WordTrace]
  refine ⟨140129434446079522059367469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93419622964053014706244979 140129434446079522059367469)
  ·
    refine ⟨52548537917279820772262801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140129434446079522059367469 52548537917279820772262801)
    ·
      refine ⟨39411403437959865579197101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52548537917279820772262801 39411403437959865579197101)
      ·
        refine ⟨14779276289234949592198913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39411403437959865579197101 14779276289234949592198913)
        ·
          refine ⟨11084457216926212194149185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14779276289234949592198913 11084457216926212194149185)
          ·
            refine ⟨8313342912694659145611889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11084457216926212194149185 8313342912694659145611889)
            ·
              refine ⟨6235007184520994359208917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8313342912694659145611889 6235007184520994359208917)
              ·
                refine ⟨146132980887210805293959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6235007184520994359208917 146132980887210805293959)
                ·
                  rfl

theorem cell22_3842005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 7].length) (baseStart_3842005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842005 prefixEnd_3842005 := by exact prefixLift 3842005
  have htrace : WordTrace (prefixWord ++ tailWord_3842005) baseStart_3842005 baseEnd_3842005 := by
    simpa [prefixWord, tailWord_3842005, baseEnd_3842005] using wordTrace_append hprefix tailTrace_3842005
  have hstable : (prefixWord ++ tailWord_3842005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842005).length < 2 ^ (prefixWord ++ tailWord_3842005).sum := by decide
  have hdescent : baseEnd_3842005 < baseStart_3842005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842020 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_3842020 : Nat := 118140960795 + 3842020 * 2 ^ 59
def prefixEnd_3842020 : Nat := 4983230072969 + 3 ^ 40 * 3842020 * 2
def baseEnd_3842020 : Nat := 1315201962791442208520585

theorem tailTrace_3842020 : CollatzResearch.WordTrace tailWord_3842020 prefixEnd_3842020 1315201962791442208520585 := by
  unfold tailWord_3842020
  simp only [CollatzResearch.WordTrace]
  refine ⟨70064990770512589810581757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93419987694016786414109009 70064990770512589810581757)
  ·
    refine ⟨26274371538942221178968159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70064990770512589810581757 26274371538942221178968159)
    ·
      refine ⟨39411557308413331768452239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26274371538942221178968159 39411557308413331768452239)
      ·
        refine ⟨59117335962619997652678359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39411557308413331768452239 59117335962619997652678359)
        ·
          refine ⟨88676003943929996479017539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59117335962619997652678359 88676003943929996479017539)
          ·
            refine ⟨133014005915894994718526309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88676003943929996479017539 133014005915894994718526309)
            ·
              refine ⟨24940126109230311509723683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133014005915894994718526309 24940126109230311509723683)
              ·
                refine ⟨37410189163845467264585525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24940126109230311509723683 37410189163845467264585525)
                ·
                  refine ⟨3507205234110512556054893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37410189163845467264585525 3507205234110512556054893)
                  ·
                    refine ⟨1315201962791442208520585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3507205234110512556054893 1315201962791442208520585)
                    ·
                      rfl

theorem cell22_3842020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_3842020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842020 prefixEnd_3842020 := by exact prefixLift 3842020
  have htrace : WordTrace (prefixWord ++ tailWord_3842020) baseStart_3842020 baseEnd_3842020 := by
    simpa [prefixWord, tailWord_3842020, baseEnd_3842020] using wordTrace_append hprefix tailTrace_3842020
  have hstable : (prefixWord ++ tailWord_3842020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842020).length < 2 ^ (prefixWord ++ tailWord_3842020).sum := by decide
  have hdescent : baseEnd_3842020 < baseStart_3842020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842088 : List Nat := [2, 1, 5, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3842088 : Nat := 118140960795 + 3842088 * 2 ^ 59
def prefixEnd_3842088 : Nat := 4983230072969 + 3 ^ 40 * 3842088 * 2
def baseEnd_3842088 : Nat := 1315225240581112697820377

theorem tailTrace_3842088 : CollatzResearch.WordTrace tailWord_3842088 prefixEnd_3842088 1315225240581112697820377 := by
  unfold tailWord_3842088
  simp only [CollatzResearch.WordTrace]
  refine ⟨70066230852389413617319459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93421641136519218156425945 70066230852389413617319459)
  ·
    refine ⟨105099346278584120425979189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70066230852389413617319459 105099346278584120425979189)
    ·
      refine ⟨9853063713617261289935549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105099346278584120425979189 9853063713617261289935549)
      ·
        refine ⟨3694898892606472983725831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9853063713617261289935549 3694898892606472983725831)
        ·
          refine ⟨5542348338909709475588747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3694898892606472983725831 5542348338909709475588747)
          ·
            refine ⟨8313522508364564213383121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542348338909709475588747 8313522508364564213383121)
            ·
              refine ⟨6235141881273423160037341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8313522508364564213383121 6235141881273423160037341)
              ·
                refine ⟨2338178205477533685014003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6235141881273423160037341 2338178205477533685014003)
                ·
                  refine ⟨3507267308216300527521005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338178205477533685014003 3507267308216300527521005)
                  ·
                    refine ⟨1315225240581112697820377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3507267308216300527521005 1315225240581112697820377)
                    ·
                      rfl

theorem cell22_3842088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3842088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842088 prefixEnd_3842088 := by exact prefixLift 3842088
  have htrace : WordTrace (prefixWord ++ tailWord_3842088) baseStart_3842088 baseEnd_3842088 := by
    simpa [prefixWord, tailWord_3842088, baseEnd_3842088] using wordTrace_append hprefix tailTrace_3842088
  have hstable : (prefixWord ++ tailWord_3842088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842088).length < 2 ^ (prefixWord ++ tailWord_3842088).sum := by decide
  have hdescent : baseEnd_3842088 < baseStart_3842088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842097 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 1, 4]
def baseStart_3842097 : Nat := 118140960795 + 3842097 * 2 ^ 59
def prefixEnd_3842097 : Nat := 4983230072969 + 3 ^ 40 * 3842097 * 2
def baseEnd_3842097 : Nat := 1315228321465039674345349

theorem tailTrace_3842097 : CollatzResearch.WordTrace tailWord_3842097 prefixEnd_3842097 1315228321465039674345349 := by
  unfold tailWord_3842097
  simp only [CollatzResearch.WordTrace]
  refine ⟨140132789961746221771716545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93421859974497481181144363 140132789961746221771716545)
  ·
    refine ⟨105099592471309666328787409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140132789961746221771716545 105099592471309666328787409)
    ·
      refine ⟨78824694353482249746590557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105099592471309666328787409 78824694353482249746590557)
      ·
        refine ⟨29559260382555843654971459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78824694353482249746590557 29559260382555843654971459)
        ·
          refine ⟨44338890573833765482457189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29559260382555843654971459 44338890573833765482457189)
          ·
            refine ⟨8313541982593831027960723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44338890573833765482457189 8313541982593831027960723)
            ·
              refine ⟨12470312973890746541941085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8313541982593831027960723 12470312973890746541941085)
              ·
                refine ⟨4676367365209029953227907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12470312973890746541941085 4676367365209029953227907)
                ·
                  refine ⟨7014551047813544929841861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676367365209029953227907 7014551047813544929841861)
                  ·
                    refine ⟨1315228321465039674345349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7014551047813544929841861 1315228321465039674345349)
                    ·
                      rfl

theorem cell22_3842097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_3842097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842097 prefixEnd_3842097 := by exact prefixLift 3842097
  have htrace : WordTrace (prefixWord ++ tailWord_3842097) baseStart_3842097 baseEnd_3842097 := by
    simpa [prefixWord, tailWord_3842097, baseEnd_3842097] using wordTrace_append hprefix tailTrace_3842097
  have hstable : (prefixWord ++ tailWord_3842097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842097).length < 2 ^ (prefixWord ++ tailWord_3842097).sum := by decide
  have hdescent : baseEnd_3842097 < baseStart_3842097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842112 : List Nat := [2, 1, 1, 2, 2, 4, 2, 4, 4]
def baseStart_3842112 : Nat := 118140960795 + 3842112 * 2 ^ 59
def prefixEnd_3842112 : Nat := 4983230072969 + 3 ^ 40 * 3842112 * 2
def baseEnd_3842112 : Nat := 438411152090528211740101

theorem tailTrace_3842112 : CollatzResearch.WordTrace tailWord_3842112 prefixEnd_3842112 438411152090528211740101 := by
  unfold tailWord_3842112
  simp only [CollatzResearch.WordTrace]
  refine ⟨70066668528345939666756295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93422224704461252889008393 70066668528345939666756295)
  ·
    refine ⟨105100002792518909500134443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70066668528345939666756295 105100002792518909500134443)
    ·
      refine ⟨157650004188778364250201665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105100002792518909500134443 157650004188778364250201665)
      ·
        refine ⟨118237503141583773187651249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157650004188778364250201665 118237503141583773187651249)
        ·
          refine ⟨88678127356187829890738437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118237503141583773187651249 88678127356187829890738437)
          ·
            refine ⟨16627148879285218104513457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88678127356187829890738437 16627148879285218104513457)
            ·
              refine ⟨12470361659463913578385093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16627148879285218104513457 12470361659463913578385093)
              ·
                refine ⟨2338192811149483795947205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12470361659463913578385093 2338192811149483795947205)
                ·
                  refine ⟨438411152090528211740101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338192811149483795947205 438411152090528211740101)
                  ·
                    rfl

theorem cell22_3842112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 4].length) (baseStart_3842112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842112 prefixEnd_3842112 := by exact prefixLift 3842112
  have htrace : WordTrace (prefixWord ++ tailWord_3842112) baseStart_3842112 baseEnd_3842112 := by
    simpa [prefixWord, tailWord_3842112, baseEnd_3842112] using wordTrace_append hprefix tailTrace_3842112
  have hstable : (prefixWord ++ tailWord_3842112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842112).length < 2 ^ (prefixWord ++ tailWord_3842112).sum := by decide
  have hdescent : baseEnd_3842112 < baseStart_3842112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842264 : List Nat := [2, 1, 2, 2, 4, 1, 1, 5, 4]
def baseStart_3842264 : Nat := 118140960795 + 3842264 * 2 ^ 59
def prefixEnd_3842264 : Nat := 4983230072969 + 3 ^ 40 * 3842264 * 2
def baseEnd_3842264 : Nat := 438428496325968968473279

theorem tailTrace_3842264 : CollatzResearch.WordTrace tailWord_3842264 prefixEnd_3842264 438428496325968968473279 := by
  unfold tailWord_3842264
  simp only [CollatzResearch.WordTrace]
  refine ⟨70069440476070604646522923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93425920634760806195363897 70069440476070604646522923)
  ·
    refine ⟨105104160714105906969784385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70069440476070604646522923 105104160714105906969784385)
    ·
      refine ⟨78828120535579430227338289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105104160714105906969784385 78828120535579430227338289)
      ·
        refine ⟨59121090401684572670503717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78828120535579430227338289 59121090401684572670503717)
        ·
          refine ⟨11085204450315857375719447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59121090401684572670503717 11085204450315857375719447)
          ·
            refine ⟨16627806675473786063579171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11085204450315857375719447 16627806675473786063579171)
            ·
              refine ⟨24941710013210679095368757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16627806675473786063579171 24941710013210679095368757)
              ·
                refine ⟨2338285313738501165190821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24941710013210679095368757 2338285313738501165190821)
                ·
                  refine ⟨438428496325968968473279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338285313738501165190821 438428496325968968473279)
                  ·
                    rfl

theorem cell22_3842264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 4].length) (baseStart_3842264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842264 prefixEnd_3842264 := by exact prefixLift 3842264
  have htrace : WordTrace (prefixWord ++ tailWord_3842264) baseStart_3842264 baseEnd_3842264 := by
    simpa [prefixWord, tailWord_3842264, baseEnd_3842264] using wordTrace_append hprefix tailTrace_3842264
  have hstable : (prefixWord ++ tailWord_3842264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842264).length < 2 ^ (prefixWord ++ tailWord_3842264).sum := by decide
  have hdescent : baseEnd_3842264 < baseStart_3842264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842337 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 7]
def baseStart_3842337 : Nat := 118140960795 + 3842337 * 2 ^ 59
def prefixEnd_3842337 : Nat := 4983230072969 + 3 ^ 40 * 3842337 * 2
def baseEnd_3842337 : Nat := 438436826123253016114871

theorem tailTrace_3842337 : CollatzResearch.WordTrace tailWord_3842337 prefixEnd_3842337 438436826123253016114871 := by
  unfold tailWord_3842337
  simp only [CollatzResearch.WordTrace]
  refine ⟨140141543480876742760453265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93427695653917828506968843 140141543480876742760453265)
  ·
    refine ⟨105106157610657557070339949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140141543480876742760453265 105106157610657557070339949)
    ·
      refine ⟨39414809103996583901377481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105106157610657557070339949 39414809103996583901377481)
      ·
        refine ⟨29561106827997437926033111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39414809103996583901377481 29561106827997437926033111)
        ·
          refine ⟨44341660241996156889049667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29561106827997437926033111 44341660241996156889049667)
          ·
            refine ⟨66512490362994235333574501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44341660241996156889049667 66512490362994235333574501)
            ·
              refine ⟨12471091943061419125045219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66512490362994235333574501 12471091943061419125045219)
              ·
                refine ⟨18706637914592128687567829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12471091943061419125045219 18706637914592128687567829)
                ·
                  refine ⟨438436826123253016114871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18706637914592128687567829 438436826123253016114871)
                  ·
                    rfl

theorem cell22_3842337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_3842337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842337 prefixEnd_3842337 := by exact prefixLift 3842337
  have htrace : WordTrace (prefixWord ++ tailWord_3842337) baseStart_3842337 baseEnd_3842337 := by
    simpa [prefixWord, tailWord_3842337, baseEnd_3842337] using wordTrace_append hprefix tailTrace_3842337
  have hstable : (prefixWord ++ tailWord_3842337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842337).length < 2 ^ (prefixWord ++ tailWord_3842337).sum := by decide
  have hdescent : baseEnd_3842337 < baseStart_3842337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842343 : List Nat := [1, 1, 8, 1, 1, 1, 2, 7]
def baseStart_3842343 : Nat := 118140960795 + 3842343 * 2 ^ 59
def prefixEnd_3842343 : Nat := 4983230072969 + 3 ^ 40 * 3842343 * 2
def baseEnd_3842343 : Nat := 146145836921375225854955

theorem tailTrace_3842343 : CollatzResearch.WordTrace tailWord_3842343 prefixEnd_3842343 146145836921375225854955 := by
  unfold tailWord_3842343
  simp only [CollatzResearch.WordTrace]
  refine ⟨140141762318855005785171683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93427841545903337190114455 140141762318855005785171683)
  ·
    refine ⟨210212643478282508677757525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140141762318855005785171683 210212643478282508677757525)
    ·
      refine ⟨2463429415761123148567471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 210212643478282508677757525 2463429415761123148567471)
      ·
        refine ⟨3695144123641684722851207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463429415761123148567471 3695144123641684722851207)
        ·
          refine ⟨5542716185462527084276811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695144123641684722851207 5542716185462527084276811)
          ·
            refine ⟨8314074278193790626415217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542716185462527084276811 8314074278193790626415217)
            ·
              refine ⟨6235555708645342969811413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8314074278193790626415217 6235555708645342969811413)
              ·
                refine ⟨146145836921375225854955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6235555708645342969811413 146145836921375225854955)
                ·
                  rfl

theorem cell22_3842343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 7].length) (baseStart_3842343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842343 prefixEnd_3842343 := by exact prefixLift 3842343
  have htrace : WordTrace (prefixWord ++ tailWord_3842343) baseStart_3842343 baseEnd_3842343 := by
    simpa [prefixWord, tailWord_3842343, baseEnd_3842343] using wordTrace_append hprefix tailTrace_3842343
  have hstable : (prefixWord ++ tailWord_3842343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842343).length < 2 ^ (prefixWord ++ tailWord_3842343).sum := by decide
  have hdescent : baseEnd_3842343 < baseStart_3842343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842382 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_3842382 : Nat := 118140960795 + 3842382 * 2 ^ 59
def prefixEnd_3842382 : Nat := 4983230072969 + 3 ^ 40 * 3842382 * 2
def baseEnd_3842382 : Nat := 438441960929797976989825

theorem tailTrace_3842382 : CollatzResearch.WordTrace tailWord_3842382 prefixEnd_3842382 438441960929797976989825 := by
  unfold tailWord_3842382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17517898095714214430730175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93428789843809143630560933 17517898095714214430730175)
  ·
    refine ⟨26276847143571321646095263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17517898095714214430730175 26276847143571321646095263)
    ·
      refine ⟨39415270715356982469142895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26276847143571321646095263 39415270715356982469142895)
      ·
        refine ⟨59122906073035473703714343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39415270715356982469142895 59122906073035473703714343)
        ·
          refine ⟨88684359109553210555571515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59122906073035473703714343 88684359109553210555571515)
          ·
            refine ⟨133026538664329815833357273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88684359109553210555571515 133026538664329815833357273)
            ·
              refine ⟨99769903998247361875017955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133026538664329815833357273 99769903998247361875017955)
              ·
                refine ⟨149654855997371042812526933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99769903998247361875017955 149654855997371042812526933)
                ·
                  refine ⟨438441960929797976989825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149654855997371042812526933 438441960929797976989825)
                  ·
                    rfl

theorem cell22_3842382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_3842382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842382 prefixEnd_3842382 := by exact prefixLift 3842382
  have htrace : WordTrace (prefixWord ++ tailWord_3842382) baseStart_3842382 baseEnd_3842382 := by
    simpa [prefixWord, tailWord_3842382, baseEnd_3842382] using wordTrace_append hprefix tailTrace_3842382
  have hstable : (prefixWord ++ tailWord_3842382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842382).length < 2 ^ (prefixWord ++ tailWord_3842382).sum := by decide
  have hdescent : baseEnd_3842382 < baseStart_3842382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842429 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3842429 : Nat := 118140960795 + 3842429 * 2 ^ 59
def prefixEnd_3842429 : Nat := 4983230072969 + 3 ^ 40 * 3842429 * 2
def baseEnd_3842429 : Nat := 1315341971849901475044331

theorem tailTrace_3842429 : CollatzResearch.WordTrace tailWord_3842429 prefixEnd_3842429 1315341971849901475044331 := by
  unfold tailWord_3842429
  simp only [CollatzResearch.WordTrace]
  refine ⟨140144898996543442472802341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93429932664362294981868227 140144898996543442472802341)
  ·
    refine ⟨26277168561851895463650439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140144898996543442472802341 26277168561851895463650439)
    ·
      refine ⟨39415752842777843195475659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26277168561851895463650439 39415752842777843195475659)
      ·
        refine ⟨59123629264166764793213489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39415752842777843195475659 59123629264166764793213489)
        ·
          refine ⟨44342721948125073594910117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59123629264166764793213489 44342721948125073594910117)
          ·
            refine ⟨8314260365273451299045647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44342721948125073594910117 8314260365273451299045647)
            ·
              refine ⟨12471390547910176948568471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8314260365273451299045647 12471390547910176948568471)
              ·
                refine ⟨18707085821865265422852707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12471390547910176948568471 18707085821865265422852707)
                ·
                  refine ⟨28060628732797898134279061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18707085821865265422852707 28060628732797898134279061)
                  ·
                    refine ⟨1315341971849901475044331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28060628732797898134279061 1315341971849901475044331)
                    ·
                      rfl

theorem cell22_3842429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3842429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842429 prefixEnd_3842429 := by exact prefixLift 3842429
  have htrace : WordTrace (prefixWord ++ tailWord_3842429) baseStart_3842429 baseEnd_3842429 := by
    simpa [prefixWord, tailWord_3842429, baseEnd_3842429] using wordTrace_append hprefix tailTrace_3842429
  have hstable : (prefixWord ++ tailWord_3842429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842429).length < 2 ^ (prefixWord ++ tailWord_3842429).sum := by decide
  have hdescent : baseEnd_3842429 < baseStart_3842429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842433 : List Nat := [1, 2, 4, 3, 1, 2, 2, 3, 4]
def baseStart_3842433 : Nat := 118140960795 + 3842433 * 2 ^ 59
def prefixEnd_3842433 : Nat := 4983230072969 + 3 ^ 40 * 3842433 * 2
def baseEnd_3842433 : Nat := 438447780377215599314773

theorem tailTrace_3842433 : CollatzResearch.WordTrace tailWord_3842433 prefixEnd_3842433 438447780377215599314773 := by
  unfold tailWord_3842433
  simp only [CollatzResearch.WordTrace]
  refine ⟨140145044888528951155947953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93430029925685967437298635 140145044888528951155947953)
  ·
    refine ⟨105108783666396713366960965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140145044888528951155947953 105108783666396713366960965)
    ·
      refine ⟨19707896937449383756305181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105108783666396713366960965 19707896937449383756305181)
      ·
        refine ⟨7390461351543518908614443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19707896937449383756305181 7390461351543518908614443)
        ·
          refine ⟨11085692027315278362921665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390461351543518908614443 11085692027315278362921665)
          ·
            refine ⟨8314269020486458772191249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11085692027315278362921665 8314269020486458772191249)
            ·
              refine ⟨6235701765364844079143437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8314269020486458772191249 6235701765364844079143437)
              ·
                refine ⟨2338388162011816529678789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6235701765364844079143437 2338388162011816529678789)
                ·
                  refine ⟨438447780377215599314773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338388162011816529678789 438447780377215599314773)
                  ·
                    rfl

theorem cell22_3842433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 4].length) (baseStart_3842433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842433 prefixEnd_3842433 := by exact prefixLift 3842433
  have htrace : WordTrace (prefixWord ++ tailWord_3842433) baseStart_3842433 baseEnd_3842433 := by
    simpa [prefixWord, tailWord_3842433, baseEnd_3842433] using wordTrace_append hprefix tailTrace_3842433
  have hstable : (prefixWord ++ tailWord_3842433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842433).length < 2 ^ (prefixWord ++ tailWord_3842433).sum := by decide
  have hdescent : baseEnd_3842433 < baseStart_3842433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842435 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 1, 4]
def baseStart_3842435 : Nat := 118140960795 + 3842435 * 2 ^ 59
def prefixEnd_3842435 : Nat := 4983230072969 + 3 ^ 40 * 3842435 * 2
def baseEnd_3842435 : Nat := 1315344025772519459394313

theorem tailTrace_3842435 : CollatzResearch.WordTrace tailWord_3842435 prefixEnd_3842435 1315344025772519459394313 := by
  unfold tailWord_3842435
  simp only [CollatzResearch.WordTrace]
  refine ⟨140145117834521705497520759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93430078556347803665013839 140145117834521705497520759)
  ·
    refine ⟨210217676751782558246281139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140145117834521705497520759 210217676751782558246281139)
    ·
      refine ⟨315326515127673837369421709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210217676751782558246281139 315326515127673837369421709)
      ·
        refine ⟨118247443172877689013533141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315326515127673837369421709 118247443172877689013533141)
        ·
          refine ⟨2771424449364320836254683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118247443172877689013533141 2771424449364320836254683)
          ·
            refine ⟨4157136674046481254382025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771424449364320836254683 4157136674046481254382025)
            ·
              refine ⟨3117852505534860940786519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157136674046481254382025 3117852505534860940786519)
              ·
                refine ⟨4676778758302291411179779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3117852505534860940786519 4676778758302291411179779)
                ·
                  refine ⟨7015168137453437116769669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676778758302291411179779 7015168137453437116769669)
                  ·
                    refine ⟨1315344025772519459394313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7015168137453437116769669 1315344025772519459394313)
                    ·
                      rfl

theorem cell22_3842435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 4].length) (baseStart_3842435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842435 prefixEnd_3842435 := by exact prefixLift 3842435
  have htrace : WordTrace (prefixWord ++ tailWord_3842435) baseStart_3842435 baseEnd_3842435 := by
    simpa [prefixWord, tailWord_3842435, baseEnd_3842435] using wordTrace_append hprefix tailTrace_3842435
  have hstable : (prefixWord ++ tailWord_3842435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842435).length < 2 ^ (prefixWord ++ tailWord_3842435).sum := by decide
  have hdescent : baseEnd_3842435 < baseStart_3842435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842465 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 1, 5]
def baseStart_3842465 : Nat := 118140960795 + 3842465 * 2 ^ 59
def prefixEnd_3842465 : Nat := 4983230072969 + 3 ^ 40 * 3842465 * 2
def baseEnd_3842465 : Nat := 1315354295385609381144221

theorem tailTrace_3842465 : CollatzResearch.WordTrace tailWord_3842465 prefixEnd_3842465 1315354295385609381144221 := by
  unfold tailWord_3842465
  simp only [CollatzResearch.WordTrace]
  refine ⟨140146212024413020621112849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93430808016275347080741899 140146212024413020621112849)
  ·
    refine ⟨105109659018309765465834637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140146212024413020621112849 105109659018309765465834637)
    ·
      refine ⟨39416122131866162049687989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105109659018309765465834637 39416122131866162049687989)
      ·
        refine ⟨3695261449862452692158249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39416122131866162049687989 3695261449862452692158249)
        ·
          refine ⟨2771446087396839519118687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3695261449862452692158249 2771446087396839519118687)
          ·
            refine ⟨4157169131095259278678031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771446087396839519118687 4157169131095259278678031)
            ·
              refine ⟨6235753696642888918017047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157169131095259278678031 6235753696642888918017047)
              ·
                refine ⟨9353630544964333377025571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6235753696642888918017047 9353630544964333377025571)
                ·
                  refine ⟨14030445817446500065538357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9353630544964333377025571 14030445817446500065538357)
                  ·
                    refine ⟨1315354295385609381144221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14030445817446500065538357 1315354295385609381144221)
                    ·
                      rfl

theorem cell22_3842465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_3842465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842465 prefixEnd_3842465 := by exact prefixLift 3842465
  have htrace : WordTrace (prefixWord ++ tailWord_3842465) baseStart_3842465 baseEnd_3842465 := by
    simpa [prefixWord, tailWord_3842465, baseEnd_3842465] using wordTrace_append hprefix tailTrace_3842465
  have hstable : (prefixWord ++ tailWord_3842465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842465).length < 2 ^ (prefixWord ++ tailWord_3842465).sum := by decide
  have hdescent : baseEnd_3842465 < baseStart_3842465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842484 : List Nat := [2, 5, 2, 2, 2, 1, 1, 3, 4]
def baseStart_3842484 : Nat := 118140960795 + 3842484 * 2 ^ 59
def prefixEnd_3842484 : Nat := 4983230072969 + 3 ^ 40 * 3842484 * 2
def baseEnd_3842484 : Nat := 438453599824633221639721

theorem tailTrace_3842484 : CollatzResearch.WordTrace tailWord_3842484 prefixEnd_3842484 438453599824633221639721 := by
  unfold tailWord_3842484
  simp only [CollatzResearch.WordTrace]
  refine ⟨70073452505672093433027253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93431270007562791244036337 70073452505672093433027253)
  ·
    refine ⟨6569386172406758759346305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70073452505672093433027253 6569386172406758759346305)
    ·
      refine ⟨4927039629305069069509729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6569386172406758759346305 4927039629305069069509729)
      ·
        refine ⟨3695279721978801802132297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4927039629305069069509729 3695279721978801802132297)
        ·
          refine ⟨2771459791484101351599223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3695279721978801802132297 2771459791484101351599223)
          ·
            refine ⟨4157189687226152027398835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771459791484101351599223 4157189687226152027398835)
            ·
              refine ⟨6235784530839228041098253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157189687226152027398835 6235784530839228041098253)
              ·
                refine ⟨2338419199064710515411845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6235784530839228041098253 2338419199064710515411845)
                ·
                  refine ⟨438453599824633221639721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338419199064710515411845 438453599824633221639721)
                  ·
                    rfl

theorem cell22_3842484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_3842484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842484 prefixEnd_3842484 := by exact prefixLift 3842484
  have htrace : WordTrace (prefixWord ++ tailWord_3842484) baseStart_3842484 baseEnd_3842484 := by
    simpa [prefixWord, tailWord_3842484, baseEnd_3842484] using wordTrace_append hprefix tailTrace_3842484
  have hstable : (prefixWord ++ tailWord_3842484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842484).length < 2 ^ (prefixWord ++ tailWord_3842484).sum := by decide
  have hdescent : baseEnd_3842484 < baseStart_3842484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842489 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 7]
def baseStart_3842489 : Nat := 118140960795 + 3842489 * 2 ^ 59
def prefixEnd_3842489 : Nat := 4983230072969 + 3 ^ 40 * 3842489 * 2
def baseEnd_3842489 : Nat := 438454170358693772848049

theorem tailTrace_3842489 : CollatzResearch.WordTrace tailWord_3842489 prefixEnd_3842489 438454170358693772848049 := by
  unfold tailWord_3842489
  simp only [CollatzResearch.WordTrace]
  refine ⟨140147087376326072719986521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93431391584217381813324347 140147087376326072719986521)
  ·
    refine ⟨105110315532244554539989891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140147087376326072719986521 105110315532244554539989891)
    ·
      refine ⟨157665473298366831809984837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105110315532244554539989891 157665473298366831809984837)
      ·
        refine ⟨29562276243443780964372157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157665473298366831809984837 29562276243443780964372157)
        ·
          refine ⟨11085853591291417861639559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29562276243443780964372157 11085853591291417861639559)
          ·
            refine ⟨16628780386937126792459339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11085853591291417861639559 16628780386937126792459339)
            ·
              refine ⟨24943170580405690188689009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16628780386937126792459339 24943170580405690188689009)
              ·
                refine ⟨18707377935304267641516757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24943170580405690188689009 18707377935304267641516757)
                ·
                  refine ⟨438454170358693772848049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18707377935304267641516757 438454170358693772848049)
                  ·
                    rfl

theorem cell22_3842489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_3842489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842489 prefixEnd_3842489 := by exact prefixLift 3842489
  have htrace : WordTrace (prefixWord ++ tailWord_3842489) baseStart_3842489 baseEnd_3842489 := by
    simpa [prefixWord, tailWord_3842489, baseEnd_3842489] using wordTrace_append hprefix tailTrace_3842489
  have hstable : (prefixWord ++ tailWord_3842489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842489).length < 2 ^ (prefixWord ++ tailWord_3842489).sum := by decide
  have hdescent : baseEnd_3842489 < baseStart_3842489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842536 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3842536 : Nat := 118140960795 + 3842536 * 2 ^ 59
def prefixEnd_3842536 : Nat := 4983230072969 + 3 ^ 40 * 3842536 * 2
def baseEnd_3842536 : Nat := 1315378600136588862619003

theorem tailTrace_3842536 : CollatzResearch.WordTrace tailWord_3842536 prefixEnd_3842536 1315378600136588862619003 := by
  unfold tailWord_3842536
  simp only [CollatzResearch.WordTrace]
  refine ⟨70074400803577899873473731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93432534404770533164631641 70074400803577899873473731)
  ·
    refine ⟨105111601205366849810210597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70074400803577899873473731 105111601205366849810210597)
    ·
      refine ⟨19708425226006284339414487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105111601205366849810210597 19708425226006284339414487)
      ·
        refine ⟨29562637839009426509121731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19708425226006284339414487 29562637839009426509121731)
        ·
          refine ⟨44343956758514139763682597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29562637839009426509121731 44343956758514139763682597)
          ·
            refine ⟨8314491892221401205690487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44343956758514139763682597 8314491892221401205690487)
            ·
              refine ⟨12471737838332101808535731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8314491892221401205690487 12471737838332101808535731)
              ·
                refine ⟨18707606757498152712803597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12471737838332101808535731 18707606757498152712803597)
                ·
                  refine ⟨7015352534061807267301349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18707606757498152712803597 7015352534061807267301349)
                  ·
                    refine ⟨1315378600136588862619003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7015352534061807267301349 1315378600136588862619003)
                    ·
                      rfl

theorem cell22_3842536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3842536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842536 prefixEnd_3842536 := by exact prefixLift 3842536
  have htrace : WordTrace (prefixWord ++ tailWord_3842536) baseStart_3842536 baseEnd_3842536 := by
    simpa [prefixWord, tailWord_3842536, baseEnd_3842536] using wordTrace_append hprefix tailTrace_3842536
  have hstable : (prefixWord ++ tailWord_3842536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842536).length < 2 ^ (prefixWord ++ tailWord_3842536).sum := by decide
  have hdescent : baseEnd_3842536 < baseStart_3842536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842611 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 5, 3]
def baseStart_3842611 : Nat := 118140960795 + 3842611 * 2 ^ 59
def prefixEnd_3842611 : Nat := 4983230072969 + 3 ^ 40 * 3842611 * 2
def baseEnd_3842611 : Nat := 1315404274169313666993773

theorem tailTrace_3842611 : CollatzResearch.WordTrace tailWord_3842611 prefixEnd_3842611 1315404274169313666993773 := by
  unfold tailWord_3842611
  simp only [CollatzResearch.WordTrace]
  refine ⟨140151537081884087555927687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93434358054589391703951791 140151537081884087555927687)
  ·
    refine ⟨210227305622826131333891531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140151537081884087555927687 210227305622826131333891531)
    ·
      refine ⟨315340958434239197000837297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210227305622826131333891531 315340958434239197000837297)
      ·
        refine ⟨236505718825679397750627973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315340958434239197000837297 236505718825679397750627973)
        ·
          refine ⟨44344822279814887078242745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236505718825679397750627973 44344822279814887078242745)
          ·
            refine ⟨33258616709861165308682059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44344822279814887078242745 33258616709861165308682059)
            ·
              refine ⟨49887925064791747963023089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33258616709861165308682059 49887925064791747963023089)
              ·
                refine ⟨37415943798593810972267317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49887925064791747963023089 37415943798593810972267317)
                ·
                  refine ⟨3507744731118169778650061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37415943798593810972267317 3507744731118169778650061)
                  ·
                    refine ⟨1315404274169313666993773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3507744731118169778650061 1315404274169313666993773)
                    ·
                      rfl

theorem cell22_3842611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 3].length) (baseStart_3842611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842611 prefixEnd_3842611 := by exact prefixLift 3842611
  have htrace : WordTrace (prefixWord ++ tailWord_3842611) baseStart_3842611 baseEnd_3842611 := by
    simpa [prefixWord, tailWord_3842611, baseEnd_3842611] using wordTrace_append hprefix tailTrace_3842611
  have hstable : (prefixWord ++ tailWord_3842611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842611).length < 2 ^ (prefixWord ++ tailWord_3842611).sum := by decide
  have hdescent : baseEnd_3842611 < baseStart_3842611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842735 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 2, 3]
def baseStart_3842735 : Nat := 118140960795 + 3842735 * 2 ^ 59
def prefixEnd_3842735 : Nat := 4983230072969 + 3 ^ 40 * 3842735 * 2
def baseEnd_3842735 : Nat := 1315446721903418676893393

theorem tailTrace_3842735 : CollatzResearch.WordTrace tailWord_3842735 prefixEnd_3842735 1315446721903418676893393 := by
  unfold tailWord_3842735
  simp only [CollatzResearch.WordTrace]
  refine ⟨140156059733434856733441659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93437373155623237822294439 140156059733434856733441659)
  ·
    refine ⟨210234089600152285100162489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140156059733434856733441659 210234089600152285100162489)
    ·
      refine ⟨157675567200114213825121867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210234089600152285100162489 157675567200114213825121867)
      ·
        refine ⟨236513350800171320737682801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157675567200114213825121867 236513350800171320737682801)
        ·
          refine ⟨177385013100128490553262101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236513350800171320737682801 177385013100128490553262101)
          ·
            refine ⟨8314922489068522994684161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177385013100128490553262101 8314922489068522994684161)
            ·
              refine ⟨6236191866801392246013121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8314922489068522994684161 6236191866801392246013121)
              ·
                refine ⟨4677143900101044184509841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6236191866801392246013121 4677143900101044184509841)
                ·
                  refine ⟨3507857925075783138382381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677143900101044184509841 3507857925075783138382381)
                  ·
                    refine ⟨1315446721903418676893393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3507857925075783138382381 1315446721903418676893393)
                    ·
                      rfl

theorem cell22_3842735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 3].length) (baseStart_3842735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842735 prefixEnd_3842735 := by exact prefixLift 3842735
  have htrace : WordTrace (prefixWord ++ tailWord_3842735) baseStart_3842735 baseEnd_3842735 := by
    simpa [prefixWord, tailWord_3842735, baseEnd_3842735] using wordTrace_append hprefix tailTrace_3842735
  have hstable : (prefixWord ++ tailWord_3842735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842735).length < 2 ^ (prefixWord ++ tailWord_3842735).sum := by decide
  have hdescent : baseEnd_3842735 < baseStart_3842735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842737 : List Nat := [1, 2, 2, 6, 1, 1, 1, 4, 4]
def baseStart_3842737 : Nat := 118140960795 + 3842737 * 2 ^ 59
def prefixEnd_3842737 : Nat := 4983230072969 + 3 ^ 40 * 3842737 * 2
def baseEnd_3842737 : Nat := 438482468848097112781129

theorem tailTrace_3842737 : CollatzResearch.WordTrace tailWord_3842737 prefixEnd_3842737 438482468848097112781129 := by
  unfold tailWord_3842737
  simp only [CollatzResearch.WordTrace]
  refine ⟨140156132679427611075014465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93437421786285074050009643 140156132679427611075014465)
  ·
    refine ⟨105117099509570708306260849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140156132679427611075014465 105117099509570708306260849)
    ·
      refine ⟨78837824632178031229695637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105117099509570708306260849 78837824632178031229695637)
      ·
        refine ⟨3695523029633345213891983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78837824632178031229695637 3695523029633345213891983)
        ·
          refine ⟨5543284544450017820837975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695523029633345213891983 5543284544450017820837975)
          ·
            refine ⟨8314926816675026731256963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5543284544450017820837975 8314926816675026731256963)
            ·
              refine ⟨12472390225012540096885445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8314926816675026731256963 12472390225012540096885445)
              ·
                refine ⟨2338573167189851268166021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12472390225012540096885445 2338573167189851268166021)
                ·
                  refine ⟨438482468848097112781129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338573167189851268166021 438482468848097112781129)
                  ·
                    rfl

theorem cell22_3842737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 4].length) (baseStart_3842737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842737 prefixEnd_3842737 := by exact prefixLift 3842737
  have htrace : WordTrace (prefixWord ++ tailWord_3842737) baseStart_3842737 baseEnd_3842737 := by
    simpa [prefixWord, tailWord_3842737, baseEnd_3842737] using wordTrace_append hprefix tailTrace_3842737
  have hstable : (prefixWord ++ tailWord_3842737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842737).length < 2 ^ (prefixWord ++ tailWord_3842737).sum := by decide
  have hdescent : baseEnd_3842737 < baseStart_3842737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842793 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 5]
def baseStart_3842793 : Nat := 118140960795 + 3842793 * 2 ^ 59
def prefixEnd_3842793 : Nat := 4983230072969 + 3 ^ 40 * 3842793 * 2
def baseEnd_3842793 : Nat := 438488858829575286314405

theorem tailTrace_3842793 : CollatzResearch.WordTrace tailWord_3842793 prefixEnd_3842793 438488858829575286314405 := by
  unfold tailWord_3842793
  simp only [CollatzResearch.WordTrace]
  refine ⟨140158175167224732639053033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93438783444816488426035355 140158175167224732639053033)
  ·
    refine ⟨105118631375418549479289775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140158175167224732639053033 105118631375418549479289775)
    ·
      refine ⟨157677947063127824218934663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105118631375418549479289775 157677947063127824218934663)
      ·
        refine ⟨236516920594691736328401995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157677947063127824218934663 236516920594691736328401995)
        ·
          refine ⟨354775380892037604492602993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236516920594691736328401995 354775380892037604492602993)
          ·
            refine ⟨266081535669028203369452245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354775380892037604492602993 266081535669028203369452245)
            ·
              refine ⟨6236285992242848516471537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 266081535669028203369452245 6236285992242848516471537)
              ·
                refine ⟨4677214494182136387353653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6236285992242848516471537 4677214494182136387353653)
                ·
                  refine ⟨438488858829575286314405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4677214494182136387353653 438488858829575286314405)
                  ·
                    rfl

theorem cell22_3842793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_3842793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842793 prefixEnd_3842793 := by exact prefixLift 3842793
  have htrace : WordTrace (prefixWord ++ tailWord_3842793) baseStart_3842793 baseEnd_3842793 := by
    simpa [prefixWord, tailWord_3842793, baseEnd_3842793] using wordTrace_append hprefix tailTrace_3842793
  have hstable : (prefixWord ++ tailWord_3842793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842793).length < 2 ^ (prefixWord ++ tailWord_3842793).sum := by decide
  have hdescent : baseEnd_3842793 < baseStart_3842793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842797 : List Nat := [1, 5, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_3842797 : Nat := 118140960795 + 3842797 * 2 ^ 59
def prefixEnd_3842797 : Nat := 4983230072969 + 3 ^ 40 * 3842797 * 2
def baseEnd_3842797 : Nat := 1315467945770471181843203

theorem tailTrace_3842797 : CollatzResearch.WordTrace tailWord_3842797 prefixEnd_3842797 1315467945770471181843203 := by
  unfold tailWord_3842797
  simp only [CollatzResearch.WordTrace]
  refine ⟨140158321059210241322198645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93438880706140160881465763 140158321059210241322198645)
  ·
    refine ⟨13139842599300960123956123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140158321059210241322198645 13139842599300960123956123)
    ·
      refine ⟨19709763898951440185934185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13139842599300960123956123 19709763898951440185934185)
      ·
        refine ⟨14782322924213580139450639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19709763898951440185934185 14782322924213580139450639)
        ·
          refine ⟨22173484386320370209175959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14782322924213580139450639 22173484386320370209175959)
          ·
            refine ⟨33260226579480555313763939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22173484386320370209175959 33260226579480555313763939)
            ·
              refine ⟨49890339869220832970645909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33260226579480555313763939 49890339869220832970645909)
              ·
                refine ⟨2338609681369726545499027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49890339869220832970645909 2338609681369726545499027)
                ·
                  refine ⟨3507914522054589818248541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338609681369726545499027 3507914522054589818248541)
                  ·
                    refine ⟨1315467945770471181843203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3507914522054589818248541 1315467945770471181843203)
                    ·
                      rfl

theorem cell22_3842797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_3842797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842797 prefixEnd_3842797 := by exact prefixLift 3842797
  have htrace : WordTrace (prefixWord ++ tailWord_3842797) baseStart_3842797 baseEnd_3842797 := by
    simpa [prefixWord, tailWord_3842797, baseEnd_3842797] using wordTrace_append hprefix tailTrace_3842797
  have hstable : (prefixWord ++ tailWord_3842797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842797).length < 2 ^ (prefixWord ++ tailWord_3842797).sum := by decide
  have hdescent : baseEnd_3842797 < baseStart_3842797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842861 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 5]
def baseStart_3842861 : Nat := 118140960795 + 3842861 * 2 ^ 59
def prefixEnd_3842861 : Nat := 4983230072969 + 3 ^ 40 * 3842861 * 2
def baseEnd_3842861 : Nat := 438496618092798782747669

theorem tailTrace_3842861 : CollatzResearch.WordTrace tailWord_3842861 prefixEnd_3842861 438496618092798782747669 := by
  unfold tailWord_3842861
  simp only [CollatzResearch.WordTrace]
  refine ⟨140160655330978380252528437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93440436887318920168352291 140160655330978380252528437)
  ·
    refine ⟨13140061437279223148674541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140160655330978380252528437 13140061437279223148674541)
    ·
      refine ⟨4927523038979708680752953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13140061437279223148674541 4927523038979708680752953)
      ·
        refine ⟨3695642279234781510564715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4927523038979708680752953 3695642279234781510564715)
        ·
          refine ⟨5543463418852172265847073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695642279234781510564715 5543463418852172265847073)
          ·
            refine ⟨4157597564139129199385305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5543463418852172265847073 4157597564139129199385305)
            ·
              refine ⟨3118198173104346899538979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157597564139129199385305 3118198173104346899538979)
              ·
                refine ⟨4677297259656520349308469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118198173104346899538979 4677297259656520349308469)
                ·
                  refine ⟨438496618092798782747669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4677297259656520349308469 438496618092798782747669)
                  ·
                    rfl

theorem cell22_3842861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_3842861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842861 prefixEnd_3842861 := by exact prefixLift 3842861
  have htrace : WordTrace (prefixWord ++ tailWord_3842861) baseStart_3842861 baseEnd_3842861 := by
    simpa [prefixWord, tailWord_3842861, baseEnd_3842861] using wordTrace_append hprefix tailTrace_3842861
  have hstable : (prefixWord ++ tailWord_3842861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842861).length < 2 ^ (prefixWord ++ tailWord_3842861).sum := by decide
  have hdescent : baseEnd_3842861 < baseStart_3842861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842874 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 1, 4]
def baseStart_3842874 : Nat := 118140960795 + 3842874 * 2 ^ 59
def prefixEnd_3842874 : Nat := 4983230072969 + 3 ^ 40 * 3842874 * 2
def baseEnd_3842874 : Nat := 1315494304444068647667967

theorem tailTrace_3842874 : CollatzResearch.WordTrace tailWord_3842874 prefixEnd_3842874 1315494304444068647667967 := by
  unfold tailWord_3842874
  simp only [CollatzResearch.WordTrace]
  refine ⟨35040282369982820868187919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93440752986620855648501117 35040282369982820868187919)
  ·
    refine ⟨52560423554974231302281879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35040282369982820868187919 52560423554974231302281879)
    ·
      refine ⟨78840635332461346953422819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52560423554974231302281879 78840635332461346953422819)
      ·
        refine ⟨118260952998692020430134229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78840635332461346953422819 118260952998692020430134229)
        ·
          refine ⟨2771741085906844228831271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118260952998692020430134229 2771741085906844228831271)
          ·
            refine ⟨4157611628860266343246907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771741085906844228831271 4157611628860266343246907)
            ·
              refine ⟨6236417443290399514870361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157611628860266343246907 6236417443290399514870361)
              ·
                refine ⟨4677313082467799636152771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6236417443290399514870361 4677313082467799636152771)
                ·
                  refine ⟨7015969623701699454229157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4677313082467799636152771 7015969623701699454229157)
                  ·
                    refine ⟨1315494304444068647667967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7015969623701699454229157 1315494304444068647667967)
                    ·
                      rfl

theorem cell22_3842874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_3842874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842874 prefixEnd_3842874 := by exact prefixLift 3842874
  have htrace : WordTrace (prefixWord ++ tailWord_3842874) baseStart_3842874 baseEnd_3842874 := by
    simpa [prefixWord, tailWord_3842874, baseEnd_3842874] using wordTrace_append hprefix tailTrace_3842874
  have hstable : (prefixWord ++ tailWord_3842874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842874).length < 2 ^ (prefixWord ++ tailWord_3842874).sum := by decide
  have hdescent : baseEnd_3842874 < baseStart_3842874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842900 : List Nat := [2, 4, 1, 1, 5, 9]
def baseStart_3842900 : Nat := 118140960795 + 3842900 * 2 ^ 59
def prefixEnd_3842900 : Nat := 4983230072969 + 3 ^ 40 * 3842900 * 2
def baseEnd_3842900 : Nat := 16240780305869299339727

theorem tailTrace_3842900 : CollatzResearch.WordTrace tailWord_3842900 prefixEnd_3842900 16240780305869299339727 := by
  unfold tailWord_3842900
  simp only [CollatzResearch.WordTrace]
  refine ⟨70081038888918544956599077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93441385185224726608798769 70081038888918544956599077)
  ·
    refine ⟨13140194791672227179362327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70081038888918544956599077 13140194791672227179362327)
    ·
      refine ⟨19710292187508340769043491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13140194791672227179362327 19710292187508340769043491)
      ·
        refine ⟨29565438281262511153565237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19710292187508340769043491 29565438281262511153565237)
        ·
          refine ⟨2771759838868360420646741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29565438281262511153565237 2771759838868360420646741)
          ·
            refine ⟨16240780305869299339727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2771759838868360420646741 16240780305869299339727)
            ·
              rfl

theorem cell22_3842900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 9].length) (baseStart_3842900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842900 prefixEnd_3842900 := by exact prefixLift 3842900
  have htrace : WordTrace (prefixWord ++ tailWord_3842900) baseStart_3842900 baseEnd_3842900 := by
    simpa [prefixWord, tailWord_3842900, baseEnd_3842900] using wordTrace_append hprefix tailTrace_3842900
  have hstable : (prefixWord ++ tailWord_3842900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842900).length < 2 ^ (prefixWord ++ tailWord_3842900).sum := by decide
  have hdescent : baseEnd_3842900 < baseStart_3842900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842949 : List Nat := [1, 3, 1, 1, 3, 4, 2, 3, 1, 3]
def baseStart_3842949 : Nat := 118140960795 + 3842949 * 2 ^ 59
def prefixEnd_3842949 : Nat := 4983230072969 + 3 ^ 40 * 3842949 * 2
def baseEnd_3842949 : Nat := 1315519978476793452042737

theorem tailTrace_3842949 : CollatzResearch.WordTrace tailWord_3842949 prefixEnd_3842949 1315519978476793452042737 := by
  unfold tailWord_3842949
  simp only [CollatzResearch.WordTrace]
  refine ⟨140163864954659571281731901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93442576636439714187821267 140163864954659571281731901)
  ·
    refine ⟨52561449357997339230649463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140163864954659571281731901 52561449357997339230649463)
    ·
      refine ⟨78842174036996008845974195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52561449357997339230649463 78842174036996008845974195)
      ·
        refine ⟨118263261055494013268961293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78842174036996008845974195 118263261055494013268961293)
        ·
          refine ⟨44348722895810254975860485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118263261055494013268961293 44348722895810254975860485)
          ·
            refine ⟨8315385542964422807973841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44348722895810254975860485 8315385542964422807973841)
            ·
              refine ⟨6236539157223317105980381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8315385542964422807973841 6236539157223317105980381)
              ·
                refine ⟨2338702183958743914742643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6236539157223317105980381 2338702183958743914742643)
                ·
                  refine ⟨3508053275938115872113965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338702183958743914742643 3508053275938115872113965)
                  ·
                    refine ⟨1315519978476793452042737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3508053275938115872113965 1315519978476793452042737)
                    ·
                      rfl

theorem cell22_3842949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_3842949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842949 prefixEnd_3842949 := by exact prefixLift 3842949
  have htrace : WordTrace (prefixWord ++ tailWord_3842949) baseStart_3842949 baseEnd_3842949 := by
    simpa [prefixWord, tailWord_3842949, baseEnd_3842949] using wordTrace_append hprefix tailTrace_3842949
  have hstable : (prefixWord ++ tailWord_3842949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842949).length < 2 ^ (prefixWord ++ tailWord_3842949).sum := by decide
  have hdescent : baseEnd_3842949 < baseStart_3842949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842962 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_3842962 : Nat := 118140960795 + 3842962 * 2 ^ 59
def prefixEnd_3842962 : Nat := 4983230072969 + 3 ^ 40 * 3842962 * 2
def baseEnd_3842962 : Nat := 438508142880821917155899

theorem tailTrace_3842962 : CollatzResearch.WordTrace tailWord_3842962 prefixEnd_3842962 438508142880821917155899 := by
  unfold tailWord_3842962
  simp only [CollatzResearch.WordTrace]
  refine ⟨35041084775903118625488785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93442892735741649667970093 35041084775903118625488785)
  ·
    refine ⟨26280813581927338969116589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35041084775903118625488785 26280813581927338969116589)
    ·
      refine ⟨9855305093222752113418721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26280813581927338969116589 9855305093222752113418721)
      ·
        refine ⟨7391478819917064085064041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9855305093222752113418721 7391478819917064085064041)
        ·
          refine ⟨5543609114937798063798031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7391478819917064085064041 5543609114937798063798031)
          ·
            refine ⟨8315413672406697095697047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5543609114937798063798031 8315413672406697095697047)
            ·
              refine ⟨12473120508610045643545571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8315413672406697095697047 12473120508610045643545571)
              ·
                refine ⟨18709680762915068465318357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12473120508610045643545571 18709680762915068465318357)
                ·
                  refine ⟨438508142880821917155899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18709680762915068465318357 438508142880821917155899)
                  ·
                    rfl

theorem cell22_3842962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_3842962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842962 prefixEnd_3842962 := by exact prefixLift 3842962
  have htrace : WordTrace (prefixWord ++ tailWord_3842962) baseStart_3842962 baseEnd_3842962 := by
    simpa [prefixWord, tailWord_3842962, baseEnd_3842962] using wordTrace_append hprefix tailTrace_3842962
  have hstable : (prefixWord ++ tailWord_3842962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842962).length < 2 ^ (prefixWord ++ tailWord_3842962).sum := by decide
  have hdescent : baseEnd_3842962 < baseStart_3842962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842966 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3842966 : Nat := 118140960795 + 3842966 * 2 ^ 59
def prefixEnd_3842966 : Nat := 4983230072969 + 3 ^ 40 * 3842966 * 2
def baseEnd_3842966 : Nat := 1315525797924211074367685

theorem tailTrace_3842966 : CollatzResearch.WordTrace tailWord_3842966 prefixEnd_3842966 1315525797924211074367685 := by
  unfold tailWord_3842966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760280312224873949068797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93442989997065322123400501 8760280312224873949068797)
  ·
    refine ⟨3285105117084327730900799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8760280312224873949068797 3285105117084327730900799)
    ·
      refine ⟨4927657675626491596351199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285105117084327730900799 4927657675626491596351199)
      ·
        refine ⟨7391486513439737394526799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927657675626491596351199 7391486513439737394526799)
        ·
          refine ⟨11087229770159606091790199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391486513439737394526799 11087229770159606091790199)
          ·
            refine ⟨16630844655239409137685299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11087229770159606091790199 16630844655239409137685299)
            ·
              refine ⟨24946266982859113706527949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16630844655239409137685299 24946266982859113706527949)
              ·
                refine ⟨9354850118572167639947981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24946266982859113706527949 9354850118572167639947981)
                ·
                  refine ⟨3508068794464562864980493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9354850118572167639947981 3508068794464562864980493)
                  ·
                    refine ⟨1315525797924211074367685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3508068794464562864980493 1315525797924211074367685)
                    ·
                      rfl

theorem cell22_3842966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3842966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3842966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3842966 prefixEnd_3842966 := by exact prefixLift 3842966
  have htrace : WordTrace (prefixWord ++ tailWord_3842966) baseStart_3842966 baseEnd_3842966 := by
    simpa [prefixWord, tailWord_3842966, baseEnd_3842966] using wordTrace_append hprefix tailTrace_3842966
  have hstable : (prefixWord ++ tailWord_3842966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842966).length < 2 ^ (prefixWord ++ tailWord_3842966).sum := by decide
  have hdescent : baseEnd_3842966 < baseStart_3842966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843003 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 5, 6]
def baseStart_3843003 : Nat := 118140960795 + 3843003 * 2 ^ 59
def prefixEnd_3843003 : Nat := 4983230072969 + 3 ^ 40 * 3843003 * 2
def baseEnd_3843003 : Nat := 1315538463780355311192571

theorem tailTrace_3843003 : CollatzResearch.WordTrace tailWord_3843003 prefixEnd_3843003 1315538463780355311192571 := by
  unfold tailWord_3843003
  simp only [CollatzResearch.WordTrace]
  refine ⟨140165834496463938504197663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93443889664309292336131775 140165834496463938504197663)
  ·
    refine ⟨210248751744695907756296495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140165834496463938504197663 210248751744695907756296495)
    ·
      refine ⟨315373127617043861634444743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210248751744695907756296495 315373127617043861634444743)
      ·
        refine ⟨473059691425565792451667115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315373127617043861634444743 473059691425565792451667115)
        ·
          refine ⟨709589537138348688677500673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473059691425565792451667115 709589537138348688677500673)
          ·
            refine ⟨532192152853761516508125505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709589537138348688677500673 532192152853761516508125505)
            ·
              refine ⟨399144114640321137381094129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532192152853761516508125505 399144114640321137381094129)
              ·
                refine ⟨299358085980240853035820597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399144114640321137381094129 299358085980240853035820597)
                ·
                  refine ⟨28064820560647579972108181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 299358085980240853035820597 28064820560647579972108181)
                  ·
                    refine ⟨1315538463780355311192571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28064820560647579972108181 1315538463780355311192571)
                    ·
                      rfl

theorem cell22_3843003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_3843003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843003 prefixEnd_3843003 := by exact prefixLift 3843003
  have htrace : WordTrace (prefixWord ++ tailWord_3843003) baseStart_3843003 baseEnd_3843003 := by
    simpa [prefixWord, tailWord_3843003, baseEnd_3843003] using wordTrace_append hprefix tailTrace_3843003
  have hstable : (prefixWord ++ tailWord_3843003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843003).length < 2 ^ (prefixWord ++ tailWord_3843003).sum := by decide
  have hdescent : baseEnd_3843003 < baseStart_3843003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843022 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_3843022 : Nat := 118140960795 + 3843022 * 2 ^ 59
def prefixEnd_3843022 : Nat := 4983230072969 + 3 ^ 40 * 3843022 * 2
def baseEnd_3843022 : Nat := 1315544967868645594967513

theorem tailTrace_3843022 : CollatzResearch.WordTrace tailWord_3843022 prefixEnd_3843022 1315544967868645594967513 := by
  unfold tailWord_3843022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17520815935424388093642415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93444351655596736499426213 17520815935424388093642415)
  ·
    refine ⟨26281223903136582140463623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17520815935424388093642415 26281223903136582140463623)
    ·
      refine ⟨39421835854704873210695435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26281223903136582140463623 39421835854704873210695435)
      ·
        refine ⟨59132753782057309816043153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39421835854704873210695435 59132753782057309816043153)
        ·
          refine ⟨44349565336542982362032365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59132753782057309816043153 44349565336542982362032365)
          ·
            refine ⟨16631087001203618385762137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44349565336542982362032365 16631087001203618385762137)
            ·
              refine ⟨12473315250902713789321603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16631087001203618385762137 12473315250902713789321603)
              ·
                refine ⟨18709972876354070683982405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12473315250902713789321603 18709972876354070683982405)
                ·
                  refine ⟨3508119914316388253246701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18709972876354070683982405 3508119914316388253246701)
                  ·
                    refine ⟨1315544967868645594967513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3508119914316388253246701 1315544967868645594967513)
                    ·
                      rfl

theorem cell22_3843022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_3843022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843022 prefixEnd_3843022 := by exact prefixLift 3843022
  have htrace : WordTrace (prefixWord ++ tailWord_3843022) baseStart_3843022 baseEnd_3843022 := by
    simpa [prefixWord, tailWord_3843022, baseEnd_3843022] using wordTrace_append hprefix tailTrace_3843022
  have hstable : (prefixWord ++ tailWord_3843022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843022).length < 2 ^ (prefixWord ++ tailWord_3843022).sum := by decide
  have hdescent : baseEnd_3843022 < baseStart_3843022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843039 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 2, 3]
def baseStart_3843039 : Nat := 118140960795 + 3843039 * 2 ^ 59
def prefixEnd_3843039 : Nat := 4983230072969 + 3 ^ 40 * 3843039 * 2
def baseEnd_3843039 : Nat := 1315550787316063217292461

theorem tailTrace_3843039 : CollatzResearch.WordTrace tailWord_3843039 prefixEnd_3843039 1315550787316063217292461 := by
  unfold tailWord_3843039
  simp only [CollatzResearch.WordTrace]
  refine ⟨140167147524333516652508171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93444765016222344435005447 140167147524333516652508171)
  ·
    refine ⟨210250721286500274978762257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140167147524333516652508171 210250721286500274978762257)
    ·
      refine ⟨157688040964875206234071693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210250721286500274978762257 157688040964875206234071693)
      ·
        refine ⟨59133015361828202337776885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157688040964875206234071693 59133015361828202337776885)
        ·
          refine ⟨5543720190171393969166583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59133015361828202337776885 5543720190171393969166583)
          ·
            refine ⟨8315580285257090953749875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5543720190171393969166583 8315580285257090953749875)
            ·
              refine ⟨12473370427885636430624813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8315580285257090953749875 12473370427885636430624813)
              ·
                refine ⟨4677513910457113661484305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12473370427885636430624813 4677513910457113661484305)
                ·
                  refine ⟨3508135432842835246113229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677513910457113661484305 3508135432842835246113229)
                  ·
                    refine ⟨1315550787316063217292461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3508135432842835246113229 1315550787316063217292461)
                    ·
                      rfl

theorem cell22_3843039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 3].length) (baseStart_3843039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843039 prefixEnd_3843039 := by exact prefixLift 3843039
  have htrace : WordTrace (prefixWord ++ tailWord_3843039) baseStart_3843039 baseEnd_3843039 := by
    simpa [prefixWord, tailWord_3843039, baseEnd_3843039] using wordTrace_append hprefix tailTrace_3843039
  have hstable : (prefixWord ++ tailWord_3843039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843039).length < 2 ^ (prefixWord ++ tailWord_3843039).sum := by decide
  have hdescent : baseEnd_3843039 < baseStart_3843039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843054 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_3843054 : Nat := 118140960795 + 3843054 * 2 ^ 59
def prefixEnd_3843054 : Nat := 4983230072969 + 3 ^ 40 * 3843054 * 2
def baseEnd_3843054 : Nat := 1315555922122608178167415

theorem tailTrace_3843054 : CollatzResearch.WordTrace tailWord_3843054 prefixEnd_3843054 1315555922122608178167415 := by
  unfold tailWord_3843054
  simp only [CollatzResearch.WordTrace]
  refine ⟨17520961827409896776788027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93445129746186116142869477 17520961827409896776788027)
  ·
    refine ⟨26281442741114845165182041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17520961827409896776788027 26281442741114845165182041)
    ·
      refine ⟨19711082055836133873886531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26281442741114845165182041 19711082055836133873886531)
      ·
        refine ⟨29566623083754200810829797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19711082055836133873886531 29566623083754200810829797)
        ·
          refine ⟨5543741828203912652030587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29566623083754200810829797 5543741828203912652030587)
          ·
            refine ⟨8315612742305868978045881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5543741828203912652030587 8315612742305868978045881)
            ·
              refine ⟨6236709556729401733534411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8315612742305868978045881 6236709556729401733534411)
              ·
                refine ⟨9355064335094102600301617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6236709556729401733534411 9355064335094102600301617)
                ·
                  refine ⟨7016298251320576950226213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9355064335094102600301617 7016298251320576950226213)
                  ·
                    refine ⟨1315555922122608178167415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7016298251320576950226213 1315555922122608178167415)
                    ·
                      rfl

theorem cell22_3843054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_3843054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843054 prefixEnd_3843054 := by exact prefixLift 3843054
  have htrace : WordTrace (prefixWord ++ tailWord_3843054) baseStart_3843054 baseEnd_3843054 := by
    simpa [prefixWord, tailWord_3843054, baseEnd_3843054] using wordTrace_append hprefix tailTrace_3843054
  have hstable : (prefixWord ++ tailWord_3843054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843054).length < 2 ^ (prefixWord ++ tailWord_3843054).sum := by decide
  have hdescent : baseEnd_3843054 < baseStart_3843054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843125 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 10]
def baseStart_3843125 : Nat := 118140960795 + 3843125 * 2 ^ 59
def prefixEnd_3843125 : Nat := 4983230072969 + 3 ^ 40 * 3843125 * 2
def baseEnd_3843125 : Nat := 438526742291195886547399

theorem tailTrace_3843125 : CollatzResearch.WordTrace tailWord_3843125 prefixEnd_3843125 438526742291195886547399 := by
  unfold tailWord_3843125
  simp only [CollatzResearch.WordTrace]
  refine ⟨140170284202021953340138829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93446856134681302226759219 140170284202021953340138829)
  ·
    refine ⟨52563856575758232502552061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140170284202021953340138829 52563856575758232502552061)
    ·
      refine ⟨19711446215909337188457023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52563856575758232502552061 19711446215909337188457023)
      ·
        refine ⟨29567169323864005782685535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19711446215909337188457023 29567169323864005782685535)
        ·
          refine ⟨44350753985796008674028303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29567169323864005782685535 44350753985796008674028303)
          ·
            refine ⟨66526130978694013011042455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44350753985796008674028303 66526130978694013011042455)
            ·
              refine ⟨99789196468041019516563683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66526130978694013011042455 99789196468041019516563683)
              ·
                refine ⟨149683794702061529274845525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99789196468041019516563683 149683794702061529274845525)
                ·
                  refine ⟨438526742291195886547399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149683794702061529274845525 438526742291195886547399)
                  ·
                    rfl

theorem cell22_3843125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_3843125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843125 prefixEnd_3843125 := by exact prefixLift 3843125
  have htrace : WordTrace (prefixWord ++ tailWord_3843125) baseStart_3843125 baseEnd_3843125 := by
    simpa [prefixWord, tailWord_3843125, baseEnd_3843125] using wordTrace_append hprefix tailTrace_3843125
  have hstable : (prefixWord ++ tailWord_3843125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843125).length < 2 ^ (prefixWord ++ tailWord_3843125).sum := by decide
  have hdescent : baseEnd_3843125 < baseStart_3843125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843155 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 1, 6]
def baseStart_3843155 : Nat := 118140960795 + 3843155 * 2 ^ 59
def prefixEnd_3843155 : Nat := 4983230072969 + 3 ^ 40 * 3843155 * 2
def baseEnd_3843155 : Nat := 1315590496486677581392105

theorem tailTrace_3843155 : CollatzResearch.WordTrace tailWord_3843155 prefixEnd_3843155 1315590496486677581392105 := by
  unfold tailWord_3843155
  simp only [CollatzResearch.WordTrace]
  refine ⟨140171378391913268463730919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93447585594608845642487279 140171378391913268463730919)
  ·
    refine ⟨210257067587869902695596379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140171378391913268463730919 210257067587869902695596379)
    ·
      refine ⟨315385601381804854043394569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210257067587869902695596379 315385601381804854043394569)
      ·
        refine ⟨236539201036353640532545927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315385601381804854043394569 236539201036353640532545927)
        ·
          refine ⟨354808801554530460798818891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236539201036353640532545927 354808801554530460798818891)
          ·
            refine ⟨532213202331795691198228337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354808801554530460798818891 532213202331795691198228337)
            ·
              refine ⟨399159901748846768398671253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532213202331795691198228337 399159901748846768398671253)
              ·
                refine ⟨18710620394477192268687715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 399159901748846768398671253 18710620394477192268687715)
                ·
                  refine ⟨28065930591715788403031573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18710620394477192268687715 28065930591715788403031573)
                  ·
                    refine ⟨1315590496486677581392105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28065930591715788403031573 1315590496486677581392105)
                    ·
                      rfl

theorem cell22_3843155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_3843155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843155 prefixEnd_3843155 := by exact prefixLift 3843155
  have htrace : WordTrace (prefixWord ++ tailWord_3843155) baseStart_3843155 baseEnd_3843155 := by
    simpa [prefixWord, tailWord_3843155, baseEnd_3843155] using wordTrace_append hprefix tailTrace_3843155
  have hstable : (prefixWord ++ tailWord_3843155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843155).length < 2 ^ (prefixWord ++ tailWord_3843155).sum := by decide
  have hdescent : baseEnd_3843155 < baseStart_3843155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843172 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_3843172 : Nat := 118140960795 + 3843172 * 2 ^ 59
def prefixEnd_3843172 : Nat := 4983230072969 + 3 ^ 40 * 3843172 * 2
def baseEnd_3843172 : Nat := 1315596315934095203717053

theorem tailTrace_3843172 : CollatzResearch.WordTrace tailWord_3843172 prefixEnd_3843172 1315596315934095203717053 := by
  unfold tailWord_3843172
  simp only [CollatzResearch.WordTrace]
  refine ⟨70085999216425840183549885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93447998955234453578066513 70085999216425840183549885)
  ·
    refine ⟨26282249706159690068831207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70085999216425840183549885 26282249706159690068831207)
    ·
      refine ⟨39423374559239535103246811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26282249706159690068831207 39423374559239535103246811)
      ·
        refine ⟨59135061838859302654870217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39423374559239535103246811 59135061838859302654870217)
        ·
          refine ⟨44351296379144476991152663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59135061838859302654870217 44351296379144476991152663)
          ·
            refine ⟨66526944568716715486728995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44351296379144476991152663 66526944568716715486728995)
            ·
              refine ⟨99790416853075073230093493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66526944568716715486728995 99790416853075073230093493)
              ·
                refine ⟨9355351579975788115321265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99790416853075073230093493 9355351579975788115321265)
                ·
                  refine ⟨7016513684981841086490949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9355351579975788115321265 7016513684981841086490949)
                  ·
                    refine ⟨1315596315934095203717053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7016513684981841086490949 1315596315934095203717053)
                    ·
                      rfl

theorem cell22_3843172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_3843172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843172 prefixEnd_3843172 := by exact prefixLift 3843172
  have htrace : WordTrace (prefixWord ++ tailWord_3843172) baseStart_3843172 baseEnd_3843172 := by
    simpa [prefixWord, tailWord_3843172, baseEnd_3843172] using wordTrace_append hprefix tailTrace_3843172
  have hstable : (prefixWord ++ tailWord_3843172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843172).length < 2 ^ (prefixWord ++ tailWord_3843172).sum := by decide
  have hdescent : baseEnd_3843172 < baseStart_3843172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843249 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 5]
def baseStart_3843249 : Nat := 118140960795 + 3843249 * 2 ^ 59
def prefixEnd_3843249 : Nat := 4983230072969 + 3 ^ 40 * 3843249 * 2
def baseEnd_3843249 : Nat := 438540891535897556513939

theorem tailTrace_3843249 : CollatzResearch.WordTrace tailWord_3843249 prefixEnd_3843249 438540891535897556513939 := by
  unfold tailWord_3843249
  simp only [CollatzResearch.WordTrace]
  refine ⟨140174806853572722517652801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93449871235715148345101867 140174806853572722517652801)
  ·
    refine ⟨105131105140179541888239601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140174806853572722517652801 105131105140179541888239601)
    ·
      refine ⟨78848328855134656416179701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105131105140179541888239601 78848328855134656416179701)
      ·
        refine ⟨7392030830168874039016847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78848328855134656416179701 7392030830168874039016847)
        ·
          refine ⟨11088046245253311058525271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7392030830168874039016847 11088046245253311058525271)
          ·
            refine ⟨16632069367879966587787907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11088046245253311058525271 16632069367879966587787907)
            ·
              refine ⟨24948104051819949881681861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16632069367879966587787907 24948104051819949881681861)
              ·
                refine ⟨4677769509716240602815349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24948104051819949881681861 4677769509716240602815349)
                ·
                  refine ⟨438540891535897556513939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4677769509716240602815349 438540891535897556513939)
                  ·
                    rfl

theorem cell22_3843249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_3843249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843249 prefixEnd_3843249 := by exact prefixLift 3843249
  have htrace : WordTrace (prefixWord ++ tailWord_3843249) baseStart_3843249 baseEnd_3843249 := by
    simpa [prefixWord, tailWord_3843249, baseEnd_3843249] using wordTrace_append hprefix tailTrace_3843249
  have hstable : (prefixWord ++ tailWord_3843249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843249).length < 2 ^ (prefixWord ++ tailWord_3843249).sum := by decide
  have hdescent : baseEnd_3843249 < baseStart_3843249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843264 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 2, 5]
def baseStart_3843264 : Nat := 118140960795 + 3843264 * 2 ^ 59
def prefixEnd_3843264 : Nat := 4983230072969 + 3 ^ 40 * 3843264 * 2
def baseEnd_3843264 : Nat := 1315627809414237630416771

theorem tailTrace_3843264 : CollatzResearch.WordTrace tailWord_3843264 prefixEnd_3843264 1315627809414237630416771 := by
  unfold tailWord_3843264
  simp only [CollatzResearch.WordTrace]
  refine ⟨70087676974259190039724423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93450235965678920052965897 70087676974259190039724423)
  ·
    refine ⟨105131515461388785059586635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70087676974259190039724423 105131515461388785059586635)
    ·
      refine ⟨157697273192083177589379953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105131515461388785059586635 157697273192083177589379953)
      ·
        refine ⟨118272954894062383192034965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157697273192083177589379953 118272954894062383192034965)
        ·
          refine ⟨5544044760659174212126639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118272954894062383192034965 5544044760659174212126639)
          ·
            refine ⟨8316067140988761318189959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5544044760659174212126639 8316067140988761318189959)
            ·
              refine ⟨12474100711483141977284939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8316067140988761318189959 12474100711483141977284939)
              ·
                refine ⟨18711151067224712965927409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12474100711483141977284939 18711151067224712965927409)
                ·
                  refine ⟨14033363300418534724445557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18711151067224712965927409 14033363300418534724445557)
                  ·
                    refine ⟨1315627809414237630416771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14033363300418534724445557 1315627809414237630416771)
                    ·
                      rfl

theorem cell22_3843264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_3843264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843264 prefixEnd_3843264 := by exact prefixLift 3843264
  have htrace : WordTrace (prefixWord ++ tailWord_3843264) baseStart_3843264 baseEnd_3843264 := by
    simpa [prefixWord, tailWord_3843264, baseEnd_3843264] using wordTrace_append hprefix tailTrace_3843264
  have hstable : (prefixWord ++ tailWord_3843264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843264).length < 2 ^ (prefixWord ++ tailWord_3843264).sum := by decide
  have hdescent : baseEnd_3843264 < baseStart_3843264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843296 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 1, 4]
def baseStart_3843296 : Nat := 118140960795 + 3843296 * 2 ^ 59
def prefixEnd_3843296 : Nat := 4983230072969 + 3 ^ 40 * 3843296 * 2
def baseEnd_3843296 : Nat := 1315638763668200213616673

theorem tailTrace_3843296 : CollatzResearch.WordTrace tailWord_3843296 prefixEnd_3843296 1315638763668200213616673 := by
  unfold tailWord_3843296
  simp only [CollatzResearch.WordTrace]
  refine ⟨70088260542201224772306871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93451014056268299696409161 70088260542201224772306871)
  ·
    refine ⟨105132390813301837158460307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70088260542201224772306871 105132390813301837158460307)
    ·
      refine ⟨157698586219952755737690461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105132390813301837158460307 157698586219952755737690461)
      ·
        refine ⟨59136969832482283401633923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157698586219952755737690461 59136969832482283401633923)
        ·
          refine ⟨88705454748723425102450885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59136969832482283401633923 88705454748723425102450885)
          ·
            refine ⟨16632272765385642206709541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88705454748723425102450885 16632272765385642206709541)
            ·
              refine ⟨3118551143509807913758039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16632272765385642206709541 3118551143509807913758039)
              ·
                refine ⟨4677826715264711870637059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118551143509807913758039 4677826715264711870637059)
                ·
                  refine ⟨7016740072897067805955589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4677826715264711870637059 7016740072897067805955589)
                  ·
                    refine ⟨1315638763668200213616673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7016740072897067805955589 1315638763668200213616673)
                    ·
                      rfl

theorem cell22_3843296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 4].length) (baseStart_3843296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843296 prefixEnd_3843296 := by exact prefixLift 3843296
  have htrace : WordTrace (prefixWord ++ tailWord_3843296) baseStart_3843296 baseEnd_3843296 := by
    simpa [prefixWord, tailWord_3843296, baseEnd_3843296] using wordTrace_append hprefix tailTrace_3843296
  have hstable : (prefixWord ++ tailWord_3843296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843296).length < 2 ^ (prefixWord ++ tailWord_3843296).sum := by decide
  have hdescent : baseEnd_3843296 < baseStart_3843296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843322 : List Nat := [3, 1, 1, 1, 1, 4, 2, 9]
def baseStart_3843322 : Nat := 118140960795 + 3843322 * 2 ^ 59
def prefixEnd_3843322 : Nat := 4983230072969 + 3 ^ 40 * 3843322 * 2
def baseEnd_3843322 : Nat := 146183073777727201385177

theorem tailTrace_3843322 : CollatzResearch.WordTrace tailWord_3843322 prefixEnd_3843322 146183073777727201385177 := by
  unfold tailWord_3843322
  simp only [CollatzResearch.WordTrace]
  refine ⟨35044367345577063996265055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93451646254872170656706813 35044367345577063996265055)
  ·
    refine ⟨52566551018365595994397583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35044367345577063996265055 52566551018365595994397583)
    ·
      refine ⟨78849826527548393991596375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52566551018365595994397583 78849826527548393991596375)
      ·
        refine ⟨118274739791322590987394563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78849826527548393991596375 118274739791322590987394563)
        ·
          refine ⟨177412109686983886481091845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118274739791322590987394563 177412109686983886481091845)
          ·
            refine ⟨33264770566309478715204721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177412109686983886481091845 33264770566309478715204721)
            ·
              refine ⟨24948577924732109036403541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33264770566309478715204721 24948577924732109036403541)
              ·
                refine ⟨146183073777727201385177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24948577924732109036403541 146183073777727201385177)
                ·
                  rfl

theorem cell22_3843322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_3843322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843322 prefixEnd_3843322 := by exact prefixLift 3843322
  have htrace : WordTrace (prefixWord ++ tailWord_3843322) baseStart_3843322 baseEnd_3843322 := by
    simpa [prefixWord, tailWord_3843322, baseEnd_3843322] using wordTrace_append hprefix tailTrace_3843322
  have hstable : (prefixWord ++ tailWord_3843322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843322).length < 2 ^ (prefixWord ++ tailWord_3843322).sum := by decide
  have hdescent : baseEnd_3843322 < baseStart_3843322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843326 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3843326 : Nat := 118140960795 + 3843326 * 2 ^ 59
def prefixEnd_3843326 : Nat := 4983230072969 + 3 ^ 40 * 3843326 * 2
def baseEnd_3843326 : Nat := 1315649033281290135366581

theorem tailTrace_3843326 : CollatzResearch.WordTrace tailWord_3843326 prefixEnd_3843326 1315649033281290135366581 := by
  unfold tailWord_3843326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17522201909286720583525729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93451743516195843112137221 17522201909286720583525729)
  ·
    refine ⟨13141651431965040437644297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17522201909286720583525729 13141651431965040437644297)
    ·
      refine ⟨9856238573973780328233223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13141651431965040437644297 9856238573973780328233223)
      ·
        refine ⟨14784357860960670492349835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9856238573973780328233223 14784357860960670492349835)
        ·
          refine ⟨22176536791441005738524753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14784357860960670492349835 22176536791441005738524753)
          ·
            refine ⟨16632402593580754303893565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22176536791441005738524753 16632402593580754303893565)
            ·
              refine ⟨6237150972592782863960087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16632402593580754303893565 6237150972592782863960087)
              ·
                refine ⟨9355726458889174295940131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6237150972592782863960087 9355726458889174295940131)
                ·
                  refine ⟨14033589688333761443910197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9355726458889174295940131 14033589688333761443910197)
                  ·
                    refine ⟨1315649033281290135366581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14033589688333761443910197 1315649033281290135366581)
                    ·
                      rfl

theorem cell22_3843326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3843326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843326 prefixEnd_3843326 := by exact prefixLift 3843326
  have htrace : WordTrace (prefixWord ++ tailWord_3843326) baseStart_3843326 baseEnd_3843326 := by
    simpa [prefixWord, tailWord_3843326, baseEnd_3843326] using wordTrace_append hprefix tailTrace_3843326
  have hstable : (prefixWord ++ tailWord_3843326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843326).length < 2 ^ (prefixWord ++ tailWord_3843326).sum := by decide
  have hdescent : baseEnd_3843326 < baseStart_3843326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843337 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_3843337 : Nat := 118140960795 + 3843337 * 2 ^ 59
def prefixEnd_3843337 : Nat := 4983230072969 + 3 ^ 40 * 3843337 * 2
def baseEnd_3843337 : Nat := 1315652798806089773341547

theorem tailTrace_3843337 : CollatzResearch.WordTrace tailWord_3843337 prefixEnd_3843337 1315652798806089773341547 := by
  unfold tailWord_3843337
  simp only [CollatzResearch.WordTrace]
  refine ⟨140178016477253913546856265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93452010984835942364570843 140178016477253913546856265)
  ·
    refine ⟨105133512357940435160142199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140178016477253913546856265 105133512357940435160142199)
    ·
      refine ⟨157700268536910652740213299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105133512357940435160142199 157700268536910652740213299)
      ·
        refine ⟨236550402805365979110319949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157700268536910652740213299 236550402805365979110319949)
        ·
          refine ⟨88706401052012242166369981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236550402805365979110319949 88706401052012242166369981)
          ·
            refine ⟨33264900394504590812388743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88706401052012242166369981 33264900394504590812388743)
            ·
              refine ⟨49897350591756886218583115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33264900394504590812388743 49897350591756886218583115)
              ·
                refine ⟨74846025887635329327874673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49897350591756886218583115 74846025887635329327874673)
                ·
                  refine ⟨56134519415726496995906005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74846025887635329327874673 56134519415726496995906005)
                  ·
                    refine ⟨1315652798806089773341547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56134519415726496995906005 1315652798806089773341547)
                    ·
                      rfl

theorem cell22_3843337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_3843337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843337 prefixEnd_3843337 := by exact prefixLift 3843337
  have htrace : WordTrace (prefixWord ++ tailWord_3843337) baseStart_3843337 baseEnd_3843337 := by
    simpa [prefixWord, tailWord_3843337, baseEnd_3843337] using wordTrace_append hprefix tailTrace_3843337
  have hstable : (prefixWord ++ tailWord_3843337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843337).length < 2 ^ (prefixWord ++ tailWord_3843337).sum := by decide
  have hdescent : baseEnd_3843337 < baseStart_3843337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
