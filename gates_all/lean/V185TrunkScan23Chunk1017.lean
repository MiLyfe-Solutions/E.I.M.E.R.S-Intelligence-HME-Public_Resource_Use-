import V185TrunkScan23Chunk1016

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6020856 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 1, 6, 3]
def baseStart_6020856 : Nat := 118140960795 + 6020856 * 2 ^ 59
def prefixEnd_6020856 : Nat := 4983230072969 + 3 ^ 40 * 6020856 * 2
def baseEnd_6020856 : Nat := 3091593079506800606910593

theorem tailTrace_6020856 : CollatzResearch.WordTrace tailWord_6020856 prefixEnd_6020856 3091593079506800606910593 := by
  unfold tailWord_6020856
  simp only [CollatzResearch.WordTrace]
  refine ⟨109799329537737233592165211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146399106050316311456220281 109799329537737233592165211)
  ·
    refine ⟨164698994306605850388247817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109799329537737233592165211 164698994306605850388247817)
    ·
      refine ⟨123524245729954387791185863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164698994306605850388247817 123524245729954387791185863)
      ·
        refine ⟨185286368594931581686778795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123524245729954387791185863 185286368594931581686778795)
        ·
          refine ⟨277929552892397372530168193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185286368594931581686778795 277929552892397372530168193)
          ·
            refine ⟨208447164669298029397626145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277929552892397372530168193 208447164669298029397626145)
            ·
              refine ⟨156335373501973522048219609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208447164669298029397626145 156335373501973522048219609)
              ·
                refine ⟨117251530126480141536164707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156335373501973522048219609 117251530126480141536164707)
                ·
                  refine ⟨175877295189720212304247061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117251530126480141536164707 175877295189720212304247061)
                  ·
                    refine ⟨8244248212018134951761581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 175877295189720212304247061 8244248212018134951761581)
                    ·
                      refine ⟨3091593079506800606910593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8244248212018134951761581 3091593079506800606910593)
                      ·
                        rfl

theorem cell23_6020856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_6020856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020856 prefixEnd_6020856 := by exact prefixLift 6020856
  have htrace : WordTrace (prefixWord ++ tailWord_6020856) baseStart_6020856 baseEnd_6020856 := by
    simpa [prefixWord, tailWord_6020856, baseEnd_6020856] using wordTrace_append hprefix tailTrace_6020856
  have hstable : (prefixWord ++ tailWord_6020856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020856).length < 2 ^ (prefixWord ++ tailWord_6020856).sum := by decide
  have hdescent : baseEnd_6020856 < baseStart_6020856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020876 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 7]
def baseStart_6020876 : Nat := 118140960795 + 6020876 * 2 ^ 59
def prefixEnd_6020876 : Nat := 4983230072969 + 3 ^ 40 * 6020876 * 2
def baseEnd_6020876 : Nat := 343511483235543392073389

theorem tailTrace_6020876 : CollatzResearch.WordTrace tailWord_6020876 prefixEnd_6020876 343511483235543392073389 := by
  unfold tailWord_6020876
  simp only [CollatzResearch.WordTrace]
  refine ⟨109799694267701005300029241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146399592356934673733372321 109799694267701005300029241)
  ·
    refine ⟨82349770700775753975021931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109799694267701005300029241 82349770700775753975021931)
    ·
      refine ⟨123524656051163630962532897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82349770700775753975021931 123524656051163630962532897)
      ·
        refine ⟨92643492038372723221899673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123524656051163630962532897 92643492038372723221899673)
        ·
          refine ⟨69482619028779542416424755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92643492038372723221899673 69482619028779542416424755)
          ·
            refine ⟨104223928543169313624637133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69482619028779542416424755 104223928543169313624637133)
            ·
              refine ⟨39083973203688492609238925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104223928543169313624637133 39083973203688492609238925)
              ·
                refine ⟨14656489951383184728464597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39083973203688492609238925 14656489951383184728464597)
                ·
                  refine ⟨343511483235543392073389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14656489951383184728464597 343511483235543392073389)
                  ·
                    rfl

theorem cell23_6020876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_6020876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020876 prefixEnd_6020876 := by exact prefixLift 6020876
  have htrace : WordTrace (prefixWord ++ tailWord_6020876) baseStart_6020876 baseEnd_6020876 := by
    simpa [prefixWord, tailWord_6020876, baseEnd_6020876] using wordTrace_append hprefix tailTrace_6020876
  have hstable : (prefixWord ++ tailWord_6020876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020876).length < 2 ^ (prefixWord ++ tailWord_6020876).sum := by decide
  have hdescent : baseEnd_6020876 < baseStart_6020876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020887 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 1, 4, 2]
def baseStart_6020887 : Nat := 118140960795 + 6020887 * 2 ^ 59
def prefixEnd_6020887 : Nat := 4983230072969 + 3 ^ 40 * 6020887 * 2
def baseEnd_6020887 : Nat := 3091608997407089985622951

theorem tailTrace_6020887 : CollatzResearch.WordTrace tailWord_6020887 prefixEnd_6020887 3091608997407089985622951 := by
  unfold tailWord_6020887
  simp only [CollatzResearch.WordTrace]
  refine ⟨219599789738362159478708915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146399859825574772985805943 219599789738362159478708915)
  ·
    refine ⟨329399684607543239218063373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219599789738362159478708915 329399684607543239218063373)
    ·
      refine ⟨123524881727828714706773765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329399684607543239218063373 123524881727828714706773765)
      ·
        refine ⟨23160915323967884007520081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123524881727828714706773765 23160915323967884007520081)
        ·
          refine ⟨17370686492975913005640061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23160915323967884007520081 17370686492975913005640061)
          ·
            refine ⟨6514007434865967377115023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17370686492975913005640061 6514007434865967377115023)
            ·
              refine ⟨9771011152298951065672535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514007434865967377115023 9771011152298951065672535)
              ·
                refine ⟨14656516728448426598508803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9771011152298951065672535 14656516728448426598508803)
                ·
                  refine ⟨21984775092672639897763205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14656516728448426598508803 21984775092672639897763205)
                  ·
                    refine ⟨4122145329876119980830601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21984775092672639897763205 4122145329876119980830601)
                    ·
                      refine ⟨3091608997407089985622951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122145329876119980830601 3091608997407089985622951)
                      ·
                        rfl

theorem cell23_6020887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_6020887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020887 prefixEnd_6020887 := by exact prefixLift 6020887
  have htrace : WordTrace (prefixWord ++ tailWord_6020887) baseStart_6020887 baseEnd_6020887 := by
    simpa [prefixWord, tailWord_6020887, baseEnd_6020887] using wordTrace_append hprefix tailTrace_6020887
  have hstable : (prefixWord ++ tailWord_6020887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020887).length < 2 ^ (prefixWord ++ tailWord_6020887).sum := by decide
  have hdescent : baseEnd_6020887 < baseStart_6020887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020927 : List Nat := [1, 1, 2, 2, 6, 1, 3, 2, 5]
def baseStart_6020927 : Nat := 118140960795 + 6020927 * 2 ^ 59
def prefixEnd_6020927 : Nat := 4983230072969 + 3 ^ 40 * 6020927 * 2
def baseEnd_6020927 : Nat := 343514392959252203235863

theorem tailTrace_6020927 : CollatzResearch.WordTrace tailWord_6020927 prefixEnd_6020927 343514392959252203235863 := by
  unfold tailWord_6020927
  simp only [CollatzResearch.WordTrace]
  refine ⟨219601248658217246310165035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146400832438811497540110023 219601248658217246310165035)
  ·
    refine ⟨329401872987325869465247553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219601248658217246310165035 329401872987325869465247553)
    ·
      refine ⟨247051404740494402098935665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329401872987325869465247553 247051404740494402098935665)
      ·
        refine ⟨185288553555370801574201749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247051404740494402098935665 185288553555370801574201749)
        ·
          refine ⟨8685400947908006323790707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185288553555370801574201749 8685400947908006323790707)
          ·
            refine ⟨13028101421862009485686061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8685400947908006323790707 13028101421862009485686061)
            ·
              refine ⟨4885538033198253557132273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13028101421862009485686061 4885538033198253557132273)
              ·
                refine ⟨3664153524898690167849205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4885538033198253557132273 3664153524898690167849205)
                ·
                  refine ⟨343514392959252203235863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3664153524898690167849205 343514392959252203235863)
                  ·
                    rfl

theorem cell23_6020927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 5].length) (baseStart_6020927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020927 prefixEnd_6020927 := by exact prefixLift 6020927
  have htrace : WordTrace (prefixWord ++ tailWord_6020927) baseStart_6020927 baseEnd_6020927 := by
    simpa [prefixWord, tailWord_6020927, baseEnd_6020927] using wordTrace_append hprefix tailTrace_6020927
  have hstable : (prefixWord ++ tailWord_6020927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020927).length < 2 ^ (prefixWord ++ tailWord_6020927).sum := by decide
  have hdescent : baseEnd_6020927 < baseStart_6020927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020953 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 5, 4]
def baseStart_6020953 : Nat := 118140960795 + 6020953 * 2 ^ 59
def prefixEnd_6020953 : Nat := 4983230072969 + 3 ^ 40 * 6020953 * 2
def baseEnd_6020953 : Nat := 1030547629043428909132549

theorem tailTrace_6020953 : CollatzResearch.WordTrace tailWord_6020953 prefixEnd_6020953 1030547629043428909132549 := by
  unfold tailWord_6020953
  simp only [CollatzResearch.WordTrace]
  refine ⟨219602196956123052750611513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146401464637415368500407675 219602196956123052750611513)
  ·
    refine ⟨164701647717092289562958635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219602196956123052750611513 164701647717092289562958635)
    ·
      refine ⟨247052471575638434344437953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164701647717092289562958635 247052471575638434344437953)
      ·
        refine ⟨185289353681728825758328465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247052471575638434344437953 185289353681728825758328465)
        ·
          refine ⟨138967015261296619318746349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185289353681728825758328465 138967015261296619318746349)
          ·
            refine ⟨52112630722986232244529881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138967015261296619318746349 52112630722986232244529881)
            ·
              refine ⟨39084473042239674183397411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52112630722986232244529881 39084473042239674183397411)
              ·
                refine ⟨58626709563359511275096117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39084473042239674183397411 58626709563359511275096117)
                ·
                  refine ⟨5496254021564954182040261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58626709563359511275096117 5496254021564954182040261)
                  ·
                    refine ⟨1030547629043428909132549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5496254021564954182040261 1030547629043428909132549)
                    ·
                      rfl

theorem cell23_6020953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 4].length) (baseStart_6020953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020953 prefixEnd_6020953 := by exact prefixLift 6020953
  have htrace : WordTrace (prefixWord ++ tailWord_6020953) baseStart_6020953 baseEnd_6020953 := by
    simpa [prefixWord, tailWord_6020953, baseEnd_6020953] using wordTrace_append hprefix tailTrace_6020953
  have hstable : (prefixWord ++ tailWord_6020953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020953).length < 2 ^ (prefixWord ++ tailWord_6020953).sum := by decide
  have hdescent : baseEnd_6020953 < baseStart_6020953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020960 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 4]
def baseStart_6020960 : Nat := 118140960795 + 6020960 * 2 ^ 59
def prefixEnd_6020960 : Nat := 4983230072969 + 3 ^ 40 * 6020960 * 2
def baseEnd_6020960 : Nat := 3091646481494868200010115

theorem tailTrace_6020960 : CollatzResearch.WordTrace tailWord_6020960 prefixEnd_6020960 3091646481494868200010115 := by
  unfold tailWord_6020960
  simp only [CollatzResearch.WordTrace]
  refine ⟨109801226133548846473058167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146401634844731795297410889 109801226133548846473058167)
  ·
    refine ⟨164701839200323269709587251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109801226133548846473058167 164701839200323269709587251)
    ·
      refine ⟨247052758800484904564380877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164701839200323269709587251 247052758800484904564380877)
      ·
        refine ⟨92644784550181839211642829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247052758800484904564380877 92644784550181839211642829)
        ·
          refine ⟨34741794206318189704366061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92644784550181839211642829 34741794206318189704366061)
          ·
            refine ⟨13028172827369321139137273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34741794206318189704366061 13028172827369321139137273)
            ·
              refine ⟨9771129620526990854352955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13028172827369321139137273 9771129620526990854352955)
              ·
                refine ⟨14656694430790486281529433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9771129620526990854352955 14656694430790486281529433)
                ·
                  refine ⟨10992520823092864711147075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14656694430790486281529433 10992520823092864711147075)
                  ·
                    refine ⟨16488781234639297066720613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10992520823092864711147075 16488781234639297066720613)
                    ·
                      refine ⟨3091646481494868200010115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16488781234639297066720613 3091646481494868200010115)
                      ·
                        rfl

theorem cell23_6020960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_6020960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020960 prefixEnd_6020960 := by exact prefixLift 6020960
  have htrace : WordTrace (prefixWord ++ tailWord_6020960) baseStart_6020960 baseEnd_6020960 := by
    simpa [prefixWord, tailWord_6020960, baseEnd_6020960] using wordTrace_append hprefix tailTrace_6020960
  have hstable : (prefixWord ++ tailWord_6020960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020960).length < 2 ^ (prefixWord ++ tailWord_6020960).sum := by decide
  have hdescent : baseEnd_6020960 < baseStart_6020960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021013 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_6021013 : Nat := 118140960795 + 6021013 * 2 ^ 59
def prefixEnd_6021013 : Nat := 4983230072969 + 3 ^ 40 * 6021013 * 2
def baseEnd_6021013 : Nat := 1030557898656518830882457

theorem tailTrace_6021013 : CollatzResearch.WordTrace tailWord_6021013 prefixEnd_6021013 1030557898656518830882457 := by
  unfold tailWord_6021013
  simp only [CollatzResearch.WordTrace]
  refine ⟨219604385335905682997795693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146402923557270455331863795 219604385335905682997795693)
  ·
    refine ⟨82351644500964631124173385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219604385335905682997795693 82351644500964631124173385)
    ·
      refine ⟨61763733375723473343130039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82351644500964631124173385 61763733375723473343130039)
      ·
        refine ⟨92645600063585210014695059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61763733375723473343130039 92645600063585210014695059)
        ·
          refine ⟨138968400095377815022042589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92645600063585210014695059 138968400095377815022042589)
          ·
            refine ⟨52113150035766680633265971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138968400095377815022042589 52113150035766680633265971)
            ·
              refine ⟨78169725053650020949898957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52113150035766680633265971 78169725053650020949898957)
              ·
                refine ⟨29313646895118757856212109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78169725053650020949898957 29313646895118757856212109)
                ·
                  refine ⟨10992617585669534196079541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29313646895118757856212109 10992617585669534196079541)
                  ·
                    refine ⟨1030557898656518830882457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10992617585669534196079541 1030557898656518830882457)
                    ·
                      rfl

theorem cell23_6021013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_6021013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021013 prefixEnd_6021013 := by exact prefixLift 6021013
  have htrace : WordTrace (prefixWord ++ tailWord_6021013) baseStart_6021013 baseEnd_6021013 := by
    simpa [prefixWord, tailWord_6021013, baseEnd_6021013] using wordTrace_append hprefix tailTrace_6021013
  have hstable : (prefixWord ++ tailWord_6021013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021013).length < 2 ^ (prefixWord ++ tailWord_6021013).sum := by decide
  have hdescent : baseEnd_6021013 < baseStart_6021013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021033 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 4]
def baseStart_6021033 : Nat := 118140960795 + 6021033 * 2 ^ 59
def prefixEnd_6021033 : Nat := 4983230072969 + 3 ^ 40 * 6021033 * 2
def baseEnd_6021033 : Nat := 3091683965582646414397279

theorem tailTrace_6021033 : CollatzResearch.WordTrace tailWord_6021033 prefixEnd_6021033 3091683965582646414397279 := by
  unfold tailWord_6021033
  simp only [CollatzResearch.WordTrace]
  refine ⟨219605114795833226413523753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146403409863888817609015835 219605114795833226413523753)
  ·
    refine ⟨164703836096874919810142815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219605114795833226413523753 164703836096874919810142815)
    ·
      refine ⟨247055754145312379715214223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164703836096874919810142815 247055754145312379715214223)
      ·
        refine ⟨370583631217968569572821335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247055754145312379715214223 370583631217968569572821335)
        ·
          refine ⟨555875446826952854359232003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370583631217968569572821335 555875446826952854359232003)
          ·
            refine ⟨833813170240429281538848005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555875446826952854359232003 833813170240429281538848005)
            ·
              refine ⟨156339969420080490288534001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 833813170240429281538848005 156339969420080490288534001)
              ·
                refine ⟨117254977065060367716400501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156339969420080490288534001 117254977065060367716400501)
                ·
                  refine ⟨10992654099849409473412547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117254977065060367716400501 10992654099849409473412547)
                  ·
                    refine ⟨16488981149774114210118821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10992654099849409473412547 16488981149774114210118821)
                    ·
                      refine ⟨3091683965582646414397279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16488981149774114210118821 3091683965582646414397279)
                      ·
                        rfl

theorem cell23_6021033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_6021033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021033 prefixEnd_6021033 := by exact prefixLift 6021033
  have htrace : WordTrace (prefixWord ++ tailWord_6021033) baseStart_6021033 baseEnd_6021033 := by
    simpa [prefixWord, tailWord_6021033, baseEnd_6021033] using wordTrace_append hprefix tailTrace_6021033
  have hstable : (prefixWord ++ tailWord_6021033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021033).length < 2 ^ (prefixWord ++ tailWord_6021033).sum := by decide
  have hdescent : baseEnd_6021033 < baseStart_6021033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021067 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 3, 2, 2]
def baseStart_6021067 : Nat := 118140960795 + 6021067 * 2 ^ 59
def prefixEnd_6021067 : Nat := 4983230072969 + 3 ^ 40 * 6021067 * 2
def baseEnd_6021067 : Nat := 3091701423924899281372123

theorem tailTrace_6021067 : CollatzResearch.WordTrace tailWord_6021067 prefixEnd_6021067 3091701423924899281372123 := by
  unfold tailWord_6021067
  simp only [CollatzResearch.WordTrace]
  refine ⟨219606354877710050220261455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146404236585140033480174303 219606354877710050220261455)
  ·
    refine ⟨329409532316565075330392183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219606354877710050220261455 329409532316565075330392183)
    ·
      refine ⟨494114298474847612995588275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329409532316565075330392183 494114298474847612995588275)
      ·
        refine ⟨741171447712271419493382413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494114298474847612995588275 741171447712271419493382413)
        ·
          refine ⟨277939292892101782310018405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 741171447712271419493382413 277939292892101782310018405)
          ·
            refine ⟨52113617417269084183128451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277939292892101782310018405 52113617417269084183128451)
            ·
              refine ⟨78170426125903626274692677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52113617417269084183128451 78170426125903626274692677)
              ·
                refine ⟨14656954898606929926504877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78170426125903626274692677 14656954898606929926504877)
                ·
                  refine ⟨5496358086977598722439329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14656954898606929926504877 5496358086977598722439329)
                  ·
                    refine ⟨4122268565233199041829497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5496358086977598722439329 4122268565233199041829497)
                    ·
                      refine ⟨3091701423924899281372123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122268565233199041829497 3091701423924899281372123)
                      ·
                        rfl

theorem cell23_6021067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 2, 2].length) (baseStart_6021067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021067 prefixEnd_6021067 := by exact prefixLift 6021067
  have htrace : WordTrace (prefixWord ++ tailWord_6021067) baseStart_6021067 baseEnd_6021067 := by
    simpa [prefixWord, tailWord_6021067, baseEnd_6021067] using wordTrace_append hprefix tailTrace_6021067
  have hstable : (prefixWord ++ tailWord_6021067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021067).length < 2 ^ (prefixWord ++ tailWord_6021067).sum := by decide
  have hdescent : baseEnd_6021067 < baseStart_6021067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021087 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 1, 2, 3]
def baseStart_6021087 : Nat := 118140960795 + 6021087 * 2 ^ 59
def prefixEnd_6021087 : Nat := 4983230072969 + 3 ^ 40 * 6021087 * 2
def baseEnd_6021087 : Nat := 3091711693537989203122031

theorem tailTrace_6021087 : CollatzResearch.WordTrace tailWord_6021087 prefixEnd_6021087 3091711693537989203122031 := by
  unfold tailWord_6021087
  simp only [CollatzResearch.WordTrace]
  refine ⟨219607084337637593635989515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146404722891758395757326343 219607084337637593635989515)
  ·
    refine ⟨329410626506456390453984273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219607084337637593635989515 329410626506456390453984273)
    ·
      refine ⟨247057969879842292840488205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329410626506456390453984273 247057969879842292840488205)
      ·
        refine ⟨92646738704940859815183077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247057969879842292840488205 92646738704940859815183077)
        ·
          refine ⟨17371263507176411215346827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92646738704940859815183077 17371263507176411215346827)
          ·
            refine ⟨26056895260764616823020241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17371263507176411215346827 26056895260764616823020241)
            ·
              refine ⟨19542671445573462617265181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26056895260764616823020241 19542671445573462617265181)
              ·
                refine ⟨7328501792090048481474443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19542671445573462617265181 7328501792090048481474443)
                ·
                  refine ⟨10992752688135072722211665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7328501792090048481474443 10992752688135072722211665)
                  ·
                    refine ⟨8244564516101304541658749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10992752688135072722211665 8244564516101304541658749)
                    ·
                      refine ⟨3091711693537989203122031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8244564516101304541658749 3091711693537989203122031)
                      ·
                        rfl

theorem cell23_6021087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_6021087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021087 prefixEnd_6021087 := by exact prefixLift 6021087
  have htrace : WordTrace (prefixWord ++ tailWord_6021087) baseStart_6021087 baseEnd_6021087 := by
    simpa [prefixWord, tailWord_6021087, baseEnd_6021087] using wordTrace_append hprefix tailTrace_6021087
  have hstable : (prefixWord ++ tailWord_6021087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021087).length < 2 ^ (prefixWord ++ tailWord_6021087).sum := by decide
  have hdescent : baseEnd_6021087 < baseStart_6021087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021103 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 2, 7]
def baseStart_6021103 : Nat := 118140960795 + 6021103 * 2 ^ 59
def prefixEnd_6021103 : Nat := 4983230072969 + 3 ^ 40 * 6021103 * 2
def baseEnd_6021103 : Nat := 1030573303076153713507319

theorem tailTrace_6021103 : CollatzResearch.WordTrace tailWord_6021103 prefixEnd_6021103 1030573303076153713507319 := by
  unfold tailWord_6021103
  simp only [CollatzResearch.WordTrace]
  refine ⟨219607667905579628368571963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146405111937053085579047975 219607667905579628368571963)
  ·
    refine ⟨329411501858369442552857945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219607667905579628368571963 329411501858369442552857945)
    ·
      refine ⟨247058626393777081914643459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329411501858369442552857945 247058626393777081914643459)
      ·
        refine ⟨370587939590665622871965189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247058626393777081914643459 370587939590665622871965189)
        ·
          refine ⟨69485238673249804288493473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370587939590665622871965189 69485238673249804288493473)
          ·
            refine ⟨52113929004937353216370105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69485238673249804288493473 52113929004937353216370105)
            ·
              refine ⟨39085446753703014912277579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52113929004937353216370105 39085446753703014912277579)
              ·
                refine ⟨58628170130554522368416369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39085446753703014912277579 58628170130554522368416369)
                ·
                  refine ⟨43971127597915891776312277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58628170130554522368416369 43971127597915891776312277)
                  ·
                    refine ⟨1030573303076153713507319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43971127597915891776312277 1030573303076153713507319)
                    ·
                      rfl

theorem cell23_6021103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_6021103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021103 prefixEnd_6021103 := by exact prefixLift 6021103
  have htrace : WordTrace (prefixWord ++ tailWord_6021103) baseStart_6021103 baseEnd_6021103 := by
    simpa [prefixWord, tailWord_6021103, baseEnd_6021103] using wordTrace_append hprefix tailTrace_6021103
  have hstable : (prefixWord ++ tailWord_6021103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021103).length < 2 ^ (prefixWord ++ tailWord_6021103).sum := by decide
  have hdescent : baseEnd_6021103 < baseStart_6021103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021170 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_6021170 : Nat := 118140960795 + 6021170 * 2 ^ 59
def prefixEnd_6021170 : Nat := 4983230072969 + 3 ^ 40 * 6021170 * 2
def baseEnd_6021170 : Nat := 3091754312432312378384149

theorem tailTrace_6021170 : CollatzResearch.WordTrace tailWord_6021170 prefixEnd_6021170 3091754312432312378384149 := by
  unfold tailWord_6021170
  simp only [CollatzResearch.WordTrace]
  refine ⟨54902527899084224702815241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146406741064224599207507309 54902527899084224702815241)
  ·
    refine ⟨41176895924313168527111431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54902527899084224702815241 41176895924313168527111431)
    ·
      refine ⟨61765343886469752790667147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41176895924313168527111431 61765343886469752790667147)
      ·
        refine ⟨92648015829704629186000721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61765343886469752790667147 92648015829704629186000721)
        ·
          refine ⟨69486011872278471889500541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92648015829704629186000721 69486011872278471889500541)
          ·
            refine ⟨26057254452104426958562703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69486011872278471889500541 26057254452104426958562703)
            ·
              refine ⟨39085881678156640437844055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26057254452104426958562703 39085881678156640437844055)
              ·
                refine ⟨58628822517234960656766083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39085881678156640437844055 58628822517234960656766083)
                ·
                  refine ⟨87943233775852440985149125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58628822517234960656766083 87943233775852440985149125)
                  ·
                    refine ⟨16489356332972332684715461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87943233775852440985149125 16489356332972332684715461)
                    ·
                      refine ⟨3091754312432312378384149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16489356332972332684715461 3091754312432312378384149)
                      ·
                        rfl

theorem cell23_6021170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_6021170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021170 prefixEnd_6021170 := by exact prefixLift 6021170
  have htrace : WordTrace (prefixWord ++ tailWord_6021170) baseStart_6021170 baseEnd_6021170 := by
    simpa [prefixWord, tailWord_6021170, baseEnd_6021170] using wordTrace_append hprefix tailTrace_6021170
  have hstable : (prefixWord ++ tailWord_6021170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021170).length < 2 ^ (prefixWord ++ tailWord_6021170).sum := by decide
  have hdescent : baseEnd_6021170 < baseStart_6021170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021180 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 7]
def baseStart_6021180 : Nat := 118140960795 + 6021180 * 2 ^ 59
def prefixEnd_6021180 : Nat := 4983230072969 + 3 ^ 40 * 6021180 * 2
def baseEnd_6021180 : Nat := 343528827470984148806567

theorem tailTrace_6021180 : CollatzResearch.WordTrace tailWord_6021180 prefixEnd_6021180 343528827470984148806567 := by
  unfold tailWord_6021180
  simp only [CollatzResearch.WordTrace]
  refine ⟨109805238163150335259562497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146406984217533780346083329 109805238163150335259562497)
  ·
    refine ⟨82353928622362751444671873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109805238163150335259562497 82353928622362751444671873)
    ·
      refine ⟨61765446466772063583503905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82353928622362751444671873 61765446466772063583503905)
      ·
        refine ⟨46324084850079047687627929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61765446466772063583503905 46324084850079047687627929)
        ·
          refine ⟨34743063637559285765720947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46324084850079047687627929 34743063637559285765720947)
          ·
            refine ⟨52114595456338928648581421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34743063637559285765720947 52114595456338928648581421)
            ·
              refine ⟨19542973296127098243218033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52114595456338928648581421 19542973296127098243218033)
              ·
                refine ⟨14657229972095323682413525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19542973296127098243218033 14657229972095323682413525)
                ·
                  refine ⟨343528827470984148806567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14657229972095323682413525 343528827470984148806567)
                  ·
                    rfl

theorem cell23_6021180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_6021180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021180 prefixEnd_6021180 := by exact prefixLift 6021180
  have htrace : WordTrace (prefixWord ++ tailWord_6021180) baseStart_6021180 baseEnd_6021180 := by
    simpa [prefixWord, tailWord_6021180, baseEnd_6021180] using wordTrace_append hprefix tailTrace_6021180
  have hstable : (prefixWord ++ tailWord_6021180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021180).length < 2 ^ (prefixWord ++ tailWord_6021180).sum := by decide
  have hdescent : baseEnd_6021180 < baseStart_6021180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021210 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_6021210 : Nat := 118140960795 + 6021210 * 2 ^ 59
def prefixEnd_6021210 : Nat := 4983230072969 + 3 ^ 40 * 6021210 * 2
def baseEnd_6021210 : Nat := 1030591617219497407294655

theorem tailTrace_6021210 : CollatzResearch.WordTrace tailWord_6021210 prefixEnd_6021210 1030591617219497407294655 := by
  unfold tailWord_6021210
  simp only [CollatzResearch.WordTrace]
  refine ⟨54902892629047996410679271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146407713677461323761811389 54902892629047996410679271)
  ·
    refine ⟨82354338943571994616018907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54902892629047996410679271 82354338943571994616018907)
    ·
      refine ⟨123531508415357991924028361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82354338943571994616018907 123531508415357991924028361)
      ·
        refine ⟨92648631311518493943021271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123531508415357991924028361 92648631311518493943021271)
        ·
          refine ⟨138972946967277740914531907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92648631311518493943021271 138972946967277740914531907)
          ·
            refine ⟨208459420450916611371797861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138972946967277740914531907 208459420450916611371797861)
            ·
              refine ⟨39086141334546864632212099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208459420450916611371797861 39086141334546864632212099)
              ·
                refine ⟨58629212001820296948318149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39086141334546864632212099 58629212001820296948318149)
                ·
                  refine ⟨10992977250341305677809653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58629212001820296948318149 10992977250341305677809653)
                  ·
                    refine ⟨1030591617219497407294655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10992977250341305677809653 1030591617219497407294655)
                    ·
                      rfl

theorem cell23_6021210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_6021210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021210 prefixEnd_6021210 := by exact prefixLift 6021210
  have htrace : WordTrace (prefixWord ++ tailWord_6021210) baseStart_6021210 baseEnd_6021210 := by
    simpa [prefixWord, tailWord_6021210, baseEnd_6021210] using wordTrace_append hprefix tailTrace_6021210
  have hstable : (prefixWord ++ tailWord_6021210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021210).length < 2 ^ (prefixWord ++ tailWord_6021210).sum := by decide
  have hdescent : baseEnd_6021210 < baseStart_6021210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021220 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_6021220 : Nat := 118140960795 + 6021220 * 2 ^ 59
def prefixEnd_6021220 : Nat := 4983230072969 + 3 ^ 40 * 6021220 * 2
def baseEnd_6021220 : Nat := 3091779986465037182758919

theorem tailTrace_6021220 : CollatzResearch.WordTrace tailWord_6021220 prefixEnd_6021220 3091779986465037182758919 := by
  unfold tailWord_6021220
  simp only [CollatzResearch.WordTrace]
  refine ⟨109805967623077878675290557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146407956830770504900387409 109805967623077878675290557)
  ·
    refine ⟨41177237858654204503233959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109805967623077878675290557 41177237858654204503233959)
    ·
      refine ⟨61765856787981306754850939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41177237858654204503233959 61765856787981306754850939)
      ·
        refine ⟨92648785181971960132276409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61765856787981306754850939 92648785181971960132276409)
        ·
          refine ⟨69486588886478970099207307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92648785181971960132276409 69486588886478970099207307)
          ·
            refine ⟨104229883329718455148810961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69486588886478970099207307 104229883329718455148810961)
            ·
              refine ⟨78172412497288841361608221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104229883329718455148810961 78172412497288841361608221)
              ·
                refine ⟨29314654686483315510603083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78172412497288841361608221 29314654686483315510603083)
                ·
                  refine ⟨43971982029724973265904625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29314654686483315510603083 43971982029724973265904625)
                  ·
                    refine ⟨32978986522293729949428469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43971982029724973265904625 32978986522293729949428469)
                    ·
                      refine ⟨3091779986465037182758919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32978986522293729949428469 3091779986465037182758919)
                      ·
                        rfl

theorem cell23_6021220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_6021220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021220 prefixEnd_6021220 := by exact prefixLift 6021220
  have htrace : WordTrace (prefixWord ++ tailWord_6021220) baseStart_6021220 baseEnd_6021220 := by
    simpa [prefixWord, tailWord_6021220, baseEnd_6021220] using wordTrace_append hprefix tailTrace_6021220
  have hstable : (prefixWord ++ tailWord_6021220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021220).length < 2 ^ (prefixWord ++ tailWord_6021220).sum := by decide
  have hdescent : baseEnd_6021220 < baseStart_6021220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021317 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_6021317 : Nat := 118140960795 + 6021317 * 2 ^ 59
def prefixEnd_6021317 : Nat := 4983230072969 + 3 ^ 40 * 6021317 * 2
def baseEnd_6021317 : Nat := 1030609931362841101081991

theorem tailTrace_6021317 : CollatzResearch.WordTrace tailWord_6021317 prefixEnd_6021317 1030609931362841101081991 := by
  unfold tailWord_6021317
  simp only [CollatzResearch.WordTrace]
  refine ⟨219615473126804342916862205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146410315417869561944574803 219615473126804342916862205)
  ·
    refine ⟨82355802422551628593823327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219615473126804342916862205 82355802422551628593823327)
    ·
      refine ⟨123533703633827442890734991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82355802422551628593823327 123533703633827442890734991)
      ·
        refine ⟨185300555450741164336102487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123533703633827442890734991 185300555450741164336102487)
        ·
          refine ⟨277950833176111746504153731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185300555450741164336102487 277950833176111746504153731)
          ·
            refine ⟨416926249764167619756230597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277950833176111746504153731 416926249764167619756230597)
            ·
              refine ⟨78173671830781428704293237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 416926249764167619756230597 78173671830781428704293237)
              ·
                refine ⟨7328781734135758941027491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78173671830781428704293237 7328781734135758941027491)
                ·
                  refine ⟨10993172601203638411541237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7328781734135758941027491 10993172601203638411541237)
                  ·
                    refine ⟨1030609931362841101081991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10993172601203638411541237 1030609931362841101081991)
                    ·
                      rfl

theorem cell23_6021317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_6021317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021317 prefixEnd_6021317 := by exact prefixLift 6021317
  have htrace : WordTrace (prefixWord ++ tailWord_6021317) baseStart_6021317 baseEnd_6021317 := by
    simpa [prefixWord, tailWord_6021317, baseEnd_6021317] using wordTrace_append hprefix tailTrace_6021317
  have hstable : (prefixWord ++ tailWord_6021317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021317).length < 2 ^ (prefixWord ++ tailWord_6021317).sum := by decide
  have hdescent : baseEnd_6021317 < baseStart_6021317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021337 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 4]
def baseStart_6021337 : Nat := 118140960795 + 6021337 * 2 ^ 59
def prefixEnd_6021337 : Nat := 4983230072969 + 3 ^ 40 * 6021337 * 2
def baseEnd_6021337 : Nat := 3091840063701613224995881

theorem tailTrace_6021337 : CollatzResearch.WordTrace tailWord_6021337 prefixEnd_6021337 3091840063701613224995881 := by
  unfold tailWord_6021337
  simp only [CollatzResearch.WordTrace]
  refine ⟨219616202586731886332590265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146410801724487924221726843 219616202586731886332590265)
  ·
    refine ⟨164712151940048914749442699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219616202586731886332590265 164712151940048914749442699)
    ·
      refine ⟨247068227910073372124164049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164712151940048914749442699 247068227910073372124164049)
      ·
        refine ⟨185301170932555029093123037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247068227910073372124164049 185301170932555029093123037)
        ·
          refine ⟨69487939099708135909921139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185301170932555029093123037 69487939099708135909921139)
          ·
            refine ⟨104231908649562203864881709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69487939099708135909921139 104231908649562203864881709)
            ·
              refine ⟨39086965743585826449330641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104231908649562203864881709 39086965743585826449330641)
              ·
                refine ⟨29315224307689369836997981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39086965743585826449330641 29315224307689369836997981)
                ·
                  refine ⟨10993209115383513688874243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29315224307689369836997981 10993209115383513688874243)
                  ·
                    refine ⟨16489813673075270533311365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10993209115383513688874243 16489813673075270533311365)
                    ·
                      refine ⟨3091840063701613224995881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16489813673075270533311365 3091840063701613224995881)
                      ·
                        rfl

theorem cell23_6021337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_6021337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021337 prefixEnd_6021337 := by exact prefixLift 6021337
  have htrace : WordTrace (prefixWord ++ tailWord_6021337) baseStart_6021337 baseEnd_6021337 := by
    simpa [prefixWord, tailWord_6021337, baseEnd_6021337] using wordTrace_append hprefix tailTrace_6021337
  have hstable : (prefixWord ++ tailWord_6021337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021337).length < 2 ^ (prefixWord ++ tailWord_6021337).sum := by decide
  have hdescent : baseEnd_6021337 < baseStart_6021337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021354 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_6021354 : Nat := 118140960795 + 6021354 * 2 ^ 59
def prefixEnd_6021354 : Nat := 4983230072969 + 3 ^ 40 * 6021354 * 2
def baseEnd_6021354 : Nat := 3091848792872739658483303

theorem tailTrace_6021354 : CollatzResearch.WordTrace tailWord_6021354 prefixEnd_6021354 3091848792872739658483303 := by
  unfold tailWord_6021354
  simp only [CollatzResearch.WordTrace]
  refine ⟨54904205656917574558989779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146411215085113532157306077 54904205656917574558989779)
  ·
    refine ⟨82356308485376361838484669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54904205656917574558989779 82356308485376361838484669)
    ·
      refine ⟨30883615682016135689431751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82356308485376361838484669 30883615682016135689431751)
      ·
        refine ⟨46325423523024203534147627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30883615682016135689431751 46325423523024203534147627)
        ·
          refine ⟨69488135284536305301221441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46325423523024203534147627 69488135284536305301221441)
          ·
            refine ⟨52116101463402228975916081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69488135284536305301221441 52116101463402228975916081)
            ·
              refine ⟨39087076097551671731937061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52116101463402228975916081 39087076097551671731937061)
              ·
                refine ⟨7328826768290938449738199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39087076097551671731937061 7328826768290938449738199)
                ·
                  refine ⟨10993240152436407674607299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7328826768290938449738199 10993240152436407674607299)
                  ·
                    refine ⟨16489860228654611511910949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10993240152436407674607299 16489860228654611511910949)
                    ·
                      refine ⟨3091848792872739658483303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16489860228654611511910949 3091848792872739658483303)
                      ·
                        rfl

theorem cell23_6021354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_6021354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021354 prefixEnd_6021354 := by exact prefixLift 6021354
  have htrace : WordTrace (prefixWord ++ tailWord_6021354) baseStart_6021354 baseEnd_6021354 := by
    simpa [prefixWord, tailWord_6021354, baseEnd_6021354] using wordTrace_append hprefix tailTrace_6021354
  have hstable : (prefixWord ++ tailWord_6021354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021354).length < 2 ^ (prefixWord ++ tailWord_6021354).sum := by decide
  have hdescent : baseEnd_6021354 < baseStart_6021354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021360 : List Nat := [2, 1, 1, 1, 3, 1, 1, 13]
def baseStart_6021360 : Nat := 118140960795 + 6021360 * 2 ^ 59
def prefixEnd_6021360 : Nat := 4983230072969 + 3 ^ 40 * 6021360 * 2
def baseEnd_6021360 : Nat := 114513032361358023518825

theorem tailTrace_6021360 : CollatzResearch.WordTrace tailWord_6021360 prefixEnd_6021360 114513032361358023518825 := by
  unfold tailWord_6021360
  simp only [CollatzResearch.WordTrace]
  refine ⟨109808520732824280630338767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146411360977099040840451689 109808520732824280630338767)
  ·
    refine ⟨164712781099236420945508151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109808520732824280630338767 164712781099236420945508151)
    ·
      refine ⟨247069171648854631418262227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164712781099236420945508151 247069171648854631418262227)
      ·
        refine ⟨370603757473281947127393341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247069171648854631418262227 370603757473281947127393341)
        ·
          refine ⟨138976409052480730172772503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370603757473281947127393341 138976409052480730172772503)
          ·
            refine ⟨208464613578721095259158755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138976409052480730172772503 208464613578721095259158755)
            ·
              refine ⟨312696920368081642888738133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208464613578721095259158755 312696920368081642888738133)
              ·
                refine ⟨114513032361358023518825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 312696920368081642888738133 114513032361358023518825)
                ·
                  rfl

theorem cell23_6021360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 13].length) (baseStart_6021360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021360 prefixEnd_6021360 := by exact prefixLift 6021360
  have htrace : WordTrace (prefixWord ++ tailWord_6021360) baseStart_6021360 baseEnd_6021360 := by
    simpa [prefixWord, tailWord_6021360, baseEnd_6021360] using wordTrace_append hprefix tailTrace_6021360
  have hstable : (prefixWord ++ tailWord_6021360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021360).length < 2 ^ (prefixWord ++ tailWord_6021360).sum := by decide
  have hdescent : baseEnd_6021360 < baseStart_6021360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021374 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_6021374 : Nat := 118140960795 + 6021374 * 2 ^ 59
def prefixEnd_6021374 : Nat := 4983230072969 + 3 ^ 40 * 6021374 * 2
def baseEnd_6021374 : Nat := 3091859062485829580233211

theorem tailTrace_6021374 : CollatzResearch.WordTrace tailWord_6021374 prefixEnd_6021374 3091859062485829580233211 := by
  unfold tailWord_6021374
  simp only [CollatzResearch.WordTrace]
  refine ⟨27452194010949730206460897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146411701391731894434458117 27452194010949730206460897)
  ·
    refine ⟨20589145508212297654845673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27452194010949730206460897 20589145508212297654845673)
    ·
      refine ⟨15441859131159223241134255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20589145508212297654845673 15441859131159223241134255)
      ·
        refine ⟨23162788696738834861701383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15441859131159223241134255 23162788696738834861701383)
        ·
          refine ⟨34744183045108252292552075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23162788696738834861701383 34744183045108252292552075)
          ·
            refine ⟨52116274567662378438828113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34744183045108252292552075 52116274567662378438828113)
            ·
              refine ⟨39087205925746783829121085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52116274567662378438828113 39087205925746783829121085)
              ·
                refine ⟨14657702222155043935920407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39087205925746783829121085 14657702222155043935920407)
                ·
                  refine ⟨21986553333232565903880611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14657702222155043935920407 21986553333232565903880611)
                  ·
                    refine ⟨32979829999848848855820917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21986553333232565903880611 32979829999848848855820917)
                    ·
                      refine ⟨3091859062485829580233211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32979829999848848855820917 3091859062485829580233211)
                      ·
                        rfl

theorem cell23_6021374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_6021374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021374 prefixEnd_6021374 := by exact prefixLift 6021374
  have htrace : WordTrace (prefixWord ++ tailWord_6021374) baseStart_6021374 baseEnd_6021374 := by
    simpa [prefixWord, tailWord_6021374, baseEnd_6021374] using wordTrace_append hprefix tailTrace_6021374
  have hstable : (prefixWord ++ tailWord_6021374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021374).length < 2 ^ (prefixWord ++ tailWord_6021374).sum := by decide
  have hdescent : baseEnd_6021374 < baseStart_6021374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021388 : List Nat := [2, 2, 1, 2, 2, 2, 1, 6, 1, 2, 2]
def baseStart_6021388 : Nat := 118140960795 + 6021388 * 2 ^ 59
def prefixEnd_6021388 : Nat := 4983230072969 + 3 ^ 40 * 6021388 * 2
def baseEnd_6021388 : Nat := 3091866251214992525458147

theorem tailTrace_6021388 : CollatzResearch.WordTrace tailWord_6021388 prefixEnd_6021388 3091866251214992525458147 := by
  unfold tailWord_6021388
  simp only [CollatzResearch.WordTrace]
  refine ⟨109809031354773561021348409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146412041806364748028464545 109809031354773561021348409)
  ·
    refine ⟨82356773516080170766011307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109809031354773561021348409 82356773516080170766011307)
    ·
      refine ⟨123535160274120256149016961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82356773516080170766011307 123535160274120256149016961)
      ·
        refine ⟨92651370205590192111762721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123535160274120256149016961 92651370205590192111762721)
        ·
          refine ⟨69488527654192644083822041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92651370205590192111762721 69488527654192644083822041)
          ·
            refine ⟨52116395740644483062866531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69488527654192644083822041 52116395740644483062866531)
            ·
              refine ⟨78174593610966724594299797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52116395740644483062866531 78174593610966724594299797)
              ·
                refine ⟨3664434075514065215357803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78174593610966724594299797 3664434075514065215357803)
                ·
                  refine ⟨5496651113271097823036705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664434075514065215357803 5496651113271097823036705)
                  ·
                    refine ⟨4122488334953323367277529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5496651113271097823036705 4122488334953323367277529)
                    ·
                      refine ⟨3091866251214992525458147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122488334953323367277529 3091866251214992525458147)
                      ·
                        rfl

theorem cell23_6021388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_6021388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021388 prefixEnd_6021388 := by exact prefixLift 6021388
  have htrace : WordTrace (prefixWord ++ tailWord_6021388) baseStart_6021388 baseEnd_6021388 := by
    simpa [prefixWord, tailWord_6021388, baseEnd_6021388] using wordTrace_append hprefix tailTrace_6021388
  have hstable : (prefixWord ++ tailWord_6021388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021388).length < 2 ^ (prefixWord ++ tailWord_6021388).sum := by decide
  have hdescent : baseEnd_6021388 < baseStart_6021388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021447 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_6021447 : Nat := 118140960795 + 6021447 * 2 ^ 59
def prefixEnd_6021447 : Nat := 4983230072969 + 3 ^ 40 * 6021447 * 2
def baseEnd_6021447 : Nat := 3091896546573607794620375

theorem tailTrace_6021447 : CollatzResearch.WordTrace tailWord_6021447 prefixEnd_6021447 3091896546573607794620375 := by
  unfold tailWord_6021447
  simp only [CollatzResearch.WordTrace]
  refine ⟨219620214616333375119094595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146413476410888916746063063 219620214616333375119094595)
  ·
    refine ⟨329430321924500062678641893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219620214616333375119094595 329430321924500062678641893)
    ·
      refine ⟨61768185360843761752245355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329430321924500062678641893 61768185360843761752245355)
      ·
        refine ⟨92652278041265642628368033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61768185360843761752245355 92652278041265642628368033)
        ·
          refine ⟨69489208530949231971276025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92652278041265642628368033 69489208530949231971276025)
          ·
            refine ⟨52116906398211923978457019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69489208530949231971276025 52116906398211923978457019)
            ·
              refine ⟨78175359597317885967685529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52116906398211923978457019 78175359597317885967685529)
              ·
                refine ⟨58631519697988414475764147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78175359597317885967685529 58631519697988414475764147)
                ·
                  refine ⟨87947279546982621713646221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58631519697988414475764147 87947279546982621713646221)
                  ·
                    refine ⟨32980229830118483142617333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87947279546982621713646221 32980229830118483142617333)
                    ·
                      refine ⟨3091896546573607794620375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32980229830118483142617333 3091896546573607794620375)
                      ·
                        rfl

theorem cell23_6021447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_6021447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021447 prefixEnd_6021447 := by exact prefixLift 6021447
  have htrace : WordTrace (prefixWord ++ tailWord_6021447) baseStart_6021447 baseEnd_6021447 := by
    simpa [prefixWord, tailWord_6021447, baseEnd_6021447] using wordTrace_append hprefix tailTrace_6021447
  have hstable : (prefixWord ++ tailWord_6021447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021447).length < 2 ^ (prefixWord ++ tailWord_6021447).sum := by decide
  have hdescent : baseEnd_6021447 < baseStart_6021447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021497 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 3, 7]
def baseStart_6021497 : Nat := 118140960795 + 6021497 * 2 ^ 59
def prefixEnd_6021497 : Nat := 4983230072969 + 3 ^ 40 * 6021497 * 2
def baseEnd_6021497 : Nat := 1030640740202110866331715

theorem tailTrace_6021497 : CollatzResearch.WordTrace tailWord_6021497 prefixEnd_6021497 1030640740202110866331715 := by
  unfold tailWord_6021497
  simp only [CollatzResearch.WordTrace]
  refine ⟨219622038266152233658414745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146414692177434822438943163 219622038266152233658414745)
  ·
    refine ⟨164716528699614175243811059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219622038266152233658414745 164716528699614175243811059)
    ·
      refine ⟨247074793049421262865716589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164716528699614175243811059 247074793049421262865716589)
      ·
        refine ⟨92653047393532973574643721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247074793049421262865716589 92653047393532973574643721)
        ·
          refine ⟨69489785545149730180982791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92653047393532973574643721 69489785545149730180982791)
          ·
            refine ⟨104234678317724595271474187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69489785545149730180982791 104234678317724595271474187)
            ·
              refine ⟨156352017476586892907211281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104234678317724595271474187 156352017476586892907211281)
              ·
                refine ⟨117264013107440169680408461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156352017476586892907211281 117264013107440169680408461)
                ·
                  refine ⟨43974004915290063630153173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117264013107440169680408461 43974004915290063630153173)
                  ·
                    refine ⟨1030640740202110866331715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43974004915290063630153173 1030640740202110866331715)
                    ·
                      rfl

theorem cell23_6021497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_6021497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021497 prefixEnd_6021497 := by exact prefixLift 6021497
  have htrace : WordTrace (prefixWord ++ tailWord_6021497) baseStart_6021497 baseEnd_6021497 := by
    simpa [prefixWord, tailWord_6021497, baseEnd_6021497] using wordTrace_append hprefix tailTrace_6021497
  have hstable : (prefixWord ++ tailWord_6021497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021497).length < 2 ^ (prefixWord ++ tailWord_6021497).sum := by decide
  have hdescent : baseEnd_6021497 < baseStart_6021497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021501 : List Nat := [1, 4, 1, 1, 2, 4, 1, 4, 5]
def baseStart_6021501 : Nat := 118140960795 + 6021501 * 2 ^ 59
def prefixEnd_6021501 : Nat := 4983230072969 + 3 ^ 40 * 6021501 * 2
def baseEnd_6021501 : Nat := 343547141614327842593903

theorem tailTrace_6021501 : CollatzResearch.WordTrace tailWord_6021501 prefixEnd_6021501 343547141614327842593903 := by
  unfold tailWord_6021501
  simp only [CollatzResearch.WordTrace]
  refine ⟨219622184158137742341560357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146414789438758494894373571 219622184158137742341560357)
  ·
    refine ⟨41179159529650826689042567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219622184158137742341560357 41179159529650826689042567)
    ·
      refine ⟨61768739294476240033563851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41179159529650826689042567 61768739294476240033563851)
      ·
        refine ⟨92653108941714360050345777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61768739294476240033563851 92653108941714360050345777)
        ·
          refine ⟨69489831706285770037759333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92653108941714360050345777 69489831706285770037759333)
          ·
            refine ⟨13029343444928581882079875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69489831706285770037759333 13029343444928581882079875)
            ·
              refine ⟨19544015167392872823119813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13029343444928581882079875 19544015167392872823119813)
              ·
                refine ⟨3664502843886163654334965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19544015167392872823119813 3664502843886163654334965)
                ·
                  refine ⟨343547141614327842593903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3664502843886163654334965 343547141614327842593903)
                  ·
                    rfl

theorem cell23_6021501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_6021501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021501 prefixEnd_6021501 := by exact prefixLift 6021501
  have htrace : WordTrace (prefixWord ++ tailWord_6021501) baseStart_6021501 baseEnd_6021501 := by
    simpa [prefixWord, tailWord_6021501, baseEnd_6021501] using wordTrace_append hprefix tailTrace_6021501
  have hstable : (prefixWord ++ tailWord_6021501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021501).length < 2 ^ (prefixWord ++ tailWord_6021501).sum := by decide
  have hdescent : baseEnd_6021501 < baseStart_6021501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021546 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6021546 : Nat := 118140960795 + 6021546 * 2 ^ 59
def prefixEnd_6021546 : Nat := 4983230072969 + 3 ^ 40 * 6021546 * 2
def baseEnd_6021546 : Nat := 3091947381158402907282421

theorem tailTrace_6021546 : CollatzResearch.WordTrace tailWord_6021546 prefixEnd_6021546 3091947381158402907282421 := by
  unfold tailWord_6021546
  simp only [CollatzResearch.WordTrace]
  refine ⟨54905956360743678756737123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146415883628649810017965661 54905956360743678756737123)
  ·
    refine ⟨82358934541115518135105685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54905956360743678756737123 82358934541115518135105685)
    ·
      refine ⟨3860575056614789912583079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82358934541115518135105685 3860575056614789912583079)
      ·
        refine ⟨5790862584922184868874619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3860575056614789912583079 5790862584922184868874619)
        ·
          refine ⟨8686293877383277303311929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5790862584922184868874619 8686293877383277303311929)
          ·
            refine ⟨6514720408037457977483947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8686293877383277303311929 6514720408037457977483947)
            ·
              refine ⟨9772080612056186966225921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514720408037457977483947 9772080612056186966225921)
              ·
                refine ⟨7329060459042140224669441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9772080612056186966225921 7329060459042140224669441)
                ·
                  refine ⟨5496795344281605168502081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7329060459042140224669441 5496795344281605168502081)
                  ·
                    refine ⟨4122596508211203876376561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5496795344281605168502081 4122596508211203876376561)
                    ·
                      refine ⟨3091947381158402907282421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122596508211203876376561 3091947381158402907282421)
                      ·
                        rfl

theorem cell23_6021546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6021546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021546 prefixEnd_6021546 := by exact prefixLift 6021546
  have htrace : WordTrace (prefixWord ++ tailWord_6021546) baseStart_6021546 baseEnd_6021546 := by
    simpa [prefixWord, tailWord_6021546, baseEnd_6021546] using wordTrace_append hprefix tailTrace_6021546
  have hstable : (prefixWord ++ tailWord_6021546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021546).length < 2 ^ (prefixWord ++ tailWord_6021546).sum := by decide
  have hdescent : baseEnd_6021546 < baseStart_6021546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021561 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 3, 4]
def baseStart_6021561 : Nat := 118140960795 + 6021561 * 2 ^ 59
def prefixEnd_6021561 : Nat := 4983230072969 + 3 ^ 40 * 6021561 * 2
def baseEnd_6021561 : Nat := 1030651694456073449531617

theorem tailTrace_6021561 : CollatzResearch.WordTrace tailWord_6021561 prefixEnd_6021561 1030651694456073449531617 := by
  unfold tailWord_6021561
  simp only [CollatzResearch.WordTrace]
  refine ⟨219624372537920372588744537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146416248358613581725829691 219624372537920372588744537)
  ·
    refine ⟨164718279403440279441558403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219624372537920372588744537 164718279403440279441558403)
    ·
      refine ⟨247077419105160419162337605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164718279403440279441558403 247077419105160419162337605)
      ·
        refine ⟨46327016082217578592938301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247077419105160419162337605 46327016082217578592938301)
        ·
          refine ⟨17372631030831591972351863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46327016082217578592938301 17372631030831591972351863)
          ·
            refine ⟨26058946546247387958527795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17372631030831591972351863 26058946546247387958527795)
            ·
              refine ⟨39088419819371081937791693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26058946546247387958527795 39088419819371081937791693)
              ·
                refine ⟨14658157432264155726671885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39088419819371081937791693 14658157432264155726671885)
                ·
                  refine ⟨5496809037099058397501957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14658157432264155726671885 5496809037099058397501957)
                  ·
                    refine ⟨1030651694456073449531617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5496809037099058397501957 1030651694456073449531617)
                    ·
                      rfl

theorem cell23_6021561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 4].length) (baseStart_6021561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021561 prefixEnd_6021561 := by exact prefixLift 6021561
  have htrace : WordTrace (prefixWord ++ tailWord_6021561) baseStart_6021561 baseEnd_6021561 := by
    simpa [prefixWord, tailWord_6021561, baseEnd_6021561] using wordTrace_append hprefix tailTrace_6021561
  have hstable : (prefixWord ++ tailWord_6021561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021561).length < 2 ^ (prefixWord ++ tailWord_6021561).sum := by decide
  have hdescent : baseEnd_6021561 < baseStart_6021561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021604 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_6021604 : Nat := 118140960795 + 6021604 * 2 ^ 59
def prefixEnd_6021604 : Nat := 4983230072969 + 3 ^ 40 * 6021604 * 2
def baseEnd_6021604 : Nat := 1030659054345454560119051

theorem tailTrace_6021604 : CollatzResearch.WordTrace tailWord_6021604 prefixEnd_6021604 1030659054345454560119051 := by
  unfold tailWord_6021604
  simp only [CollatzResearch.WordTrace]
  refine ⟨109812970438382295466279933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146417293917843060621706577 109812970438382295466279933)
  ·
    refine ⟨41179863914393360799854975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109812970438382295466279933 41179863914393360799854975)
    ·
      refine ⟨61769795871590041199782463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41179863914393360799854975 61769795871590041199782463)
      ·
        refine ⟨92654693807385061799673695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61769795871590041199782463 92654693807385061799673695)
        ·
          refine ⟨138982040711077592699510543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92654693807385061799673695 138982040711077592699510543)
          ·
            refine ⟨208473061066616389049265815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138982040711077592699510543 208473061066616389049265815)
            ·
              refine ⟨312709591599924583573898723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208473061066616389049265815 312709591599924583573898723)
              ·
                refine ⟨469064387399886875360848085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312709591599924583573898723 469064387399886875360848085)
                ·
                  refine ⟨10993696579684848641269877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 469064387399886875360848085 10993696579684848641269877)
                  ·
                    refine ⟨1030659054345454560119051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10993696579684848641269877 1030659054345454560119051)
                    ·
                      rfl

theorem cell23_6021604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_6021604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021604 prefixEnd_6021604 := by exact prefixLift 6021604
  have htrace : WordTrace (prefixWord ++ tailWord_6021604) baseStart_6021604 baseEnd_6021604 := by
    simpa [prefixWord, tailWord_6021604, baseEnd_6021604] using wordTrace_append hprefix tailTrace_6021604
  have hstable : (prefixWord ++ tailWord_6021604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021604).length < 2 ^ (prefixWord ++ tailWord_6021604).sum := by decide
  have hdescent : baseEnd_6021604 < baseStart_6021604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021641 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 4]
def baseStart_6021641 : Nat := 118140960795 + 6021641 * 2 ^ 59
def prefixEnd_6021641 : Nat := 4983230072969 + 3 ^ 40 * 6021641 * 2
def baseEnd_6021641 : Nat := 3091996161820580035594483

theorem tailTrace_6021641 : CollatzResearch.WordTrace tailWord_6021641 prefixEnd_6021641 3091996161820580035594483 := by
  unfold tailWord_6021641
  simp only [CollatzResearch.WordTrace]
  refine ⟨219627290377630546251656777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146418193585087030834437851 219627290377630546251656777)
  ·
    refine ⟨164720467783222909688742583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219627290377630546251656777 164720467783222909688742583)
    ·
      refine ⟨247080701674834364533113875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164720467783222909688742583 247080701674834364533113875)
      ·
        refine ⟨370621052512251546799670813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247080701674834364533113875 370621052512251546799670813)
        ·
          refine ⟨138982894692094330049876555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370621052512251546799670813 138982894692094330049876555)
          ·
            refine ⟨208474342038141495074814833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138982894692094330049876555 208474342038141495074814833)
            ·
              refine ⟨156355756528606121306111125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208474342038141495074814833 156355756528606121306111125)
              ·
                refine ⟨7329176087278411936223959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156355756528606121306111125 7329176087278411936223959)
                ·
                  refine ⟨10993764130917617904335939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7329176087278411936223959 10993764130917617904335939)
                  ·
                    refine ⟨16490646196376426856503909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10993764130917617904335939 16490646196376426856503909)
                    ·
                      refine ⟨3091996161820580035594483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16490646196376426856503909 3091996161820580035594483)
                      ·
                        rfl

theorem cell23_6021641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 4].length) (baseStart_6021641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021641 prefixEnd_6021641 := by exact prefixLift 6021641
  have htrace : WordTrace (prefixWord ++ tailWord_6021641) baseStart_6021641 baseEnd_6021641 := by
    simpa [prefixWord, tailWord_6021641, baseEnd_6021641] using wordTrace_append hprefix tailTrace_6021641
  have hstable : (prefixWord ++ tailWord_6021641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021641).length < 2 ^ (prefixWord ++ tailWord_6021641).sum := by decide
  have hdescent : baseEnd_6021641 < baseStart_6021641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021664 : List Nat := [2, 1, 1, 6, 13]
def baseStart_6021664 : Nat := 118140960795 + 6021664 * 2 ^ 59
def prefixEnd_6021664 : Nat := 4983230072969 + 3 ^ 40 * 6021664 * 2
def baseEnd_6021664 : Nat := 4241437547154504040613

theorem tailTrace_6021664 : CollatzResearch.WordTrace tailWord_6021664 prefixEnd_6021664 4241437547154504040613 := by
  unfold tailWord_6021664
  simp only [CollatzResearch.WordTrace]
  refine ⟨109814064628273610589872023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146418752837698147453162697 109814064628273610589872023)
  ·
    refine ⟨164721096942410415884808035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109814064628273610589872023 164721096942410415884808035)
    ·
      refine ⟨247081645413615623827212053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164721096942410415884808035 247081645413615623827212053)
      ·
        refine ⟨11581952128763232366900565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 247081645413615623827212053 11581952128763232366900565)
        ·
          refine ⟨4241437547154504040613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11581952128763232366900565 4241437547154504040613)
          ·
            rfl

theorem cell23_6021664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 13].length) (baseStart_6021664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021664 prefixEnd_6021664 := by exact prefixLift 6021664
  have htrace : WordTrace (prefixWord ++ tailWord_6021664) baseStart_6021664 baseEnd_6021664 := by
    simpa [prefixWord, tailWord_6021664, baseEnd_6021664] using wordTrace_append hprefix tailTrace_6021664
  have hstable : (prefixWord ++ tailWord_6021664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021664).length < 2 ^ (prefixWord ++ tailWord_6021664).sum := by decide
  have hdescent : baseEnd_6021664 < baseStart_6021664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021708 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 4, 1, 3]
def baseStart_6021708 : Nat := 118140960795 + 6021708 * 2 ^ 59
def prefixEnd_6021708 : Nat := 4983230072969 + 3 ^ 40 * 6021708 * 2
def baseEnd_6021708 : Nat := 3092030565024431273456675

theorem tailTrace_6021708 : CollatzResearch.WordTrace tailWord_6021708 prefixEnd_6021708 3092030565024431273456675 := by
  unfold tailWord_6021708
  simp only [CollatzResearch.WordTrace]
  refine ⟨109814867034193908347172889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146419822712258544462897185 109814867034193908347172889)
  ·
    refine ⟨82361150275645431260379667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109814867034193908347172889 82361150275645431260379667)
    ·
      refine ⟨123541725413468146890569501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82361150275645431260379667 123541725413468146890569501)
      ·
        refine ⟨46328147030050555083963563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123541725413468146890569501 46328147030050555083963563)
        ·
          refine ⟨69492220545075832625945345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46328147030050555083963563 69492220545075832625945345)
          ·
            refine ⟨52119165408806874469459009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69492220545075832625945345 52119165408806874469459009)
            ·
              refine ⟨39089374056605155852094257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52119165408806874469459009 39089374056605155852094257)
              ·
                refine ⟨29317030542453866889070693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39089374056605155852094257 29317030542453866889070693)
                ·
                  refine ⟨5496943226710100041700755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29317030542453866889070693 5496943226710100041700755)
                  ·
                    refine ⟨8245414840065150062551133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5496943226710100041700755 8245414840065150062551133)
                    ·
                      refine ⟨3092030565024431273456675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8245414840065150062551133 3092030565024431273456675)
                      ·
                        rfl

theorem cell23_6021708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_6021708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021708 prefixEnd_6021708 := by exact prefixLift 6021708
  have htrace : WordTrace (prefixWord ++ tailWord_6021708) baseStart_6021708 baseEnd_6021708 := by
    simpa [prefixWord, tailWord_6021708, baseEnd_6021708] using wordTrace_append hprefix tailTrace_6021708
  have hstable : (prefixWord ++ tailWord_6021708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021708).length < 2 ^ (prefixWord ++ tailWord_6021708).sum := by decide
  have hdescent : baseEnd_6021708 < baseStart_6021708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021709 : List Nat := [1, 6, 1, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_6021709 : Nat := 118140960795 + 6021709 * 2 ^ 59
def prefixEnd_6021709 : Nat := 4983230072969 + 3 ^ 40 * 6021709 * 2
def baseEnd_6021709 : Nat := 3092031078505085769544171

theorem tailTrace_6021709 : CollatzResearch.WordTrace tailWord_6021709 prefixEnd_6021709 3092031078505085769544171 := by
  unfold tailWord_6021709
  simp only [CollatzResearch.WordTrace]
  refine ⟨219629770541384193865132181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146419847027589462576754787 219629770541384193865132181)
  ·
    refine ⟨10295145494127384087428071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 219629770541384193865132181 10295145494127384087428071)
    ·
      refine ⟨15442718241191076131142107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10295145494127384087428071 15442718241191076131142107)
      ·
        refine ⟨23164077361786614196713161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15442718241191076131142107 23164077361786614196713161)
        ·
          refine ⟨17373058021339960647534871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23164077361786614196713161 17373058021339960647534871)
          ·
            refine ⟨26059587032009940971302307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17373058021339960647534871 26059587032009940971302307)
            ·
              refine ⟨39089380548014911456953461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26059587032009940971302307 39089380548014911456953461)
              ·
                refine ⟨3664629426376397949089387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39089380548014911456953461 3664629426376397949089387)
                ·
                  refine ⟨5496944139564596923634081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664629426376397949089387 5496944139564596923634081)
                  ·
                    refine ⟨4122708104673447692725561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5496944139564596923634081 4122708104673447692725561)
                    ·
                      refine ⟨3092031078505085769544171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122708104673447692725561 3092031078505085769544171)
                      ·
                        rfl

theorem cell23_6021709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_6021709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021709 prefixEnd_6021709 := by exact prefixLift 6021709
  have htrace : WordTrace (prefixWord ++ tailWord_6021709) baseStart_6021709 baseEnd_6021709 := by
    simpa [prefixWord, tailWord_6021709, baseEnd_6021709] using wordTrace_append hprefix tailTrace_6021709
  have hstable : (prefixWord ++ tailWord_6021709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021709).length < 2 ^ (prefixWord ++ tailWord_6021709).sum := by decide
  have hdescent : baseEnd_6021709 < baseStart_6021709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021751 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 3]
def baseStart_6021751 : Nat := 118140960795 + 6021751 * 2 ^ 59
def prefixEnd_6021751 : Nat := 4983230072969 + 3 ^ 40 * 6021751 * 2
def baseEnd_6021751 : Nat := 3092052644692574605218977

theorem tailTrace_6021751 : CollatzResearch.WordTrace tailWord_6021751 prefixEnd_6021751 3092052644692574605218977 := by
  unfold tailWord_6021751
  simp only [CollatzResearch.WordTrace]
  refine ⟨219631302407232035038161107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146420868271488023358774071 219631302407232035038161107)
  ·
    refine ⟨329446953610848052557241661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219631302407232035038161107 329446953610848052557241661)
    ·
      refine ⟨123542607604068019708965623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329446953610848052557241661 123542607604068019708965623)
      ·
        refine ⟨185313911406102029563448435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123542607604068019708965623 185313911406102029563448435)
        ·
          refine ⟨277970867109153044345172653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185313911406102029563448435 277970867109153044345172653)
          ·
            refine ⟨104239075165932391629439745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277970867109153044345172653 104239075165932391629439745)
            ·
              refine ⟨78179306374449293722079809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104239075165932391629439745 78179306374449293722079809)
              ·
                refine ⟨58634479780836970291559857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78179306374449293722079809 58634479780836970291559857)
                ·
                  refine ⟨43975859835627727718669893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58634479780836970291559857 43975859835627727718669893)
                  ·
                    refine ⟨8245473719180198947250605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43975859835627727718669893 8245473719180198947250605)
                    ·
                      refine ⟨3092052644692574605218977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8245473719180198947250605 3092052644692574605218977)
                      ·
                        rfl

theorem cell23_6021751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_6021751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021751 prefixEnd_6021751 := by exact prefixLift 6021751
  have htrace : WordTrace (prefixWord ++ tailWord_6021751) baseStart_6021751 baseEnd_6021751 := by
    simpa [prefixWord, tailWord_6021751, baseEnd_6021751] using wordTrace_append hprefix tailTrace_6021751
  have hstable : (prefixWord ++ tailWord_6021751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021751).length < 2 ^ (prefixWord ++ tailWord_6021751).sum := by decide
  have hdescent : baseEnd_6021751 < baseStart_6021751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021765 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 4, 2, 2]
def baseStart_6021765 : Nat := 118140960795 + 6021765 * 2 ^ 59
def prefixEnd_6021765 : Nat := 4983230072969 + 3 ^ 40 * 6021765 * 2
def baseEnd_6021765 : Nat := 3092059833421737550443913

theorem tailTrace_6021765 : CollatzResearch.WordTrace tailWord_6021765 prefixEnd_6021765 3092059833421737550443913 := by
  unfold tailWord_6021765
  simp only [CollatzResearch.WordTrace]
  refine ⟨219631813029181315429170749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146421208686120876952780499 219631813029181315429170749)
  ·
    refine ⟨82361929885942993285939031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219631813029181315429170749 82361929885942993285939031)
    ·
      refine ⟨123542894828914489928908547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82361929885942993285939031 123542894828914489928908547)
      ·
        refine ⟨185314342243371734893362821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123542894828914489928908547 185314342243371734893362821)
        ·
          refine ⟨34746439170632200292505529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185314342243371734893362821 34746439170632200292505529)
          ·
            refine ⟨26059829377974150219379147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34746439170632200292505529 26059829377974150219379147)
            ·
              refine ⟨39089744066961225329068721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26059829377974150219379147 39089744066961225329068721)
              ·
                refine ⟨29317308050220918996801541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39089744066961225329068721 29317308050220918996801541)
                ·
                  refine ⟨5496995259416422311900289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29317308050220918996801541 5496995259416422311900289)
                  ·
                    refine ⟨4122746444562316733925217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5496995259416422311900289 4122746444562316733925217)
                    ·
                      refine ⟨3092059833421737550443913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122746444562316733925217 3092059833421737550443913)
                      ·
                        rfl

theorem cell23_6021765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_6021765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021765 prefixEnd_6021765 := by exact prefixLift 6021765
  have htrace : WordTrace (prefixWord ++ tailWord_6021765) baseStart_6021765 baseEnd_6021765 := by
    simpa [prefixWord, tailWord_6021765, baseEnd_6021765] using wordTrace_append hprefix tailTrace_6021765
  have hstable : (prefixWord ++ tailWord_6021765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021765).length < 2 ^ (prefixWord ++ tailWord_6021765).sum := by decide
  have hdescent : baseEnd_6021765 < baseStart_6021765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021788 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 7]
def baseStart_6021788 : Nat := 118140960795 + 6021788 * 2 ^ 59
def prefixEnd_6021788 : Nat := 4983230072969 + 3 ^ 40 * 6021788 * 2
def baseEnd_6021788 : Nat := 343563515941865662272923

theorem tailTrace_6021788 : CollatzResearch.WordTrace tailWord_6021788 prefixEnd_6021788 343563515941865662272923 := by
  unfold tailWord_6021788
  simp only [CollatzResearch.WordTrace]
  refine ⟨109816325954048995178629009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146421767938731993571505345 109816325954048995178629009)
  ·
    refine ⟨82362244465536746383971757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109816325954048995178629009 82362244465536746383971757)
    ·
      refine ⟨30885841674576279893989409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82362244465536746383971757 30885841674576279893989409)
      ·
        refine ⟨23164381255932209920492057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30885841674576279893989409 23164381255932209920492057)
        ·
          refine ⟨17373285941949157440369043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23164381255932209920492057 17373285941949157440369043)
          ·
            refine ⟨26059928912923736160553565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17373285941949157440369043 26059928912923736160553565)
            ·
              refine ⟨9772473342346401060207587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26059928912923736160553565 9772473342346401060207587)
              ·
                refine ⟨14658710013519601590311381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9772473342346401060207587 14658710013519601590311381)
                ·
                  refine ⟨343563515941865662272923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14658710013519601590311381 343563515941865662272923)
                  ·
                    rfl

theorem cell23_6021788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_6021788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021788 prefixEnd_6021788 := by exact prefixLift 6021788
  have htrace : WordTrace (prefixWord ++ tailWord_6021788) baseStart_6021788 baseEnd_6021788 := by
    simpa [prefixWord, tailWord_6021788, baseEnd_6021788] using wordTrace_append hprefix tailTrace_6021788
  have hstable : (prefixWord ++ tailWord_6021788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021788).length < 2 ^ (prefixWord ++ tailWord_6021788).sum := by decide
  have hdescent : baseEnd_6021788 < baseStart_6021788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021818 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_6021818 : Nat := 118140960795 + 6021818 * 2 ^ 59
def prefixEnd_6021818 : Nat := 4983230072969 + 3 ^ 40 * 6021818 * 2
def baseEnd_6021818 : Nat := 1030695682632141947693723

theorem tailTrace_6021818 : CollatzResearch.WordTrace tailWord_6021818 prefixEnd_6021818 1030695682632141947693723 := by
  unfold tailWord_6021818
  simp only [CollatzResearch.WordTrace]
  refine ⟨54908436524497326370212527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146422497398659536987233405 54908436524497326370212527)
  ·
    refine ⟨82362654786745989555318791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54908436524497326370212527 82362654786745989555318791)
    ·
      refine ⟨123543982180118984332978187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82362654786745989555318791 123543982180118984332978187)
      ·
        refine ⟨185315973270178476499467281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123543982180118984332978187 185315973270178476499467281)
        ·
          refine ⟨138986979952633857374600461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185315973270178476499467281 138986979952633857374600461)
          ·
            refine ⟨52120117482237696515475173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138986979952633857374600461 52120117482237696515475173)
            ·
              refine ⟨9772522027919568096651595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52120117482237696515475173 9772522027919568096651595)
              ·
                refine ⟨14658783041879352144977393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9772522027919568096651595 14658783041879352144977393)
                ·
                  refine ⟨10994087281409514108733045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14658783041879352144977393 10994087281409514108733045)
                  ·
                    refine ⟨1030695682632141947693723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10994087281409514108733045 1030695682632141947693723)
                    ·
                      rfl

theorem cell23_6021818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_6021818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021818 prefixEnd_6021818 := by exact prefixLift 6021818
  have htrace : WordTrace (prefixWord ++ tailWord_6021818) baseStart_6021818 baseEnd_6021818 := by
    simpa [prefixWord, tailWord_6021818, baseEnd_6021818] using wordTrace_append hprefix tailTrace_6021818
  have hstable : (prefixWord ++ tailWord_6021818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021818).length < 2 ^ (prefixWord ++ tailWord_6021818).sum := by decide
  have hdescent : baseEnd_6021818 < baseStart_6021818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021828 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6021828 : Nat := 118140960795 + 6021828 * 2 ^ 59
def prefixEnd_6021828 : Nat := 4983230072969 + 3 ^ 40 * 6021828 * 2
def baseEnd_6021828 : Nat := 3092092182702970803956123

theorem tailTrace_6021828 : CollatzResearch.WordTrace tailWord_6021828 prefixEnd_6021828 3092092182702970803956123 := by
  unfold tailWord_6021828
  simp only [CollatzResearch.WordTrace]
  refine ⟨109817055413976538594357069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146422740551968718125809425 109817055413976538594357069)
  ·
    refine ⟨41181395780241201972883901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109817055413976538594357069 41181395780241201972883901)
    ·
      refine ⟨15443023417590450739831463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41181395780241201972883901 15443023417590450739831463)
      ·
        refine ⟨23164535126385676109747195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15443023417590450739831463 23164535126385676109747195)
        ·
          refine ⟨34746802689578514164620793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23164535126385676109747195 34746802689578514164620793)
          ·
            refine ⟨26060102017183885623465595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34746802689578514164620793 26060102017183885623465595)
            ·
              refine ⟨39090153025775828435198393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26060102017183885623465595 39090153025775828435198393)
              ·
                refine ⟨29317614769331871326398795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39090153025775828435198393 29317614769331871326398795)
                ·
                  refine ⟨43976422153997806989598193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29317614769331871326398795 43976422153997806989598193)
                  ·
                    refine ⟨32982316615498355242198645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43976422153997806989598193 32982316615498355242198645)
                    ·
                      refine ⟨3092092182702970803956123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32982316615498355242198645 3092092182702970803956123)
                      ·
                        rfl

theorem cell23_6021828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6021828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021828 prefixEnd_6021828 := by exact prefixLift 6021828
  have htrace : WordTrace (prefixWord ++ tailWord_6021828) baseStart_6021828 baseEnd_6021828 := by
    simpa [prefixWord, tailWord_6021828, baseEnd_6021828] using wordTrace_append hprefix tailTrace_6021828
  have hstable : (prefixWord ++ tailWord_6021828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021828).length < 2 ^ (prefixWord ++ tailWord_6021828).sum := by decide
  have hdescent : baseEnd_6021828 < baseStart_6021828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021841 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_6021841 : Nat := 118140960795 + 6021841 * 2 ^ 59
def prefixEnd_6021841 : Nat := 4983230072969 + 3 ^ 40 * 6021841 * 2
def baseEnd_6021841 : Nat := 3092098857951479253093563

theorem tailTrace_6021841 : CollatzResearch.WordTrace tailWord_6021841 prefixEnd_6021841 3092098857951479253093563 := by
  unfold tailWord_6021841
  simp only [CollatzResearch.WordTrace]
  refine ⟨219634584976905980408937377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146423056651270653605958251 219634584976905980408937377)
  ·
    refine ⟨164725938732679485306703033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219634584976905980408937377 164725938732679485306703033)
    ·
      refine ⟨123544454049509613980027275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164725938732679485306703033 123544454049509613980027275)
      ·
        refine ⟨185316681074264420970040913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123544454049509613980027275 185316681074264420970040913)
        ·
          refine ⟨138987510805698315727530685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185316681074264420970040913 138987510805698315727530685)
          ·
            refine ⟨52120316552136868397824007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138987510805698315727530685 52120316552136868397824007)
            ·
              refine ⟨78180474828205302596736011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52120316552136868397824007 78180474828205302596736011)
              ·
                refine ⟨117270712242307953895104017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78180474828205302596736011 117270712242307953895104017)
                ·
                  refine ⟨87953034181730965421328013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117270712242307953895104017 87953034181730965421328013)
                  ·
                    refine ⟨32982387818149112032998005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87953034181730965421328013 32982387818149112032998005)
                    ·
                      refine ⟨3092098857951479253093563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32982387818149112032998005 3092098857951479253093563)
                      ·
                        rfl

theorem cell23_6021841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_6021841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021841 prefixEnd_6021841 := by exact prefixLift 6021841
  have htrace : WordTrace (prefixWord ++ tailWord_6021841) baseStart_6021841 baseEnd_6021841 := by
    simpa [prefixWord, tailWord_6021841, baseEnd_6021841] using wordTrace_append hprefix tailTrace_6021841
  have hstable : (prefixWord ++ tailWord_6021841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021841).length < 2 ^ (prefixWord ++ tailWord_6021841).sum := by decide
  have hdescent : baseEnd_6021841 < baseStart_6021841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021855 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 2, 4, 2]
def baseStart_6021855 : Nat := 118140960795 + 6021855 * 2 ^ 59
def prefixEnd_6021855 : Nat := 4983230072969 + 3 ^ 40 * 6021855 * 2
def baseEnd_6021855 : Nat := 3092106046680642198318499

theorem tailTrace_6021855 : CollatzResearch.WordTrace tailWord_6021855 prefixEnd_6021855 3092106046680642198318499 := by
  unfold tailWord_6021855
  simp only [CollatzResearch.WordTrace]
  refine ⟨219635095598855260799947019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146423397065903507199964679 219635095598855260799947019)
  ·
    refine ⟨329452643398282891199920529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219635095598855260799947019 329452643398282891199920529)
    ·
      refine ⟨247089482548712168399940397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329452643398282891199920529 247089482548712168399940397)
      ·
        refine ⟨92658555955767063149977649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247089482548712168399940397 92658555955767063149977649)
        ·
          refine ⟨69493916966825297362483237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92658555955767063149977649 69493916966825297362483237)
          ·
            refine ⟨13030109431279743255465607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69493916966825297362483237 13030109431279743255465607)
            ·
              refine ⟨19545164146919614883198411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13030109431279743255465607 19545164146919614883198411)
              ·
                refine ⟨29317746220379422324797617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19545164146919614883198411 29317746220379422324797617)
                ·
                  refine ⟨21988309665284566743598213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29317746220379422324797617 21988309665284566743598213)
                  ·
                    refine ⟨4122808062240856264424665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21988309665284566743598213 4122808062240856264424665)
                    ·
                      refine ⟨3092106046680642198318499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122808062240856264424665 3092106046680642198318499)
                      ·
                        rfl

theorem cell23_6021855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_6021855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021855 prefixEnd_6021855 := by exact prefixLift 6021855
  have htrace : WordTrace (prefixWord ++ tailWord_6021855) baseStart_6021855 baseEnd_6021855 := by
    simpa [prefixWord, tailWord_6021855, baseEnd_6021855] using wordTrace_append hprefix tailTrace_6021855
  have hstable : (prefixWord ++ tailWord_6021855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021855).length < 2 ^ (prefixWord ++ tailWord_6021855).sum := by decide
  have hdescent : baseEnd_6021855 < baseStart_6021855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021878 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_6021878 : Nat := 118140960795 + 6021878 * 2 ^ 59
def prefixEnd_6021878 : Nat := 4983230072969 + 3 ^ 40 * 6021878 * 2
def baseEnd_6021878 : Nat := 343568650748410623147877

theorem tailTrace_6021878 : CollatzResearch.WordTrace tailWord_6021878 prefixEnd_6021878 343568650748410623147877 := by
  unfold tailWord_6021878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13727245904860745983002143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146423956318514623818689525 13727245904860745983002143)
  ·
    refine ⟨20590868857291118974503215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13727245904860745983002143 20590868857291118974503215)
    ·
      refine ⟨30886303285936678461754823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20590868857291118974503215 30886303285936678461754823)
      ·
        refine ⟨46329454928905017692632235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30886303285936678461754823 46329454928905017692632235)
        ·
          refine ⟨69494182393357526538948353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46329454928905017692632235 69494182393357526538948353)
          ·
            refine ⟨52120636795018144904211265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69494182393357526538948353 52120636795018144904211265)
            ·
              refine ⟨39090477596263608678158449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52120636795018144904211265 39090477596263608678158449)
              ·
                refine ⟨29317858197197706508618837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39090477596263608678158449 29317858197197706508618837)
                ·
                  refine ⟨343568650748410623147877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29317858197197706508618837 343568650748410623147877)
                  ·
                    rfl

theorem cell23_6021878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_6021878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021878 prefixEnd_6021878 := by exact prefixLift 6021878
  have htrace : WordTrace (prefixWord ++ tailWord_6021878) baseStart_6021878 baseEnd_6021878 := by
    simpa [prefixWord, tailWord_6021878, baseEnd_6021878] using wordTrace_append hprefix tailTrace_6021878
  have hstable : (prefixWord ++ tailWord_6021878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021878).length < 2 ^ (prefixWord ++ tailWord_6021878).sum := by decide
  have hdescent : baseEnd_6021878 < baseStart_6021878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021881 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_6021881 : Nat := 118140960795 + 6021881 * 2 ^ 59
def prefixEnd_6021881 : Nat := 4983230072969 + 3 ^ 40 * 6021881 * 2
def baseEnd_6021881 : Nat := 3092119397177659096593379

theorem tailTrace_6021881 : CollatzResearch.WordTrace tailWord_6021881 prefixEnd_6021881 3092119397177659096593379 := by
  unfold tailWord_6021881
  simp only [CollatzResearch.WordTrace]
  refine ⟨219636043896761067240393497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146424029264507378160262331 219636043896761067240393497)
  ·
    refine ⟨164727032922570800430295123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219636043896761067240393497 164727032922570800430295123)
    ·
      refine ⟨247090549383856200645442685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164727032922570800430295123 247090549383856200645442685)
      ·
        refine ⟨92658956018946075242041007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247090549383856200645442685 92658956018946075242041007)
        ·
          refine ⟨138988434028419112863061511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92658956018946075242041007 138988434028419112863061511)
          ·
            refine ⟨208482651042628669294592267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138988434028419112863061511 208482651042628669294592267)
            ·
              refine ⟨312723976563943003941888401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208482651042628669294592267 312723976563943003941888401)
              ·
                refine ⟨234542982422957252956416301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312723976563943003941888401 234542982422957252956416301)
                ·
                  refine ⟨87953618408608969858656113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234542982422957252956416301 87953618408608969858656113)
                  ·
                    refine ⟨65965213806456727393992085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87953618408608969858656113 65965213806456727393992085)
                    ·
                      refine ⟨3092119397177659096593379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65965213806456727393992085 3092119397177659096593379)
                      ·
                        rfl

theorem cell23_6021881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_6021881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021881 prefixEnd_6021881 := by exact prefixLift 6021881
  have htrace : WordTrace (prefixWord ++ tailWord_6021881) baseStart_6021881 baseEnd_6021881 := by
    simpa [prefixWord, tailWord_6021881, baseEnd_6021881] using wordTrace_append hprefix tailTrace_6021881
  have hstable : (prefixWord ++ tailWord_6021881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021881).length < 2 ^ (prefixWord ++ tailWord_6021881).sum := by decide
  have hdescent : baseEnd_6021881 < baseStart_6021881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021895 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 6]
def baseStart_6021895 : Nat := 118140960795 + 6021895 * 2 ^ 59
def prefixEnd_6021895 : Nat := 4983230072969 + 3 ^ 40 * 6021895 * 2
def baseEnd_6021895 : Nat := 343569620656313560202035

theorem tailTrace_6021895 : CollatzResearch.WordTrace tailWord_6021895 prefixEnd_6021895 343569620656313560202035 := by
  unfold tailWord_6021895
  simp only [CollatzResearch.WordTrace]
  refine ⟨219636554518710347631403139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146424369679140231754268759 219636554518710347631403139)
  ·
    refine ⟨329454831778065521447104709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219636554518710347631403139 329454831778065521447104709)
    ·
      refine ⟨61772780958387285271332133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329454831778065521447104709 61772780958387285271332133)
      ·
        refine ⟨11582396429697615988374775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61772780958387285271332133 11582396429697615988374775)
        ·
          refine ⟨17373594644546423982562163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11582396429697615988374775 17373594644546423982562163)
          ·
            refine ⟨26060391966819635973843245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17373594644546423982562163 26060391966819635973843245)
            ·
              refine ⟨9772646987557363490191217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26060391966819635973843245 9772646987557363490191217)
              ·
                refine ⟨7329485240668022617643413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9772646987557363490191217 7329485240668022617643413)
                ·
                  refine ⟨343569620656313560202035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7329485240668022617643413 343569620656313560202035)
                  ·
                    rfl

theorem cell23_6021895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 6].length) (baseStart_6021895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021895 prefixEnd_6021895 := by exact prefixLift 6021895
  have htrace : WordTrace (prefixWord ++ tailWord_6021895) baseStart_6021895 baseEnd_6021895 := by
    simpa [prefixWord, tailWord_6021895, baseEnd_6021895] using wordTrace_append hprefix tailTrace_6021895
  have hstable : (prefixWord ++ tailWord_6021895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021895).length < 2 ^ (prefixWord ++ tailWord_6021895).sum := by decide
  have hdescent : baseEnd_6021895 < baseStart_6021895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021905 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 3, 1, 3]
def baseStart_6021905 : Nat := 118140960795 + 6021905 * 2 ^ 59
def prefixEnd_6021905 : Nat := 4983230072969 + 3 ^ 40 * 6021905 * 2
def baseEnd_6021905 : Nat := 3092131720713367002693269

theorem tailTrace_6021905 : CollatzResearch.WordTrace tailWord_6021905 prefixEnd_6021905 3092131720713367002693269 := by
  unfold tailWord_6021905
  simp only [CollatzResearch.WordTrace]
  refine ⟨219636919248674119339267169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146424612832449412892844779 219636919248674119339267169)
  ·
    refine ⟨164727689436505589504450377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219636919248674119339267169 164727689436505589504450377)
    ·
      refine ⟨123545767077379192128337783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164727689436505589504450377 123545767077379192128337783)
      ·
        refine ⟨185318650616068788192506675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123545767077379192128337783 185318650616068788192506675)
        ·
          refine ⟨277977975924103182288760013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185318650616068788192506675 277977975924103182288760013)
          ·
            refine ⟨104241740971538693358285005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277977975924103182288760013 104241740971538693358285005)
            ·
              refine ⟨39090652864327010009356877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104241740971538693358285005 39090652864327010009356877)
              ·
                refine ⟨14658994824122628753508829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39090652864327010009356877 14658994824122628753508829)
                ·
                  refine ⟨5497123059045985782565811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14658994824122628753508829 5497123059045985782565811)
                  ·
                    refine ⟨8245684588568978673848717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5497123059045985782565811 8245684588568978673848717)
                    ·
                      refine ⟨3092131720713367002693269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8245684588568978673848717 3092131720713367002693269)
                      ·
                        rfl

theorem cell23_6021905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_6021905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021905 prefixEnd_6021905 := by exact prefixLift 6021905
  have htrace : WordTrace (prefixWord ++ tailWord_6021905) baseStart_6021905 baseEnd_6021905 := by
    simpa [prefixWord, tailWord_6021905, baseEnd_6021905] using wordTrace_append hprefix tailTrace_6021905
  have hstable : (prefixWord ++ tailWord_6021905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021905).length < 2 ^ (prefixWord ++ tailWord_6021905).sum := by decide
  have hdescent : baseEnd_6021905 < baseStart_6021905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021922 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_6021922 : Nat := 118140960795 + 6021922 * 2 ^ 59
def prefixEnd_6021922 : Nat := 4983230072969 + 3 ^ 40 * 6021922 * 2
def baseEnd_6021922 : Nat := 3092140449884493436180691

theorem tailTrace_6021922 : CollatzResearch.WordTrace tailWord_6021922 prefixEnd_6021922 3092140449884493436180691 := by
  unfold tailWord_6021922
  simp only [CollatzResearch.WordTrace]
  refine ⟨54909384822403132810659005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146425026193075020828424013 54909384822403132810659005)
  ·
    refine ⟨20591019308401174803997127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54909384822403132810659005 20591019308401174803997127)
    ·
      refine ⟨30886528962601762205995691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20591019308401174803997127 30886528962601762205995691)
      ·
        refine ⟨46329793443902643308993537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30886528962601762205995691 46329793443902643308993537)
        ·
          refine ⟨34747345082926982481745153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46329793443902643308993537 34747345082926982481745153)
          ·
            refine ⟨26060508812195236861308865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34747345082926982481745153 26060508812195236861308865)
            ·
              refine ⟨19545381609146427645981649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26060508812195236861308865 19545381609146427645981649)
              ·
                refine ⟨14659036206859820734486237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19545381609146427645981649 14659036206859820734486237)
                ·
                  refine ⟨5497138577572432775432339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14659036206859820734486237 5497138577572432775432339)
                  ·
                    refine ⟨8245707866358649163148509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5497138577572432775432339 8245707866358649163148509)
                    ·
                      refine ⟨3092140449884493436180691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8245707866358649163148509 3092140449884493436180691)
                      ·
                        rfl

theorem cell23_6021922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_6021922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021922 prefixEnd_6021922 := by exact prefixLift 6021922
  have htrace : WordTrace (prefixWord ++ tailWord_6021922) baseStart_6021922 baseEnd_6021922 := by
    simpa [prefixWord, tailWord_6021922, baseEnd_6021922] using wordTrace_append hprefix tailTrace_6021922
  have hstable : (prefixWord ++ tailWord_6021922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021922).length < 2 ^ (prefixWord ++ tailWord_6021922).sum := by decide
  have hdescent : baseEnd_6021922 < baseStart_6021922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021925 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_6021925 : Nat := 118140960795 + 6021925 * 2 ^ 59
def prefixEnd_6021925 : Nat := 4983230072969 + 3 ^ 40 * 6021925 * 2
def baseEnd_6021925 : Nat := 1030713996775485641481059

theorem tailTrace_6021925 : CollatzResearch.WordTrace tailWord_6021925 prefixEnd_6021925 1030713996775485641481059 := by
  unfold tailWord_6021925
  simp only [CollatzResearch.WordTrace]
  refine ⟨219637648708601662754995229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146425099139067775169996819 219637648708601662754995229)
  ·
    refine ⟨82364118265725623533123211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219637648708601662754995229 82364118265725623533123211)
    ·
      refine ⟨123546177398588435299684817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82364118265725623533123211 123546177398588435299684817)
      ·
        refine ⟨92659633048941326474763613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123546177398588435299684817 92659633048941326474763613)
        ·
          refine ⟨34747362393352997428036355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92659633048941326474763613 34747362393352997428036355)
          ·
            refine ⟨52121043590029496142054533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34747362393352997428036355 52121043590029496142054533)
            ·
              refine ⟨9772695673130530526635225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52121043590029496142054533 9772695673130530526635225)
              ·
                refine ⟨7329521754847897894976419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9772695673130530526635225 7329521754847897894976419)
                ·
                  refine ⟨10994282632271846842464629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7329521754847897894976419 10994282632271846842464629)
                  ·
                    refine ⟨1030713996775485641481059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10994282632271846842464629 1030713996775485641481059)
                    ·
                      rfl

theorem cell23_6021925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_6021925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021925 prefixEnd_6021925 := by exact prefixLift 6021925
  have htrace : WordTrace (prefixWord ++ tailWord_6021925) baseStart_6021925 baseEnd_6021925 := by
    simpa [prefixWord, tailWord_6021925, baseEnd_6021925] using wordTrace_append hprefix tailTrace_6021925
  have hstable : (prefixWord ++ tailWord_6021925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021925).length < 2 ^ (prefixWord ++ tailWord_6021925).sum := by decide
  have hdescent : baseEnd_6021925 < baseStart_6021925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021933 : List Nat := [1, 5, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_6021933 : Nat := 118140960795 + 6021933 * 2 ^ 59
def prefixEnd_6021933 : Nat := 4983230072969 + 3 ^ 40 * 6021933 * 2
def baseEnd_6021933 : Nat := 1030715366057230964381047

theorem tailTrace_6021933 : CollatzResearch.WordTrace tailWord_6021933 prefixEnd_6021933 1030715366057230964381047 := by
  unfold tailWord_6021933
  simp only [CollatzResearch.WordTrace]
  refine ⟨219637940492572680121286453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146425293661715120080857635 219637940492572680121286453)
  ·
    refine ⟨20591056921178688761370605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219637940492572680121286453 20591056921178688761370605)
    ·
      refine ⟨7721646345442008285513977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20591056921178688761370605 7721646345442008285513977)
      ·
        refine ⟨5791234759081506214135483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7721646345442008285513977 5791234759081506214135483)
        ·
          refine ⟨8686852138622259321203225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5791234759081506214135483 8686852138622259321203225)
          ·
            refine ⟨6515139103966694490902419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8686852138622259321203225 6515139103966694490902419)
            ·
              refine ⟨9772708655950041736353629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6515139103966694490902419 9772708655950041736353629)
              ·
                refine ⟨3664765745981265651132611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9772708655950041736353629 3664765745981265651132611)
                ·
                  refine ⟨5497148618971898476698917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664765745981265651132611 5497148618971898476698917)
                  ·
                    refine ⟨1030715366057230964381047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5497148618971898476698917 1030715366057230964381047)
                    ·
                      rfl

theorem cell23_6021933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_6021933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021933 prefixEnd_6021933 := by exact prefixLift 6021933
  have htrace : WordTrace (prefixWord ++ tailWord_6021933) baseStart_6021933 baseEnd_6021933 := by
    simpa [prefixWord, tailWord_6021933, baseEnd_6021933] using wordTrace_append hprefix tailTrace_6021933
  have hstable : (prefixWord ++ tailWord_6021933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021933).length < 2 ^ (prefixWord ++ tailWord_6021933).sum := by decide
  have hdescent : baseEnd_6021933 < baseStart_6021933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021938 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_6021938 : Nat := 118140960795 + 6021938 * 2 ^ 59
def prefixEnd_6021938 : Nat := 4983230072969 + 3 ^ 40 * 6021938 * 2
def baseEnd_6021938 : Nat := 1030716221858321791193539

theorem tailTrace_6021938 : CollatzResearch.WordTrace tailWord_6021938 prefixEnd_6021938 1030716221858321791193539 := by
  unfold tailWord_6021938
  simp only [CollatzResearch.WordTrace]
  refine ⟨54909530714388641493804617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146425415238369710650145645 54909530714388641493804617)
  ·
    refine ⟨41182148035791481120353463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54909530714388641493804617 41182148035791481120353463)
    ·
      refine ⟨61773222053687221680530195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41182148035791481120353463 61773222053687221680530195)
      ·
        refine ⟨92659833080530832520795293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61773222053687221680530195 92659833080530832520795293)
        ·
          refine ⟨34747437405199062195298235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92659833080530832520795293 34747437405199062195298235)
          ·
            refine ⟨52121156107798593292947353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34747437405199062195298235 52121156107798593292947353)
            ·
              refine ⟨39090867080848944969710515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52121156107798593292947353 39090867080848944969710515)
              ·
                refine ⟨58636300621273417454565773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39090867080848944969710515 58636300621273417454565773)
                ·
                  refine ⟨21988612732977531545462165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58636300621273417454565773 21988612732977531545462165)
                  ·
                    refine ⟨1030716221858321791193539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21988612732977531545462165 1030716221858321791193539)
                    ·
                      rfl

theorem cell23_6021938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_6021938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021938 prefixEnd_6021938 := by exact prefixLift 6021938
  have htrace : WordTrace (prefixWord ++ tailWord_6021938) baseStart_6021938 baseEnd_6021938 := by
    simpa [prefixWord, tailWord_6021938, baseEnd_6021938] using wordTrace_append hprefix tailTrace_6021938
  have hstable : (prefixWord ++ tailWord_6021938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021938).length < 2 ^ (prefixWord ++ tailWord_6021938).sum := by decide
  have hdescent : baseEnd_6021938 < baseStart_6021938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021939 : List Nat := [1, 1, 1, 2, 6, 1, 3, 3, 1, 1, 3]
def baseStart_6021939 : Nat := 118140960795 + 6021939 * 2 ^ 59
def prefixEnd_6021939 : Nat := 4983230072969 + 3 ^ 40 * 6021939 * 2
def baseEnd_6021939 : Nat := 3092149179055619869668113

theorem tailTrace_6021939 : CollatzResearch.WordTrace tailWord_6021939 prefixEnd_6021939 3092149179055619869668113 := by
  unfold tailWord_6021939
  simp only [CollatzResearch.WordTrace]
  refine ⟨219638159330550943146004871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146425439553700628764003247 219638159330550943146004871)
  ·
    refine ⟨329457238995826414719007307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219638159330550943146004871 329457238995826414719007307)
    ·
      refine ⟨494185858493739622078510961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329457238995826414719007307 494185858493739622078510961)
      ·
        refine ⟨370639393870304716558883221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494185858493739622078510961 370639393870304716558883221)
        ·
          refine ⟨17373721587670533588697651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 370639393870304716558883221 17373721587670533588697651)
          ·
            refine ⟨26060582381505800383046477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17373721587670533588697651 26060582381505800383046477)
            ·
              refine ⟨9772718393064675143642429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26060582381505800383046477 9772718393064675143642429)
              ·
                refine ⟨3664769397399253178865911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9772718393064675143642429 3664769397399253178865911)
                ·
                  refine ⟨5497154096098879768298867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664769397399253178865911 5497154096098879768298867)
                  ·
                    refine ⟨8245731144148319652448301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5497154096098879768298867 8245731144148319652448301)
                    ·
                      refine ⟨3092149179055619869668113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8245731144148319652448301 3092149179055619869668113)
                      ·
                        rfl

theorem cell23_6021939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 1, 1, 3].length) (baseStart_6021939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021939 prefixEnd_6021939 := by exact prefixLift 6021939
  have htrace : WordTrace (prefixWord ++ tailWord_6021939) baseStart_6021939 baseEnd_6021939 := by
    simpa [prefixWord, tailWord_6021939, baseEnd_6021939] using wordTrace_append hprefix tailTrace_6021939
  have hstable : (prefixWord ++ tailWord_6021939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021939).length < 2 ^ (prefixWord ++ tailWord_6021939).sum := by decide
  have hdescent : baseEnd_6021939 < baseStart_6021939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021949 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 2, 3, 2]
def baseStart_6021949 : Nat := 118140960795 + 6021949 * 2 ^ 59
def prefixEnd_6021949 : Nat := 4983230072969 + 3 ^ 40 * 6021949 * 2
def baseEnd_6021949 : Nat := 3092154313862164830543067

theorem tailTrace_6021949 : CollatzResearch.WordTrace tailWord_6021949 prefixEnd_6021949 3092154313862164830543067 := by
  unfold tailWord_6021949
  simp only [CollatzResearch.WordTrace]
  refine ⟨219638524060514714853868901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146425682707009809902579267 219638524060514714853868901)
  ·
    refine ⟨41182223261346509035100419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219638524060514714853868901 41182223261346509035100419)
    ·
      refine ⟨61773334892019763552650629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41182223261346509035100419 61773334892019763552650629)
      ·
        refine ⟨11582500292253705666121993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61773334892019763552650629 11582500292253705666121993)
        ·
          refine ⟨8686875219190279249591495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11582500292253705666121993 8686875219190279249591495)
          ·
            refine ⟨13030312828785418874387243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8686875219190279249591495 13030312828785418874387243)
            ·
              refine ⟨19545469243178128311580865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13030312828785418874387243 19545469243178128311580865)
              ·
                refine ⟨14659101932383596233685649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19545469243178128311580865 14659101932383596233685649)
                ·
                  refine ⟨10994326449287697175264237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14659101932383596233685649 10994326449287697175264237)
                  ·
                    refine ⟨4122872418482886440724089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10994326449287697175264237 4122872418482886440724089)
                    ·
                      refine ⟨3092154313862164830543067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122872418482886440724089 3092154313862164830543067)
                      ·
                        rfl

theorem cell23_6021949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_6021949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021949 prefixEnd_6021949 := by exact prefixLift 6021949
  have htrace : WordTrace (prefixWord ++ tailWord_6021949) baseStart_6021949 baseEnd_6021949 := by
    simpa [prefixWord, tailWord_6021949, baseEnd_6021949] using wordTrace_append hprefix tailTrace_6021949
  have hstable : (prefixWord ++ tailWord_6021949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021949).length < 2 ^ (prefixWord ++ tailWord_6021949).sum := by decide
  have hdescent : baseEnd_6021949 < baseStart_6021949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021955 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 2, 4]
def baseStart_6021955 : Nat := 118140960795 + 6021955 * 2 ^ 59
def prefixEnd_6021955 : Nat := 4983230072969 + 3 ^ 40 * 6021955 * 2
def baseEnd_6021955 : Nat := 1030719131582030602356013

theorem tailTrace_6021955 : CollatzResearch.WordTrace tailWord_6021955 prefixEnd_6021955 1030719131582030602356013 := by
  unfold tailWord_6021955
  simp only [CollatzResearch.WordTrace]
  refine ⟨219638742898492977878587319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146425828598995318585724879 219638742898492977878587319)
  ·
    refine ⟨329458114347739466817880979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219638742898492977878587319 329458114347739466817880979)
    ·
      refine ⟨494187171521609200226821469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329458114347739466817880979 494187171521609200226821469)
      ·
        refine ⟨185320189320603450085058051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494187171521609200226821469 185320189320603450085058051)
        ·
          refine ⟨277980283980905175127587077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185320189320603450085058051 277980283980905175127587077)
          ·
            refine ⟨52121303246419720336422577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277980283980905175127587077 52121303246419720336422577)
            ·
              refine ⟨39090977434814790252316933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52121303246419720336422577 39090977434814790252316933)
              ·
                refine ⟨7329558269027773172309425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39090977434814790252316933 7329558269027773172309425)
                ·
                  refine ⟨5497168701770829879232069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7329558269027773172309425 5497168701770829879232069)
                  ·
                    refine ⟨1030719131582030602356013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5497168701770829879232069 1030719131582030602356013)
                    ·
                      rfl

theorem cell23_6021955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 4].length) (baseStart_6021955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021955 prefixEnd_6021955 := by exact prefixLift 6021955
  have htrace : WordTrace (prefixWord ++ tailWord_6021955) baseStart_6021955 baseEnd_6021955 := by
    simpa [prefixWord, tailWord_6021955, baseEnd_6021955] using wordTrace_append hprefix tailTrace_6021955
  have hstable : (prefixWord ++ tailWord_6021955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021955).length < 2 ^ (prefixWord ++ tailWord_6021955).sum := by decide
  have hdescent : baseEnd_6021955 < baseStart_6021955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021962 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2]
def baseStart_6021962 : Nat := 118140960795 + 6021962 * 2 ^ 59
def prefixEnd_6021962 : Nat := 4983230072969 + 3 ^ 40 * 6021962 * 2
def baseEnd_6021962 : Nat := 3092160989110673279680507

theorem tailTrace_6021962 : CollatzResearch.WordTrace tailWord_6021962 prefixEnd_6021962 3092160989110673279680507 := by
  unfold tailWord_6021962
  simp only [CollatzResearch.WordTrace]
  refine ⟨54909749552366904518523035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146425998806311745382728093 54909749552366904518523035)
  ·
    refine ⟨82364624328550356777784553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54909749552366904518523035 82364624328550356777784553)
    ·
      refine ⟨61773468246412767583338415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82364624328550356777784553 61773468246412767583338415)
      ·
        refine ⟨92660202369619151375007623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61773468246412767583338415 92660202369619151375007623)
        ·
          refine ⟨138990303554428727062511435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92660202369619151375007623 138990303554428727062511435)
          ·
            refine ⟨208485455331643090593767153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138990303554428727062511435 208485455331643090593767153)
            ·
              refine ⟨156364091498732317945325365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208485455331643090593767153 156364091498732317945325365)
              ·
                refine ⟨14659133578006154807374253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156364091498732317945325365 14659133578006154807374253)
                ·
                  refine ⟨5497175091752308052765345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14659133578006154807374253 5497175091752308052765345)
                  ·
                    refine ⟨4122881318814231039574009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5497175091752308052765345 4122881318814231039574009)
                    ·
                      refine ⟨3092160989110673279680507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122881318814231039574009 3092160989110673279680507)
                      ·
                        rfl

theorem cell23_6021962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_6021962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021962 prefixEnd_6021962 := by exact prefixLift 6021962
  have htrace : WordTrace (prefixWord ++ tailWord_6021962) baseStart_6021962 baseEnd_6021962 := by
    simpa [prefixWord, tailWord_6021962, baseEnd_6021962] using wordTrace_append hprefix tailTrace_6021962
  have hstable : (prefixWord ++ tailWord_6021962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021962).length < 2 ^ (prefixWord ++ tailWord_6021962).sum := by decide
  have hdescent : baseEnd_6021962 < baseStart_6021962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6021995 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 6, 1, 3]
def baseStart_6021995 : Nat := 118140960795 + 6021995 * 2 ^ 59
def prefixEnd_6021995 : Nat := 4983230072969 + 3 ^ 40 * 6021995 * 2
def baseEnd_6021995 : Nat := 3092177933972271650567855

theorem tailTrace_6021995 : CollatzResearch.WordTrace tailWord_6021995 prefixEnd_6021995 3092177933972271650567855 := by
  unfold tailWord_6021995
  simp only [CollatzResearch.WordTrace]
  refine ⟨219640201818348064710043439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146426801212232043140028959 219640201818348064710043439)
  ·
    refine ⟨329460302727522097065065159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219640201818348064710043439 329460302727522097065065159)
    ·
      refine ⟨494190454091283145597597739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329460302727522097065065159 494190454091283145597597739)
      ·
        refine ⟨741285681136924718396396609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494190454091283145597597739 741285681136924718396396609)
        ·
          refine ⟨555964260852693538797297457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 741285681136924718396396609 555964260852693538797297457)
          ·
            refine ⟨416973195639520154097973093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555964260852693538797297457 416973195639520154097973093)
            ·
              refine ⟨78182474182410028893369955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 416973195639520154097973093 78182474182410028893369955)
              ·
                refine ⟨117273711273615043340054933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78182474182410028893369955 117273711273615043340054933)
                ·
                  refine ⟨5497205215950705156565075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117273711273615043340054933 5497205215950705156565075)
                  ·
                    refine ⟨8245807823926057734847613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5497205215950705156565075 8245807823926057734847613)
                    ·
                      refine ⟨3092177933972271650567855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8245807823926057734847613 3092177933972271650567855)
                      ·
                        rfl

theorem cell23_6021995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 1, 3].length) (baseStart_6021995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6021995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6021995 prefixEnd_6021995 := by exact prefixLift 6021995
  have htrace : WordTrace (prefixWord ++ tailWord_6021995) baseStart_6021995 baseEnd_6021995 := by
    simpa [prefixWord, tailWord_6021995, baseEnd_6021995] using wordTrace_append hprefix tailTrace_6021995
  have hstable : (prefixWord ++ tailWord_6021995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6021995).length < 2 ^ (prefixWord ++ tailWord_6021995).sum := by decide
  have hdescent : baseEnd_6021995 < baseStart_6021995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6021995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022028 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_6022028 : Nat := 118140960795 + 6022028 * 2 ^ 59
def prefixEnd_6022028 : Nat := 4983230072969 + 3 ^ 40 * 6022028 * 2
def baseEnd_6022028 : Nat := 1030731626277956673818401

theorem tailTrace_6022028 : CollatzResearch.WordTrace tailWord_6022028 prefixEnd_6022028 1030731626277956673818401 := by
  unfold tailWord_6022028
  simp only [CollatzResearch.WordTrace]
  refine ⟨109820702713614255672997369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146427603618152340897329825 109820702713614255672997369)
  ·
    refine ⟨82365527035210691754748027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109820702713614255672997369 82365527035210691754748027)
    ·
      refine ⟨123548290552816037632122041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82365527035210691754748027 123548290552816037632122041)
      ·
        refine ⟨92661217914612028224091531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123548290552816037632122041 92661217914612028224091531)
        ·
          refine ⟨138991826871918042336137297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92661217914612028224091531 138991826871918042336137297)
          ·
            refine ⟨104243870153938531752102973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138991826871918042336137297 104243870153938531752102973)
            ·
              refine ⟨39091451307726949407038615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104243870153938531752102973 39091451307726949407038615)
              ·
                refine ⟨58637176961590424110557923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39091451307726949407038615 58637176961590424110557923)
                ·
                  refine ⟨87955765442385636165836885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58637176961590424110557923 87955765442385636165836885)
                  ·
                    refine ⟨1030731626277956673818401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87955765442385636165836885 1030731626277956673818401)
                    ·
                      rfl

theorem cell23_6022028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_6022028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022028 prefixEnd_6022028 := by exact prefixLift 6022028
  have htrace : WordTrace (prefixWord ++ tailWord_6022028) baseStart_6022028 baseEnd_6022028 := by
    simpa [prefixWord, tailWord_6022028, baseEnd_6022028] using wordTrace_append hprefix tailTrace_6022028
  have hstable : (prefixWord ++ tailWord_6022028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022028).length < 2 ^ (prefixWord ++ tailWord_6022028).sum := by decide
  have hdescent : baseEnd_6022028 < baseStart_6022028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022052 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 1, 4, 2]
def baseStart_6022052 : Nat := 118140960795 + 6022052 * 2 ^ 59
def prefixEnd_6022052 : Nat := 4983230072969 + 3 ^ 40 * 6022052 * 2
def baseEnd_6022052 : Nat := 3092207202369577927555093

theorem tailTrace_6022052 : CollatzResearch.WordTrace tailWord_6022052 prefixEnd_6022052 3092207202369577927555093 := by
  unfold tailWord_6022052
  simp only [CollatzResearch.WordTrace]
  refine ⟨109821140389570781722434205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146428187186094375629912273 109821140389570781722434205)
  ·
    refine ⟨41182927646089043145912827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109821140389570781722434205 41182927646089043145912827)
    ·
      refine ⟨61774391469133564718869241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41182927646089043145912827 61774391469133564718869241)
      ·
        refine ⟨46330793601850173539151931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61774391469133564718869241 46330793601850173539151931)
        ·
          refine ⟨69496190402775260308727897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46330793601850173539151931 69496190402775260308727897)
          ·
            refine ⟨52122142802081445231545923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69496190402775260308727897 52122142802081445231545923)
            ·
              refine ⟨78183214203122167847318885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52122142802081445231545923 78183214203122167847318885)
              ·
                refine ⟨14659352663085406471372291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78183214203122167847318885 14659352663085406471372291)
                ·
                  refine ⟨21989028994628109707058437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14659352663085406471372291 21989028994628109707058437)
                  ·
                    refine ⟨4122942936492770570073457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21989028994628109707058437 4122942936492770570073457)
                    ·
                      refine ⟨3092207202369577927555093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122942936492770570073457 3092207202369577927555093)
                      ·
                        rfl

theorem cell23_6022052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_6022052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022052 prefixEnd_6022052 := by exact prefixLift 6022052
  have htrace : WordTrace (prefixWord ++ tailWord_6022052) baseStart_6022052 baseEnd_6022052 := by
    simpa [prefixWord, tailWord_6022052, baseEnd_6022052] using wordTrace_append hprefix tailTrace_6022052
  have hstable : (prefixWord ++ tailWord_6022052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022052).length < 2 ^ (prefixWord ++ tailWord_6022052).sum := by decide
  have hdescent : baseEnd_6022052 < baseStart_6022052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022069 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_6022069 : Nat := 118140960795 + 6022069 * 2 ^ 59
def prefixEnd_6022069 : Nat := 4983230072969 + 3 ^ 40 * 6022069 * 2
def baseEnd_6022069 : Nat := 3092215931540704361042515

theorem tailTrace_6022069 : CollatzResearch.WordTrace tailWord_6022069 prefixEnd_6022069 3092215931540704361042515 := by
  unfold tailWord_6022069
  simp only [CollatzResearch.WordTrace]
  refine ⟨219642900820079975348237261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146428600546719983565491507 219642900820079975348237261)
  ·
    refine ⟨82366087807529990755588973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219642900820079975348237261 82366087807529990755588973)
    ·
      refine ⟨30887282927823746533345865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82366087807529990755588973 30887282927823746533345865)
      ·
        refine ⟨23165462195867809900009399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30887282927823746533345865 23165462195867809900009399)
        ·
          refine ⟨34748193293801714850014099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23165462195867809900009399 34748193293801714850014099)
          ·
            refine ⟨52122289940702572275021149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34748193293801714850014099 52122289940702572275021149)
            ·
              refine ⟨19545858727763464603132931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52122289940702572275021149 19545858727763464603132931)
              ·
                refine ⟨29318788091645196904699397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19545858727763464603132931 29318788091645196904699397)
                ·
                  refine ⟨5497272767183474419631137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29318788091645196904699397 5497272767183474419631137)
                  ·
                    refine ⟨4122954575387605814723353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5497272767183474419631137 4122954575387605814723353)
                    ·
                      refine ⟨3092215931540704361042515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122954575387605814723353 3092215931540704361042515)
                      ·
                        rfl

theorem cell23_6022069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_6022069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022069 prefixEnd_6022069 := by exact prefixLift 6022069
  have htrace : WordTrace (prefixWord ++ tailWord_6022069) baseStart_6022069 baseEnd_6022069 := by
    simpa [prefixWord, tailWord_6022069, baseEnd_6022069] using wordTrace_append hprefix tailTrace_6022069
  have hstable : (prefixWord ++ tailWord_6022069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022069).length < 2 ^ (prefixWord ++ tailWord_6022069).sum := by decide
  have hdescent : baseEnd_6022069 < baseStart_6022069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022105 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 1, 7]
def baseStart_6022105 : Nat := 118140960795 + 6022105 * 2 ^ 59
def prefixEnd_6022105 : Nat := 4983230072969 + 3 ^ 40 * 6022105 * 2
def baseEnd_6022105 : Nat := 1030744805614755406730783

theorem tailTrace_6022105 : CollatzResearch.WordTrace tailWord_6022105 prefixEnd_6022105 1030744805614755406730783 := by
  unfold tailWord_6022105
  simp only [CollatzResearch.WordTrace]
  refine ⟨219644213847949553496547769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146429475898633035664365179 219644213847949553496547769)
  ·
    refine ⟨164733160385962165122410827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219644213847949553496547769 164733160385962165122410827)
    ·
      refine ⟨247099740578943247683616241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164733160385962165122410827 247099740578943247683616241)
      ·
        refine ⟨185324805434207435762712181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247099740578943247683616241 185324805434207435762712181)
        ·
          refine ⟨17374200509456947102754267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185324805434207435762712181 17374200509456947102754267)
          ·
            refine ⟨26061300764185420654131401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17374200509456947102754267 26061300764185420654131401)
            ·
              refine ⟨19545975573139065490598551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26061300764185420654131401 19545975573139065490598551)
              ·
                refine ⟨29318963359708598235897827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19545975573139065490598551 29318963359708598235897827)
                ·
                  refine ⟨43978445039562897353846741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29318963359708598235897827 43978445039562897353846741)
                  ·
                    refine ⟨1030744805614755406730783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43978445039562897353846741 1030744805614755406730783)
                    ·
                      rfl

theorem cell23_6022105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_6022105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022105 prefixEnd_6022105 := by exact prefixLift 6022105
  have htrace : WordTrace (prefixWord ++ tailWord_6022105) baseStart_6022105 baseEnd_6022105 := by
    simpa [prefixWord, tailWord_6022105, baseEnd_6022105] using wordTrace_append hprefix tailTrace_6022105
  have hstable : (prefixWord ++ tailWord_6022105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022105).length < 2 ^ (prefixWord ++ tailWord_6022105).sum := by decide
  have hdescent : baseEnd_6022105 < baseStart_6022105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022109 : List Nat := [1, 4, 3, 1, 2, 1, 3, 3, 5]
def baseStart_6022109 : Nat := 118140960795 + 6022109 * 2 ^ 59
def prefixEnd_6022109 : Nat := 4983230072969 + 3 ^ 40 * 6022109 * 2
def baseEnd_6022109 : Nat := 343581830085209356060259

theorem tailTrace_6022109 : CollatzResearch.WordTrace tailWord_6022109 prefixEnd_6022109 343581830085209356060259 := by
  unfold tailWord_6022109
  simp only [CollatzResearch.WordTrace]
  refine ⟨219644359739935062179693381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146429573159956708119795587 219644359739935062179693381)
  ·
    refine ⟨41183317451237824158692509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219644359739935062179693381 41183317451237824158692509)
    ·
      refine ⟨15443744044214184059509691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41183317451237824158692509 15443744044214184059509691)
      ·
        refine ⟨23165616066321276089264537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15443744044214184059509691 23165616066321276089264537)
        ·
          refine ⟨17374212049740957066948403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23165616066321276089264537 17374212049740957066948403)
          ·
            refine ⟨26061318074611435600422605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17374212049740957066948403 26061318074611435600422605)
            ·
              refine ⟨9772994277979288350158477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26061318074611435600422605 9772994277979288350158477)
              ·
                refine ⟨3664872854242233131309429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9772994277979288350158477 3664872854242233131309429)
                ·
                  refine ⟨343581830085209356060259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3664872854242233131309429 343581830085209356060259)
                  ·
                    rfl

theorem cell23_6022109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_6022109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022109 prefixEnd_6022109 := by exact prefixLift 6022109
  have htrace : WordTrace (prefixWord ++ tailWord_6022109) baseStart_6022109 baseEnd_6022109 := by
    simpa [prefixWord, tailWord_6022109, baseEnd_6022109] using wordTrace_append hprefix tailTrace_6022109
  have hstable : (prefixWord ++ tailWord_6022109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022109).length < 2 ^ (prefixWord ++ tailWord_6022109).sum := by decide
  have hdescent : baseEnd_6022109 < baseStart_6022109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022115 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 5]
def baseStart_6022115 : Nat := 118140960795 + 6022115 * 2 ^ 59
def prefixEnd_6022115 : Nat := 4983230072969 + 3 ^ 40 * 6022115 * 2
def baseEnd_6022115 : Nat := 3092239551650811181067303

theorem tailTrace_6022115 : CollatzResearch.WordTrace tailWord_6022115 prefixEnd_6022115 3092239551650811181067303 := by
  unfold tailWord_6022115
  simp only [CollatzResearch.WordTrace]
  refine ⟨219644578577913325204411799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146429719051942216802941199 219644578577913325204411799)
  ·
    refine ⟨329466867866869987806617699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219644578577913325204411799 329466867866869987806617699)
    ·
      refine ⟨494200301800304981709926549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329466867866869987806617699 494200301800304981709926549)
      ·
        refine ⟨23165639146889296017652807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 494200301800304981709926549 23165639146889296017652807)
        ·
          refine ⟨34748458720333944026479211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23165639146889296017652807 34748458720333944026479211)
          ·
            refine ⟨52122688080500916039718817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34748458720333944026479211 52122688080500916039718817)
            ·
              refine ⟨39092016060375687029789113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52122688080500916039718817 39092016060375687029789113)
              ·
                refine ⟨29319012045281765272341835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39092016060375687029789113 29319012045281765272341835)
                ·
                  refine ⟨43978518067922647908512753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29319012045281765272341835 43978518067922647908512753)
                  ·
                    refine ⟨32983888550941985931384565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43978518067922647908512753 32983888550941985931384565)
                    ·
                      refine ⟨3092239551650811181067303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32983888550941985931384565 3092239551650811181067303)
                      ·
                        rfl

theorem cell23_6022115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_6022115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022115 prefixEnd_6022115 := by exact prefixLift 6022115
  have htrace : WordTrace (prefixWord ++ tailWord_6022115) baseStart_6022115 baseEnd_6022115 := by
    simpa [prefixWord, tailWord_6022115, baseEnd_6022115] using wordTrace_append hprefix tailTrace_6022115
  have hstable : (prefixWord ++ tailWord_6022115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022115).length < 2 ^ (prefixWord ++ tailWord_6022115).sum := by decide
  have hdescent : baseEnd_6022115 < baseStart_6022115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022122 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_6022122 : Nat := 118140960795 + 6022122 * 2 ^ 59
def prefixEnd_6022122 : Nat := 4983230072969 + 3 ^ 40 * 6022122 * 2
def baseEnd_6022122 : Nat := 1030747715338464217893257

theorem tailTrace_6022122 : CollatzResearch.WordTrace tailWord_6022122 prefixEnd_6022122 1030747715338464217893257 := by
  unfold tailWord_6022122
  simp only [CollatzResearch.WordTrace]
  refine ⟨54911208472221991349979155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146429889259258643599944413 54911208472221991349979155)
  ·
    refine ⟨82366812708332987024968733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54911208472221991349979155 82366812708332987024968733)
    ·
      refine ⟨30887554765624870134363275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82366812708332987024968733 30887554765624870134363275)
      ·
        refine ⟨46331332148437305201544913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30887554765624870134363275 46331332148437305201544913)
        ·
          refine ⟨34748499111327978901158685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46331332148437305201544913 34748499111327978901158685)
          ·
            refine ⟨13030687166747992087934507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34748499111327978901158685 13030687166747992087934507)
            ·
              refine ⟨19546030750121988131901761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13030687166747992087934507 19546030750121988131901761)
              ·
                refine ⟨14659523062591491098926321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19546030750121988131901761 14659523062591491098926321)
                ·
                  refine ⟨10994642296943618324194741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14659523062591491098926321 10994642296943618324194741)
                  ·
                    refine ⟨1030747715338464217893257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10994642296943618324194741 1030747715338464217893257)
                    ·
                      rfl

theorem cell23_6022122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_6022122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022122 prefixEnd_6022122 := by exact prefixLift 6022122
  have htrace : WordTrace (prefixWord ++ tailWord_6022122) baseStart_6022122 baseEnd_6022122 := by
    simpa [prefixWord, tailWord_6022122, baseEnd_6022122] using wordTrace_append hprefix tailTrace_6022122
  have hstable : (prefixWord ++ tailWord_6022122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022122).length < 2 ^ (prefixWord ++ tailWord_6022122).sum := by decide
  have hdescent : baseEnd_6022122 < baseStart_6022122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022126 : List Nat := [4, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_6022126 : Nat := 118140960795 + 6022126 * 2 ^ 59
def prefixEnd_6022126 : Nat := 4983230072969 + 3 ^ 40 * 6022126 * 2
def baseEnd_6022126 : Nat := 343582799993112293114417

theorem tailTrace_6022126 : CollatzResearch.WordTrace tailWord_6022126 prefixEnd_6022126 343582799993112293114417 := by
  unfold tailWord_6022126
  simp only [CollatzResearch.WordTrace]
  refine ⟨27455622472609184260382779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146429986520582316055374821 27455622472609184260382779)
  ·
    refine ⟨41183433708913776390574169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27455622472609184260382779 41183433708913776390574169)
    ·
      refine ⟨30887575281685332292930627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41183433708913776390574169 30887575281685332292930627)
      ·
        refine ⟨46331362922527998439395941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30887575281685332292930627 46331362922527998439395941)
        ·
          refine ⟨8687130547973999707386739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46331362922527998439395941 8687130547973999707386739)
          ·
            refine ⟨13030695821960999561080109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8687130547973999707386739 13030695821960999561080109)
            ·
              refine ⟨4886510933235374835405041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13030695821960999561080109 4886510933235374835405041)
              ·
                refine ⟨3664883199926531126553781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4886510933235374835405041 3664883199926531126553781)
                ·
                  refine ⟨343582799993112293114417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3664883199926531126553781 343582799993112293114417)
                  ·
                    rfl

theorem cell23_6022126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_6022126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022126 prefixEnd_6022126 := by exact prefixLift 6022126
  have htrace : WordTrace (prefixWord ++ tailWord_6022126) baseStart_6022126 baseEnd_6022126 := by
    simpa [prefixWord, tailWord_6022126, baseEnd_6022126] using wordTrace_append hprefix tailTrace_6022126
  have hstable : (prefixWord ++ tailWord_6022126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022126).length < 2 ^ (prefixWord ++ tailWord_6022126).sum := by decide
  have hdescent : baseEnd_6022126 < baseStart_6022126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022252 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_6022252 : Nat := 118140960795 + 6022252 * 2 ^ 59
def prefixEnd_6022252 : Nat := 4983230072969 + 3 ^ 40 * 6022252 * 2
def baseEnd_6022252 : Nat := 3092309898500477145054173

theorem tailTrace_6022252 : CollatzResearch.WordTrace tailWord_6022252 prefixEnd_6022252 3092309898500477145054173 := by
  unfold tailWord_6022252
  simp only [CollatzResearch.WordTrace]
  refine ⟨109824787689208498801074505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146433050252277998401432673 109824787689208498801074505)
  ·
    refine ⟨82368590766906374100805879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109824787689208498801074505 82368590766906374100805879)
    ·
      refine ⟨123552886150359561151208819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82368590766906374100805879 123552886150359561151208819)
      ·
        refine ⟨185329329225539341726813229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123552886150359561151208819 185329329225539341726813229)
        ·
          refine ⟨69498498459577253147554961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185329329225539341726813229 69498498459577253147554961)
          ·
            refine ⟨52123873844682939860666221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69498498459577253147554961 52123873844682939860666221)
            ·
              refine ⟨19546452691756102447749833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52123873844682939860666221 19546452691756102447749833)
              ·
                refine ⟨14659839518817076835812375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19546452691756102447749833 14659839518817076835812375)
                ·
                  refine ⟨21989759278225615253718563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14659839518817076835812375 21989759278225615253718563)
                  ·
                    refine ⟨32984638917338422880577845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21989759278225615253718563 32984638917338422880577845)
                    ·
                      refine ⟨3092309898500477145054173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32984638917338422880577845 3092309898500477145054173)
                      ·
                        rfl

theorem cell23_6022252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_6022252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022252 prefixEnd_6022252 := by exact prefixLift 6022252
  have htrace : WordTrace (prefixWord ++ tailWord_6022252) baseStart_6022252 baseEnd_6022252 := by
    simpa [prefixWord, tailWord_6022252, baseEnd_6022252] using wordTrace_append hprefix tailTrace_6022252
  have hstable : (prefixWord ++ tailWord_6022252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022252).length < 2 ^ (prefixWord ++ tailWord_6022252).sum := by decide
  have hdescent : baseEnd_6022252 < baseStart_6022252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022255 : List Nat := [1, 1, 2, 1, 3, 3, 2, 10]
def baseStart_6022255 : Nat := 118140960795 + 6022255 * 2 ^ 59
def prefixEnd_6022255 : Nat := 4983230072969 + 3 ^ 40 * 6022255 * 2
def baseEnd_6022255 : Nat := 114530053294164467900617

theorem tailTrace_6022255 : CollatzResearch.WordTrace tailWord_6022255 prefixEnd_6022255 114530053294164467900617 := by
  unfold tailWord_6022255
  simp only [CollatzResearch.WordTrace]
  refine ⟨219649684797406129114508219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146433123198270752743005479 219649684797406129114508219)
  ·
    refine ⟨329474527196109193671762329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219649684797406129114508219 329474527196109193671762329)
    ·
      refine ⟨247105895397081895253821747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329474527196109193671762329 247105895397081895253821747)
      ·
        refine ⟨370658843095622842880732621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247105895397081895253821747 370658843095622842880732621)
        ·
          refine ⟨138997066160858566080274733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370658843095622842880732621 138997066160858566080274733)
          ·
            refine ⟨52123899810321962280103025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138997066160858566080274733 52123899810321962280103025)
            ·
              refine ⟨39092924857741471710077269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52123899810321962280103025 39092924857741471710077269)
              ·
                refine ⟨114530053294164467900617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39092924857741471710077269 114530053294164467900617)
                ·
                  rfl

theorem cell23_6022255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 10].length) (baseStart_6022255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022255 prefixEnd_6022255 := by exact prefixLift 6022255
  have htrace : WordTrace (prefixWord ++ tailWord_6022255) baseStart_6022255 baseEnd_6022255 := by
    simpa [prefixWord, tailWord_6022255, baseEnd_6022255] using wordTrace_append hprefix tailTrace_6022255
  have hstable : (prefixWord ++ tailWord_6022255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022255).length < 2 ^ (prefixWord ++ tailWord_6022255).sum := by decide
  have hdescent : baseEnd_6022255 < baseStart_6022255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022272 : List Nat := [2, 1, 1, 2, 1, 3, 6, 7]
def baseStart_6022272 : Nat := 118140960795 + 6022272 * 2 ^ 59
def prefixEnd_6022272 : Nat := 4983230072969 + 3 ^ 40 * 6022272 * 2
def baseEnd_6022272 : Nat := 114530376596798780252003

theorem tailTrace_6022272 : CollatzResearch.WordTrace tailWord_6022272 prefixEnd_6022272 114530376596798780252003 := by
  unfold tailWord_6022272
  simp only [CollatzResearch.WordTrace]
  refine ⟨109825152419172270508938535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146433536558896360678584713 109825152419172270508938535)
  ·
    refine ⟨164737728628758405763407803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109825152419172270508938535 164737728628758405763407803)
    ·
      refine ⟨247106592943137608645111705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164737728628758405763407803 247106592943137608645111705)
      ·
        refine ⟨185329944707353206483833779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247106592943137608645111705 185329944707353206483833779)
        ·
          refine ⟨277994917061029809725750669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185329944707353206483833779 277994917061029809725750669)
          ·
            refine ⟨104248093897886178647156501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277994917061029809725750669 104248093897886178647156501)
            ·
              refine ⟨4886629401463414624085461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104248093897886178647156501 4886629401463414624085461)
              ·
                refine ⟨114530376596798780252003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4886629401463414624085461 114530376596798780252003)
                ·
                  rfl

theorem cell23_6022272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 7].length) (baseStart_6022272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022272 prefixEnd_6022272 := by exact prefixLift 6022272
  have htrace : WordTrace (prefixWord ++ tailWord_6022272) baseStart_6022272 baseEnd_6022272 := by
    simpa [prefixWord, tailWord_6022272, baseEnd_6022272] using wordTrace_append hprefix tailTrace_6022272
  have hstable : (prefixWord ++ tailWord_6022272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022272).length < 2 ^ (prefixWord ++ tailWord_6022272).sum := by decide
  have hdescent : baseEnd_6022272 < baseStart_6022272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022286 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_6022286 : Nat := 118140960795 + 6022286 * 2 ^ 59
def prefixEnd_6022286 : Nat := 4983230072969 + 3 ^ 40 * 6022286 * 2
def baseEnd_6022286 : Nat := 3092327356842730012029017

theorem tailTrace_6022286 : CollatzResearch.WordTrace tailWord_6022286 prefixEnd_6022286 3092327356842730012029017 := by
  unfold tailWord_6022286
  simp only [CollatzResearch.WordTrace]
  refine ⟨27456351932536727676110839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146433876973529214272591141 27456351932536727676110839)
  ·
    refine ⟨41184527898805091514166259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27456351932536727676110839 41184527898805091514166259)
    ·
      refine ⟨61776791848207637271249389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41184527898805091514166259 61776791848207637271249389)
      ·
        refine ⟨23166296943077863976718521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61776791848207637271249389 23166296943077863976718521)
        ·
          refine ⟨17374722707308397982538891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23166296943077863976718521 17374722707308397982538891)
          ·
            refine ⟨26062084060962596973808337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17374722707308397982538891 26062084060962596973808337)
            ·
              refine ⟨19546563045721947730356253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26062084060962596973808337 19546563045721947730356253)
              ·
                refine ⟨7329961142145730398883595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19546563045721947730356253 7329961142145730398883595)
                ·
                  refine ⟨10994941713218595598325393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7329961142145730398883595 10994941713218595598325393)
                  ·
                    refine ⟨8246206284913946698744045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10994941713218595598325393 8246206284913946698744045)
                    ·
                      refine ⟨3092327356842730012029017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8246206284913946698744045 3092327356842730012029017)
                      ·
                        rfl

theorem cell23_6022286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_6022286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022286 prefixEnd_6022286 := by exact prefixLift 6022286
  have htrace : WordTrace (prefixWord ++ tailWord_6022286) baseStart_6022286 baseEnd_6022286 := by
    simpa [prefixWord, tailWord_6022286, baseEnd_6022286] using wordTrace_append hprefix tailTrace_6022286
  have hstable : (prefixWord ++ tailWord_6022286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022286).length < 2 ^ (prefixWord ++ tailWord_6022286).sum := by decide
  have hdescent : baseEnd_6022286 < baseStart_6022286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022362 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 7]
def baseStart_6022362 : Nat := 118140960795 + 6022362 * 2 ^ 59
def prefixEnd_6022362 : Nat := 4983230072969 + 3 ^ 40 * 6022362 * 2
def baseEnd_6022362 : Nat := 343596264596941301630963

theorem tailTrace_6022362 : CollatzResearch.WordTrace tailWord_6022362 prefixEnd_6022362 343596264596941301630963 := by
  unfold tailWord_6022362
  simp only [CollatzResearch.WordTrace]
  refine ⟨54913396852004621597163335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146435724938678990925768893 54913396852004621597163335)
  ·
    refine ⟨82370095278006932395745003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54913396852004621597163335 82370095278006932395745003)
    ·
      refine ⟨123555142917010398593617505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82370095278006932395745003 123555142917010398593617505)
      ·
        refine ⟨92666357187757798945213129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123555142917010398593617505 92666357187757798945213129)
        ·
          refine ⟨69499767890818349208909847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92666357187757798945213129 69499767890818349208909847)
          ·
            refine ⟨104249651836227523813364771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69499767890818349208909847 104249651836227523813364771)
            ·
              refine ⟨156374477754341285720047157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104249651836227523813364771 156374477754341285720047157)
              ·
                refine ⟨14660107289469495536254421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156374477754341285720047157 14660107289469495536254421)
                ·
                  refine ⟨343596264596941301630963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14660107289469495536254421 343596264596941301630963)
                  ·
                    rfl

theorem cell23_6022362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_6022362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022362 prefixEnd_6022362 := by exact prefixLift 6022362
  have htrace : WordTrace (prefixWord ++ tailWord_6022362) baseStart_6022362 baseEnd_6022362 := by
    simpa [prefixWord, tailWord_6022362, baseEnd_6022362] using wordTrace_append hprefix tailTrace_6022362
  have hstable : (prefixWord ++ tailWord_6022362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022362).length < 2 ^ (prefixWord ++ tailWord_6022362).sum := by decide
  have hdescent : baseEnd_6022362 < baseStart_6022362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022369 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_6022369 : Nat := 118140960795 + 6022369 * 2 ^ 59
def prefixEnd_6022369 : Nat := 4983230072969 + 3 ^ 40 * 6022369 * 2
def baseEnd_6022369 : Nat := 3092369975737053187291135

theorem tailTrace_6022369 : CollatzResearch.WordTrace tailWord_6022369 prefixEnd_6022369 3092369975737053187291135 := by
  unfold tailWord_6022369
  simp only [CollatzResearch.WordTrace]
  refine ⟨219653842718993126584158161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146435895145995417722772107 219653842718993126584158161)
  ·
    refine ⟨164740382039244844938118621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219653842718993126584158161 164740382039244844938118621)
    ·
      refine ⟨61777643264716816851794483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164740382039244844938118621 61777643264716816851794483)
      ·
        refine ⟨92666464897075225277691725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61777643264716816851794483 92666464897075225277691725)
        ·
          refine ⟨34749924336403209479134397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92666464897075225277691725 34749924336403209479134397)
          ·
            refine ⟨13031221626151203554675399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34749924336403209479134397 13031221626151203554675399)
            ·
              refine ⟨19546832439226805332013099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13031221626151203554675399 19546832439226805332013099)
              ·
                refine ⟨29320248658840207998019649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19546832439226805332013099 29320248658840207998019649)
                ·
                  refine ⟨21990186494130155998514737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29320248658840207998019649 21990186494130155998514737)
                  ·
                    refine ⟨16492639870597616998886053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21990186494130155998514737 16492639870597616998886053)
                    ·
                      refine ⟨3092369975737053187291135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16492639870597616998886053 3092369975737053187291135)
                      ·
                        rfl

theorem cell23_6022369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_6022369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022369 prefixEnd_6022369 := by exact prefixLift 6022369
  have htrace : WordTrace (prefixWord ++ tailWord_6022369) baseStart_6022369 baseEnd_6022369 := by
    simpa [prefixWord, tailWord_6022369, baseEnd_6022369] using wordTrace_append hprefix tailTrace_6022369
  have hstable : (prefixWord ++ tailWord_6022369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022369).length < 2 ^ (prefixWord ++ tailWord_6022369).sum := by decide
  have hdescent : baseEnd_6022369 < baseStart_6022369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022373 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 1, 4, 2]
def baseStart_6022373 : Nat := 118140960795 + 6022373 * 2 ^ 59
def prefixEnd_6022373 : Nat := 4983230072969 + 3 ^ 40 * 6022373 * 2
def baseEnd_6022373 : Nat := 3092372029659671171641117

theorem tailTrace_6022373 : CollatzResearch.WordTrace tailWord_6022373 prefixEnd_6022373 3092372029659671171641117 := by
  unfold tailWord_6022373
  simp only [CollatzResearch.WordTrace]
  refine ⟨219653988610978635267303773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146435992407319090178202515 219653988610978635267303773)
  ·
    refine ⟨82370245729116988225238915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219653988610978635267303773 82370245729116988225238915)
    ·
      refine ⟨123555368593675482337858373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82370245729116988225238915 123555368593675482337858373)
      ·
        refine ⟨23166631611314152938348445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123555368593675482337858373 23166631611314152938348445)
        ·
          refine ⟨8687486854242807351880667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23166631611314152938348445 8687486854242807351880667)
          ·
            refine ⟨13031230281364211027821001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8687486854242807351880667 13031230281364211027821001)
            ·
              refine ⟨9773422711023158270865751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13031230281364211027821001 9773422711023158270865751)
              ·
                refine ⟨14660134066534737406298627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9773422711023158270865751 14660134066534737406298627)
                ·
                  refine ⟨21990201099802106109447941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14660134066534737406298627 21990201099802106109447941)
                  ·
                    refine ⟨4123162706212894895521489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21990201099802106109447941 4123162706212894895521489)
                    ·
                      refine ⟨3092372029659671171641117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123162706212894895521489 3092372029659671171641117)
                      ·
                        rfl

theorem cell23_6022373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_6022373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022373 prefixEnd_6022373 := by exact prefixLift 6022373
  have htrace : WordTrace (prefixWord ++ tailWord_6022373) baseStart_6022373 baseEnd_6022373 := by
    simpa [prefixWord, tailWord_6022373, baseEnd_6022373] using wordTrace_append hprefix tailTrace_6022373
  have hstable : (prefixWord ++ tailWord_6022373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022373).length < 2 ^ (prefixWord ++ tailWord_6022373).sum := by decide
  have hdescent : baseEnd_6022373 < baseStart_6022373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022470 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6022470 : Nat := 118140960795 + 6022470 * 2 ^ 59
def prefixEnd_6022470 : Nat := 4983230072969 + 3 ^ 40 * 6022470 * 2
def baseEnd_6022470 : Nat := 3092421837283157292128171

theorem tailTrace_6022470 : CollatzResearch.WordTrace tailWord_6022470 prefixEnd_6022470 3092421837283157292128171 := by
  unfold tailWord_6022470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6864297702863350651049527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146438350994418147222389909 6864297702863350651049527)
  ·
    refine ⟨10296446554295025976574291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6864297702863350651049527 10296446554295025976574291)
    ·
      refine ⟨15444669831442538964861437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10296446554295025976574291 15444669831442538964861437)
      ·
        refine ⟨5791751186790952111823039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15444669831442538964861437 5791751186790952111823039)
        ·
          refine ⟨8687626780186428167734559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5791751186790952111823039 8687626780186428167734559)
          ·
            refine ⟨13031440170279642251601839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8687626780186428167734559 13031440170279642251601839)
            ·
              refine ⟨19547160255419463377402759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13031440170279642251601839 19547160255419463377402759)
              ·
                refine ⟨29320740383129195066104139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19547160255419463377402759 29320740383129195066104139)
                ·
                  refine ⟨43981110574693792599156209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29320740383129195066104139 43981110574693792599156209)
                  ·
                    refine ⟨32985832931020344449367157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43981110574693792599156209 32985832931020344449367157)
                    ·
                      refine ⟨3092421837283157292128171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32985832931020344449367157 3092421837283157292128171)
                      ·
                        rfl

theorem cell23_6022470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6022470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022470 prefixEnd_6022470 := by exact prefixLift 6022470
  have htrace : WordTrace (prefixWord ++ tailWord_6022470) baseStart_6022470 baseEnd_6022470 := by
    simpa [prefixWord, tailWord_6022470, baseEnd_6022470] using wordTrace_append hprefix tailTrace_6022470
  have hstable : (prefixWord ++ tailWord_6022470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022470).length < 2 ^ (prefixWord ++ tailWord_6022470).sum := by decide
  have hdescent : baseEnd_6022470 < baseStart_6022470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022536 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_6022536 : Nat := 118140960795 + 6022536 * 2 ^ 59
def prefixEnd_6022536 : Nat := 4983230072969 + 3 ^ 40 * 6022536 * 2
def baseEnd_6022536 : Nat := 3092455727006354033902867

theorem tailTrace_6022536 : CollatzResearch.WordTrace tailWord_6022536 prefixEnd_6022536 3092455727006354033902867 := by
  unfold tailWord_6022536
  simp only [CollatzResearch.WordTrace]
  refine ⟨109829966854694057052743731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146439955806258742736991641 109829966854694057052743731)
  ·
    refine ⟨164744950282041085579115597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109829966854694057052743731 164744950282041085579115597)
    ·
      refine ⟨61779356355765407092168349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164744950282041085579115597 61779356355765407092168349)
      ·
        refine ⟨23167258633412027659563131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61779356355765407092168349 23167258633412027659563131)
        ·
          refine ⟨34750887950118041489344697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23167258633412027659563131 34750887950118041489344697)
          ·
            refine ⟨26063165962588531117008523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34750887950118041489344697 26063165962588531117008523)
            ·
              refine ⟨39094748943882796675512785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26063165962588531117008523 39094748943882796675512785)
              ·
                refine ⟨29321061707912097506634589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39094748943882796675512785 29321061707912097506634589)
                ·
                  refine ⟨10995398140467036564987971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29321061707912097506634589 10995398140467036564987971)
                  ·
                    refine ⟨16493097210700554847481957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10995398140467036564987971 16493097210700554847481957)
                    ·
                      refine ⟨3092455727006354033902867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16493097210700554847481957 3092455727006354033902867)
                      ·
                        rfl

theorem cell23_6022536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_6022536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022536 prefixEnd_6022536 := by exact prefixLift 6022536
  have htrace : WordTrace (prefixWord ++ tailWord_6022536) baseStart_6022536 baseEnd_6022536 := by
    simpa [prefixWord, tailWord_6022536, baseEnd_6022536] using wordTrace_append hprefix tailTrace_6022536
  have hstable : (prefixWord ++ tailWord_6022536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022536).length < 2 ^ (prefixWord ++ tailWord_6022536).sum := by decide
  have hdescent : baseEnd_6022536 < baseStart_6022536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022539 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 5]
def baseStart_6022539 : Nat := 118140960795 + 6022539 * 2 ^ 59
def prefixEnd_6022539 : Nat := 4983230072969 + 3 ^ 40 * 6022539 * 2
def baseEnd_6022539 : Nat := 3092457267448317522165353

theorem tailTrace_6022539 : CollatzResearch.WordTrace tailWord_6022539 prefixEnd_6022539 3092457267448317522165353 := by
  unfold tailWord_6022539
  simp only [CollatzResearch.WordTrace]
  refine ⟨219660043128377245617846671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146440028752251497078564447 219660043128377245617846671)
  ·
    refine ⟨329490064692565868426770007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219660043128377245617846671 329490064692565868426770007)
    ·
      refine ⟨494235097038848802640155011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329490064692565868426770007 494235097038848802640155011)
      ·
        refine ⟨741352645558273203960232517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494235097038848802640155011 741352645558273203960232517)
        ·
          refine ⟨139003621042176225742543597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 741352645558273203960232517 139003621042176225742543597)
          ·
            refine ⟨52126357890816084653453849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139003621042176225742543597 52126357890816084653453849)
            ·
              refine ⟨39094768418112063490090387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52126357890816084653453849 39094768418112063490090387)
              ·
                refine ⟨58642152627168095235135581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39094768418112063490090387 58642152627168095235135581)
                ·
                  refine ⟨21990807235188035713175843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58642152627168095235135581 21990807235188035713175843)
                  ·
                    refine ⟨32986210852782053569763765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21990807235188035713175843 32986210852782053569763765)
                    ·
                      refine ⟨3092457267448317522165353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32986210852782053569763765 3092457267448317522165353)
                      ·
                        rfl

theorem cell23_6022539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 5].length) (baseStart_6022539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022539 prefixEnd_6022539 := by exact prefixLift 6022539
  have htrace : WordTrace (prefixWord ++ tailWord_6022539) baseStart_6022539 baseEnd_6022539 := by
    simpa [prefixWord, tailWord_6022539, baseEnd_6022539] using wordTrace_append hprefix tailTrace_6022539
  have hstable : (prefixWord ++ tailWord_6022539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022539).length < 2 ^ (prefixWord ++ tailWord_6022539).sum := by decide
  have hdescent : baseEnd_6022539 < baseStart_6022539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022549 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_6022549 : Nat := 118140960795 + 6022549 * 2 ^ 59
def prefixEnd_6022549 : Nat := 4983230072969 + 3 ^ 40 * 6022549 * 2
def baseEnd_6022549 : Nat := 3092462402254862483040307

theorem tailTrace_6022549 : CollatzResearch.WordTrace tailWord_6022549 prefixEnd_6022549 3092462402254862483040307 := by
  unfold tailWord_6022549
  simp only [CollatzResearch.WordTrace]
  refine ⟨219660407858341017325710701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146440271905560678217140467 219660407858341017325710701)
  ·
    refine ⟨82372652946877881497141513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219660407858341017325710701 82372652946877881497141513)
    ·
      refine ⟨61779489710158411122856135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82372652946877881497141513 61779489710158411122856135)
      ·
        refine ⟨92669234565237616684284203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61779489710158411122856135 92669234565237616684284203)
        ·
          refine ⟨139003851847856425026426305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92669234565237616684284203 139003851847856425026426305)
          ·
            refine ⟨104252888885892318769819729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139003851847856425026426305 104252888885892318769819729)
            ·
              refine ⟨78189666664419239077364797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104252888885892318769819729 78189666664419239077364797)
              ·
                refine ⟨29321124999157214654011799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78189666664419239077364797 29321124999157214654011799)
                ·
                  refine ⟨43981687498735821981017699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29321124999157214654011799 43981687498735821981017699)
                  ·
                    refine ⟨65972531248103732971526549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43981687498735821981017699 65972531248103732971526549)
                    ·
                      refine ⟨3092462402254862483040307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65972531248103732971526549 3092462402254862483040307)
                      ·
                        rfl

theorem cell23_6022549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_6022549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022549 prefixEnd_6022549 := by exact prefixLift 6022549
  have htrace : WordTrace (prefixWord ++ tailWord_6022549) baseStart_6022549 baseEnd_6022549 := by
    simpa [prefixWord, tailWord_6022549, baseEnd_6022549] using wordTrace_append hprefix tailTrace_6022549
  have hstable : (prefixWord ++ tailWord_6022549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022549).length < 2 ^ (prefixWord ++ tailWord_6022549).sum := by decide
  have hdescent : baseEnd_6022549 < baseStart_6022549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022553 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 5, 2, 2]
def baseStart_6022553 : Nat := 118140960795 + 6022553 * 2 ^ 59
def prefixEnd_6022553 : Nat := 4983230072969 + 3 ^ 40 * 6022553 * 2
def baseEnd_6022553 : Nat := 3092464456177480467390289

theorem tailTrace_6022553 : CollatzResearch.WordTrace tailWord_6022553 prefixEnd_6022553 3092464456177480467390289 := by
  unfold tailWord_6022553
  simp only [CollatzResearch.WordTrace]
  refine ⟨219660553750326526008856313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146440369166884350672570875 219660553750326526008856313)
  ·
    refine ⟨164745415312744894506642235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219660553750326526008856313 164745415312744894506642235)
    ·
      refine ⟨247118122969117341759963353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164745415312744894506642235 247118122969117341759963353)
      ·
        refine ⟨185338592226838006319972515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247118122969117341759963353 185338592226838006319972515)
        ·
          refine ⟨278007888340257009479958773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185338592226838006319972515 278007888340257009479958773)
          ·
            refine ⟨26063239531899094638746135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278007888340257009479958773 26063239531899094638746135)
            ·
              refine ⟨39094859297848641958119203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26063239531899094638746135 39094859297848641958119203)
              ·
                refine ⟨58642288946772962937178805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39094859297848641958119203 58642288946772962937178805)
                ·
                  refine ⟨5497714588759965275360513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58642288946772962937178805 5497714588759965275360513)
                  ·
                    refine ⟨4123285941569973956520385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5497714588759965275360513 4123285941569973956520385)
                    ·
                      refine ⟨3092464456177480467390289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123285941569973956520385 3092464456177480467390289)
                      ·
                        rfl

theorem cell23_6022553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_6022553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022553 prefixEnd_6022553 := by exact prefixLift 6022553
  have htrace : WordTrace (prefixWord ++ tailWord_6022553) baseStart_6022553 baseEnd_6022553 := by
    simpa [prefixWord, tailWord_6022553, baseEnd_6022553] using wordTrace_append hprefix tailTrace_6022553
  have hstable : (prefixWord ++ tailWord_6022553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022553).length < 2 ^ (prefixWord ++ tailWord_6022553).sum := by decide
  have hdescent : baseEnd_6022553 < baseStart_6022553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022603 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 2, 1, 3]
def baseStart_6022603 : Nat := 118140960795 + 6022603 * 2 ^ 59
def prefixEnd_6022603 : Nat := 4983230072969 + 3 ^ 40 * 6022603 * 2
def baseEnd_6022603 : Nat := 3092490130210205271765059

theorem tailTrace_6022603 : CollatzResearch.WordTrace tailWord_6022603 prefixEnd_6022603 3092490130210205271765059 := by
  unfold tailWord_6022603
  simp only [CollatzResearch.WordTrace]
  refine ⟨219662377400145384548176463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146441584933430256365450975 219662377400145384548176463)
  ·
    refine ⟨329493566100218076822264695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219662377400145384548176463 329493566100218076822264695)
    ·
      refine ⟨494240349150327115233397043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329493566100218076822264695 494240349150327115233397043)
      ·
        refine ⟨741360523725490672850095565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494240349150327115233397043 741360523725490672850095565)
        ·
          refine ⟨278010196397059002318785837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 741360523725490672850095565 278010196397059002318785837)
          ·
            refine ⟨104253823648897125869544689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278010196397059002318785837 104253823648897125869544689)
            ·
              refine ⟨78190367736672844402158517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104253823648897125869544689 78190367736672844402158517)
              ·
                refine ⟨7330346975313079162702361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78190367736672844402158517 7330346975313079162702361)
                ·
                  refine ⟨5497760231484809372026771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7330346975313079162702361 5497760231484809372026771)
                  ·
                    refine ⟨8246640347227214058040157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5497760231484809372026771 8246640347227214058040157)
                    ·
                      refine ⟨3092490130210205271765059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8246640347227214058040157 3092490130210205271765059)
                      ·
                        rfl

theorem cell23_6022603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 1, 3].length) (baseStart_6022603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022603 prefixEnd_6022603 := by exact prefixLift 6022603
  have htrace : WordTrace (prefixWord ++ tailWord_6022603) baseStart_6022603 baseEnd_6022603 := by
    simpa [prefixWord, tailWord_6022603, baseEnd_6022603] using wordTrace_append hprefix tailTrace_6022603
  have hstable : (prefixWord ++ tailWord_6022603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022603).length < 2 ^ (prefixWord ++ tailWord_6022603).sum := by decide
  have hdescent : baseEnd_6022603 < baseStart_6022603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022654 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6022654 : Nat := 118140960795 + 6022654 * 2 ^ 59
def prefixEnd_6022654 : Nat := 4983230072969 + 3 ^ 40 * 6022654 * 2
def baseEnd_6022654 : Nat := 3092516317723584572227325

theorem tailTrace_6022654 : CollatzResearch.WordTrace tailWord_6022654 prefixEnd_6022654 3092516317723584572227325 := by
  unfold tailWord_6022654
  simp only [CollatzResearch.WordTrace]
  refine ⟨27458029690370077532285377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146442825015307080172188677 27458029690370077532285377)
  ·
    refine ⟨20593522267777558149214033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27458029690370077532285377 20593522267777558149214033)
    ·
      refine ⟨15445141700833168611910525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20593522267777558149214033 15445141700833168611910525)
      ·
        refine ⟨5791928137812438229466447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15445141700833168611910525 5791928137812438229466447)
        ·
          refine ⟨8687892206718657344199671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5791928137812438229466447 8687892206718657344199671)
          ·
            refine ⟨13031838310077986016299507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8687892206718657344199671 13031838310077986016299507)
            ·
              refine ⟨19547757465116979024449261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13031838310077986016299507 19547757465116979024449261)
              ·
                refine ⟨7330409049418867134168473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19547757465116979024449261 7330409049418867134168473)
                ·
                  refine ⟨5497806787064150350626355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7330409049418867134168473 5497806787064150350626355)
                  ·
                    refine ⟨8246710180596225525939533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5497806787064150350626355 8246710180596225525939533)
                    ·
                      refine ⟨3092516317723584572227325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8246710180596225525939533 3092516317723584572227325)
                      ·
                        rfl

theorem cell23_6022654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6022654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022654 prefixEnd_6022654 := by exact prefixLift 6022654
  have htrace : WordTrace (prefixWord ++ tailWord_6022654) baseStart_6022654 baseEnd_6022654 := by
    simpa [prefixWord, tailWord_6022654, baseEnd_6022654] using wordTrace_append hprefix tailTrace_6022654
  have hstable : (prefixWord ++ tailWord_6022654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022654).length < 2 ^ (prefixWord ++ tailWord_6022654).sum := by decide
  have hdescent : baseEnd_6022654 < baseStart_6022654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022746 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_6022746 : Nat := 118140960795 + 6022746 * 2 ^ 59
def prefixEnd_6022746 : Nat := 4983230072969 + 3 ^ 40 * 6022746 * 2
def baseEnd_6022746 : Nat := 3092563557943798212276901

theorem tailTrace_6022746 : CollatzResearch.WordTrace tailWord_6022746 prefixEnd_6022746 3092563557943798212276901 := by
  unfold tailWord_6022746
  simp only [CollatzResearch.WordTrace]
  refine ⟨54916898259656829992658023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146445062025751546647088061 54916898259656829992658023)
  ·
    refine ⟨82375347389485244988987035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54916898259656829992658023 82375347389485244988987035)
    ·
      refine ⟨123563021084227867483480553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82375347389485244988987035 123563021084227867483480553)
      ·
        refine ⟨92672265813170900612610415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123563021084227867483480553 92672265813170900612610415)
        ·
          refine ⟨139008398719756350918915623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92672265813170900612610415 139008398719756350918915623)
          ·
            refine ⟨208512598079634526378373435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139008398719756350918915623 208512598079634526378373435)
            ·
              refine ⟨312768897119451789567560153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208512598079634526378373435 312768897119451789567560153)
              ·
                refine ⟨234576672839588842175670115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312768897119451789567560153 234576672839588842175670115)
                ·
                  refine ⟨351865009259383263263505173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234576672839588842175670115 351865009259383263263505173)
                  ·
                    refine ⟨16493672309033590465476805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 351865009259383263263505173 16493672309033590465476805)
                    ·
                      refine ⟨3092563557943798212276901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16493672309033590465476805 3092563557943798212276901)
                      ·
                        rfl

theorem cell23_6022746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_6022746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022746 prefixEnd_6022746 := by exact prefixLift 6022746
  have htrace : WordTrace (prefixWord ++ tailWord_6022746) baseStart_6022746 baseEnd_6022746 := by
    simpa [prefixWord, tailWord_6022746, baseEnd_6022746] using wordTrace_append hprefix tailTrace_6022746
  have hstable : (prefixWord ++ tailWord_6022746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022746).length < 2 ^ (prefixWord ++ tailWord_6022746).sum := by decide
  have hdescent : baseEnd_6022746 < baseStart_6022746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022753 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_6022753 : Nat := 118140960795 + 6022753 * 2 ^ 59
def prefixEnd_6022753 : Nat := 4983230072969 + 3 ^ 40 * 6022753 * 2
def baseEnd_6022753 : Nat := 3092567152308379684889369

theorem tailTrace_6022753 : CollatzResearch.WordTrace tailWord_6022753 prefixEnd_6022753 3092567152308379684889369 := by
  unfold tailWord_6022753
  simp only [CollatzResearch.WordTrace]
  refine ⟨219667848349601960166136913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146445232233067973444091275 219667848349601960166136913)
  ·
    refine ⟨164750886262201470124602685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219667848349601960166136913 164750886262201470124602685)
    ·
      refine ⟨61781582348325551296726007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164750886262201470124602685 61781582348325551296726007)
      ·
        refine ⟨92672373522488326945089011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61781582348325551296726007 92672373522488326945089011)
        ·
          refine ⟨139008560283732490417633517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92672373522488326945089011 139008560283732490417633517)
          ·
            refine ⟨52128210106399683906612569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139008560283732490417633517 52128210106399683906612569)
            ·
              refine ⟨39096157579799762929959427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52128210106399683906612569 39096157579799762929959427)
              ·
                refine ⟨58644236369699644394939141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39096157579799762929959427 58644236369699644394939141)
                ·
                  refine ⟨10995794319318683324051089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58644236369699644394939141 10995794319318683324051089)
                  ·
                    refine ⟨8246845739489012493038317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10995794319318683324051089 8246845739489012493038317)
                    ·
                      refine ⟨3092567152308379684889369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8246845739489012493038317 3092567152308379684889369)
                      ·
                        rfl

theorem cell23_6022753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_6022753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022753 prefixEnd_6022753 := by exact prefixLift 6022753
  have htrace : WordTrace (prefixWord ++ tailWord_6022753) baseStart_6022753 baseEnd_6022753 := by
    simpa [prefixWord, tailWord_6022753, baseEnd_6022753] using wordTrace_append hprefix tailTrace_6022753
  have hstable : (prefixWord ++ tailWord_6022753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022753).length < 2 ^ (prefixWord ++ tailWord_6022753).sum := by decide
  have hdescent : baseEnd_6022753 < baseStart_6022753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022760 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 3, 4]
def baseStart_6022760 : Nat := 118140960795 + 6022760 * 2 ^ 59
def prefixEnd_6022760 : Nat := 4983230072969 + 3 ^ 40 * 6022760 * 2
def baseEnd_6022760 : Nat := 1030856915557653719167279

theorem tailTrace_6022760 : CollatzResearch.WordTrace tailWord_6022760 prefixEnd_6022760 1030856915557653719167279 := by
  unfold tailWord_6022760
  simp only [CollatzResearch.WordTrace]
  refine ⟨109834051830288300180820867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146445402440384400241094489 109834051830288300180820867)
  ·
    refine ⟨164751077745432450271231301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109834051830288300180820867 164751077745432450271231301)
    ·
      refine ⟨30890827077268584425855869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164751077745432450271231301 30890827077268584425855869)
      ·
        refine ⟨11584060153975719159695951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30890827077268584425855869 11584060153975719159695951)
        ·
          refine ⟨17376090230963578739543927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11584060153975719159695951 17376090230963578739543927)
          ·
            refine ⟨26064135346445368109315891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17376090230963578739543927 26064135346445368109315891)
            ·
              refine ⟨39096203019668052163973837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26064135346445368109315891 39096203019668052163973837)
              ·
                refine ⟨14661076132375519561490189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39096203019668052163973837 14661076132375519561490189)
                ·
                  refine ⟨5497903549640819835558821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14661076132375519561490189 5497903549640819835558821)
                  ·
                    refine ⟨1030856915557653719167279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5497903549640819835558821 1030856915557653719167279)
                    ·
                      rfl

theorem cell23_6022760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_6022760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022760 prefixEnd_6022760 := by exact prefixLift 6022760
  have htrace : WordTrace (prefixWord ++ tailWord_6022760) baseStart_6022760 baseEnd_6022760 := by
    simpa [prefixWord, tailWord_6022760, baseEnd_6022760] using wordTrace_append hprefix tailTrace_6022760
  have hstable : (prefixWord ++ tailWord_6022760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022760).length < 2 ^ (prefixWord ++ tailWord_6022760).sum := by decide
  have hdescent : baseEnd_6022760 < baseStart_6022760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022794 : List Nat := [3, 1, 2, 3, 2, 3, 1, 3, 1, 4]
def baseStart_6022794 : Nat := 118140960795 + 6022794 * 2 ^ 59
def prefixEnd_6022794 : Nat := 4983230072969 + 3 ^ 40 * 6022794 * 2
def baseEnd_6022794 : Nat := 1030862735005071341492227

theorem tailTrace_6022794 : CollatzResearch.WordTrace tailWord_6022794 prefixEnd_6022794 1030862735005071341492227 := by
  unfold tailWord_6022794
  simp only [CollatzResearch.WordTrace]
  refine ⟨54917335935613356042094859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146446229161635616112252957 54917335935613356042094859)
  ·
    refine ⟨82376003903420034063142289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54917335935613356042094859 82376003903420034063142289)
    ·
      refine ⟨61782002927565025547356717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82376003903420034063142289 61782002927565025547356717)
      ·
        refine ⟨23168251097836884580258769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61782002927565025547356717 23168251097836884580258769)
        ·
          refine ⟨17376188323377663435194077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23168251097836884580258769 17376188323377663435194077)
          ·
            refine ⟨6516070621266623788197779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17376188323377663435194077 6516070621266623788197779)
            ·
              refine ⟨9774105931899935682296669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6516070621266623788197779 9774105931899935682296669)
              ·
                refine ⟨3665289724462475880861251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9774105931899935682296669 3665289724462475880861251)
                ·
                  refine ⟨5497934586693713821291877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665289724462475880861251 5497934586693713821291877)
                  ·
                    refine ⟨1030862735005071341492227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5497934586693713821291877 1030862735005071341492227)
                    ·
                      rfl

theorem cell23_6022794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_6022794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022794 prefixEnd_6022794 := by exact prefixLift 6022794
  have htrace : WordTrace (prefixWord ++ tailWord_6022794) baseStart_6022794 baseEnd_6022794 := by
    simpa [prefixWord, tailWord_6022794, baseEnd_6022794] using wordTrace_append hprefix tailTrace_6022794
  have hstable : (prefixWord ++ tailWord_6022794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022794).length < 2 ^ (prefixWord ++ tailWord_6022794).sum := by decide
  have hdescent : baseEnd_6022794 < baseStart_6022794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022817 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_6022817 : Nat := 118140960795 + 6022817 * 2 ^ 59
def prefixEnd_6022817 : Nat := 4983230072969 + 3 ^ 40 * 6022817 * 2
def baseEnd_6022817 : Nat := 3092600015070267434489075

theorem tailTrace_6022817 : CollatzResearch.WordTrace tailWord_6022817 prefixEnd_6022817 3092600015070267434489075 := by
  unfold tailWord_6022817
  simp only [CollatzResearch.WordTrace]
  refine ⟨219670182621370099096466705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146446788414246732730977803 219670182621370099096466705)
  ·
    refine ⟨164752636966027574322350029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219670182621370099096466705 164752636966027574322350029)
    ·
      refine ⟨61782238862260340370881261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164752636966027574322350029 61782238862260340370881261)
      ·
        refine ⟨23168339573347627639080473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61782238862260340370881261 23168339573347627639080473)
        ·
          refine ⟨17376254680010720729310355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23168339573347627639080473 17376254680010720729310355)
          ·
            refine ⟨26064382020016081093965533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17376254680010720729310355 26064382020016081093965533)
            ·
              refine ⟨9774143257506030410237075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26064382020016081093965533 9774143257506030410237075)
              ·
                refine ⟨14661214886259045615355613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9774143257506030410237075 14661214886259045615355613)
                ·
                  refine ⟨5497955582347142105758355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14661214886259045615355613 5497955582347142105758355)
                  ·
                    refine ⟨8246933373520713158637533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5497955582347142105758355 8246933373520713158637533)
                    ·
                      refine ⟨3092600015070267434489075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8246933373520713158637533 3092600015070267434489075)
                      ·
                        rfl

theorem cell23_6022817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_6022817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022817 prefixEnd_6022817 := by exact prefixLift 6022817
  have htrace : WordTrace (prefixWord ++ tailWord_6022817) baseStart_6022817 baseEnd_6022817 := by
    simpa [prefixWord, tailWord_6022817, baseEnd_6022817] using wordTrace_append hprefix tailTrace_6022817
  have hstable : (prefixWord ++ tailWord_6022817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022817).length < 2 ^ (prefixWord ++ tailWord_6022817).sum := by decide
  have hdescent : baseEnd_6022817 < baseStart_6022817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022824 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 6]
def baseStart_6022824 : Nat := 118140960795 + 6022824 * 2 ^ 59
def prefixEnd_6022824 : Nat := 4983230072969 + 3 ^ 40 * 6022824 * 2
def baseEnd_6022824 : Nat := 343622623270538767455727

theorem tailTrace_6022824 : CollatzResearch.WordTrace tailWord_6022824 prefixEnd_6022824 343622623270538767455727 := by
  unfold tailWord_6022824
  simp only [CollatzResearch.WordTrace]
  refine ⟨109835218966172369645985763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146446958621563159527981017 109835218966172369645985763)
  ·
    refine ⟨164752828449258554468978645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109835218966172369645985763 164752828449258554468978645)
    ·
      refine ⟨3861394416779497370366687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 164752828449258554468978645 3861394416779497370366687)
      ·
        refine ⟨5792091625169246055550031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3861394416779497370366687 5792091625169246055550031)
        ·
          refine ⟨8688137437753869083325047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5792091625169246055550031 8688137437753869083325047)
          ·
            refine ⟨13032206156630803624987571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688137437753869083325047 13032206156630803624987571)
            ·
              refine ⟨19548309234946205437481357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13032206156630803624987571 19548309234946205437481357)
              ·
                refine ⟨7330615963104827039055509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19548309234946205437481357 7330615963104827039055509)
                ·
                  refine ⟨343622623270538767455727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7330615963104827039055509 343622623270538767455727)
                  ·
                    rfl

theorem cell23_6022824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 6].length) (baseStart_6022824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022824 prefixEnd_6022824 := by exact prefixLift 6022824
  have htrace : WordTrace (prefixWord ++ tailWord_6022824) baseStart_6022824 baseEnd_6022824 := by
    simpa [prefixWord, tailWord_6022824, baseEnd_6022824] using wordTrace_append hprefix tailTrace_6022824
  have hstable : (prefixWord ++ tailWord_6022824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022824).length < 2 ^ (prefixWord ++ tailWord_6022824).sum := by decide
  have hdescent : baseEnd_6022824 < baseStart_6022824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022853 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_6022853 : Nat := 118140960795 + 6022853 * 2 ^ 59
def prefixEnd_6022853 : Nat := 4983230072969 + 3 ^ 40 * 6022853 * 2
def baseEnd_6022853 : Nat := 3092618500373829293638909

theorem tailTrace_6022853 : CollatzResearch.WordTrace tailWord_6022853 prefixEnd_6022853 3092618500373829293638909 := by
  unfold tailWord_6022853
  simp only [CollatzResearch.WordTrace]
  refine ⟨219671495649239677244777213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146447663766159784829851475 219671495649239677244777213)
  ·
    refine ⟨82376810868464878966791455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219671495649239677244777213 82376810868464878966791455)
    ·
      refine ⟨123565216302697318450187183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82376810868464878966791455 123565216302697318450187183)
      ·
        refine ⟨185347824454045977675280775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123565216302697318450187183 185347824454045977675280775)
        ·
          refine ⟨278021736681068966512921163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185347824454045977675280775 278021736681068966512921163)
          ·
            refine ⟨417032605021603449769381745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278021736681068966512921163 417032605021603449769381745)
            ·
              refine ⟨312774453766202587327036309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417032605021603449769381745 312774453766202587327036309)
              ·
                refine ⟨14661302520290746280954827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 312774453766202587327036309 14661302520290746280954827)
                ·
                  refine ⟨21991953780436119421432241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14661302520290746280954827 21991953780436119421432241)
                  ·
                    refine ⟨16493965335327089566074181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21991953780436119421432241 16493965335327089566074181)
                    ·
                      refine ⟨3092618500373829293638909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16493965335327089566074181 3092618500373829293638909)
                      ·
                        rfl

theorem cell23_6022853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_6022853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022853 prefixEnd_6022853 := by exact prefixLift 6022853
  have htrace : WordTrace (prefixWord ++ tailWord_6022853) baseStart_6022853 baseEnd_6022853 := by
    simpa [prefixWord, tailWord_6022853, baseEnd_6022853] using wordTrace_append hprefix tailTrace_6022853
  have hstable : (prefixWord ++ tailWord_6022853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022853).length < 2 ^ (prefixWord ++ tailWord_6022853).sum := by decide
  have hdescent : baseEnd_6022853 < baseStart_6022853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022868 : List Nat := [2, 4, 1, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6022868 : Nat := 118140960795 + 6022868 * 2 ^ 59
def prefixEnd_6022868 : Nat := 4983230072969 + 3 ^ 40 * 6022868 * 2
def baseEnd_6022868 : Nat := 3092626202583646734951341

theorem tailTrace_6022868 : CollatzResearch.WordTrace tailWord_6022868 prefixEnd_6022868 3092626202583646734951341 := by
  unfold tailWord_6022868
  simp only [CollatzResearch.WordTrace]
  refine ⟨109836021372092667403286629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146448028496123556537715505 109836021372092667403286629)
  ·
    refine ⟨20594254007267375138116243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109836021372092667403286629 20594254007267375138116243)
    ·
      refine ⟨30891381010901062707174365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20594254007267375138116243 30891381010901062707174365)
      ·
        refine ⟨11584267879087898515190387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30891381010901062707174365 11584267879087898515190387)
        ·
          refine ⟨17376401818631847772785581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11584267879087898515190387 17376401818631847772785581)
          ·
            refine ⟨6516150681986942914794593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17376401818631847772785581 6516150681986942914794593)
            ·
              refine ⟨4887113011490207186095945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6516150681986942914794593 4887113011490207186095945)
              ·
                refine ⟨3665334758617655389571959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4887113011490207186095945 3665334758617655389571959)
                ·
                  refine ⟨5498002137926483084357939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665334758617655389571959 5498002137926483084357939)
                  ·
                    refine ⟨8247003206889724626536909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5498002137926483084357939 8247003206889724626536909)
                    ·
                      refine ⟨3092626202583646734951341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8247003206889724626536909 3092626202583646734951341)
                      ·
                        rfl

theorem cell23_6022868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6022868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022868 prefixEnd_6022868 := by exact prefixLift 6022868
  have htrace : WordTrace (prefixWord ++ tailWord_6022868) baseStart_6022868 baseEnd_6022868 := by
    simpa [prefixWord, tailWord_6022868, baseEnd_6022868] using wordTrace_append hprefix tailTrace_6022868
  have hstable : (prefixWord ++ tailWord_6022868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022868).length < 2 ^ (prefixWord ++ tailWord_6022868).sum := by decide
  have hdescent : baseEnd_6022868 < baseStart_6022868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022890 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_6022890 : Nat := 118140960795 + 6022890 * 2 ^ 59
def prefixEnd_6022890 : Nat := 4983230072969 + 3 ^ 40 * 6022890 * 2
def baseEnd_6022890 : Nat := 3092637499158045648876239

theorem tailTrace_6022890 : CollatzResearch.WordTrace tailWord_6022890 prefixEnd_6022890 3092637499158045648876239 := by
  unfold tailWord_6022890
  simp only [CollatzResearch.WordTrace]
  refine ⟨54918211287526408140968531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146448563433403755042582749 54918211287526408140968531)
  ·
    refine ⟨82377316931289612211452797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54918211287526408140968531 82377316931289612211452797)
    ·
      refine ⟨30891493849233604579294799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82377316931289612211452797 30891493849233604579294799)
      ·
        refine ⟨46337240773850406868942199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30891493849233604579294799 46337240773850406868942199)
        ·
          refine ⟨69505861160775610303413299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46337240773850406868942199 69505861160775610303413299)
          ·
            refine ⟨104258791741163415455119949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69505861160775610303413299 104258791741163415455119949)
            ·
              refine ⟨39097046902936280795669981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104258791741163415455119949 39097046902936280795669981)
              ·
                refine ⟨14661392588601105298376243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39097046902936280795669981 14661392588601105298376243)
                ·
                  refine ⟨21992088882901657947564365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14661392588601105298376243 21992088882901657947564365)
                  ·
                    refine ⟨8247033331088121730336637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21992088882901657947564365 8247033331088121730336637)
                    ·
                      refine ⟨3092637499158045648876239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8247033331088121730336637 3092637499158045648876239)
                      ·
                        rfl

theorem cell23_6022890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_6022890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022890 prefixEnd_6022890 := by exact prefixLift 6022890
  have htrace : WordTrace (prefixWord ++ tailWord_6022890) baseStart_6022890 baseEnd_6022890 := by
    simpa [prefixWord, tailWord_6022890, baseEnd_6022890] using wordTrace_append hprefix tailTrace_6022890
  have hstable : (prefixWord ++ tailWord_6022890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022890).length < 2 ^ (prefixWord ++ tailWord_6022890).sum := by decide
  have hdescent : baseEnd_6022890 < baseStart_6022890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022923 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 2, 6]
def baseStart_6022923 : Nat := 118140960795 + 6022923 * 2 ^ 59
def prefixEnd_6022923 : Nat := 4983230072969 + 3 ^ 40 * 6022923 * 2
def baseEnd_6022923 : Nat := 1030884814673214673254529

theorem tailTrace_6022923 : CollatzResearch.WordTrace tailWord_6022923 prefixEnd_6022923 1030884814673214673254529 := by
  unfold tailWord_6022923
  simp only [CollatzResearch.WordTrace]
  refine ⟨219674048758986079199825423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146449365839324052799883615 219674048758986079199825423)
  ·
    refine ⟨329511073138479118799738135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219674048758986079199825423 329511073138479118799738135)
    ·
      refine ⟨494266609707718678199607203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329511073138479118799738135 494266609707718678199607203)
      ·
        refine ⟨741399914561578017299410805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494266609707718678199607203 741399914561578017299410805)
        ·
          refine ⟨69506241990147939121819763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 741399914561578017299410805 69506241990147939121819763)
          ·
            refine ⟨104259362985221908682729645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69506241990147939121819763 104259362985221908682729645)
            ·
              refine ⟨39097261119458215756023617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104259362985221908682729645 39097261119458215756023617)
              ·
                refine ⟨29322945839593661817017713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39097261119458215756023617 29322945839593661817017713)
                ·
                  refine ⟨21992209379695246362763285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29322945839593661817017713 21992209379695246362763285)
                  ·
                    refine ⟨1030884814673214673254529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21992209379695246362763285 1030884814673214673254529)
                    ·
                      rfl

theorem cell23_6022923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 6].length) (baseStart_6022923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022923 prefixEnd_6022923 := by exact prefixLift 6022923
  have htrace : WordTrace (prefixWord ++ tailWord_6022923) baseStart_6022923 baseEnd_6022923 := by
    simpa [prefixWord, tailWord_6022923, baseEnd_6022923] using wordTrace_append hprefix tailTrace_6022923
  have hstable : (prefixWord ++ tailWord_6022923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022923).length < 2 ^ (prefixWord ++ tailWord_6022923).sum := by decide
  have hdescent : baseEnd_6022923 < baseStart_6022923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6022947 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 1, 4, 2]
def baseStart_6022947 : Nat := 118140960795 + 6022947 * 2 ^ 59
def prefixEnd_6022947 : Nat := 4983230072969 + 3 ^ 40 * 6022947 * 2
def baseEnd_6022947 : Nat := 3092666767555351925863477

theorem tailTrace_6022947 : CollatzResearch.WordTrace tailWord_6022947 prefixEnd_6022947 3092666767555351925863477 := by
  unfold tailWord_6022947
  simp only [CollatzResearch.WordTrace]
  refine ⟨219674924110899131298699095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146449949407266087532466063 219674924110899131298699095)
  ·
    refine ⟨329512386166348696948048643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219674924110899131298699095 329512386166348696948048643)
    ·
      refine ⟨494268579249523045422072965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329512386166348696948048643 494268579249523045422072965)
      ·
        refine ⟨92675358609285571016638681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 494268579249523045422072965 92675358609285571016638681)
        ·
          refine ⟨69506518956964178262479011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92675358609285571016638681 69506518956964178262479011)
          ·
            refine ⟨104259778435446267393718517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69506518956964178262479011 104259778435446267393718517)
            ·
              refine ⟨9774354228323087568161111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104259778435446267393718517 9774354228323087568161111)
              ·
                refine ⟨14661531342484631352241667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9774354228323087568161111 14661531342484631352241667)
                ·
                  refine ⟨21992297013726947028362501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14661531342484631352241667 21992297013726947028362501)
                  ·
                    refine ⟨4123555690073802567817969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21992297013726947028362501 4123555690073802567817969)
                    ·
                      refine ⟨3092666767555351925863477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123555690073802567817969 3092666767555351925863477)
                      ·
                        rfl

theorem cell23_6022947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_6022947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6022947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6022947 prefixEnd_6022947 := by exact prefixLift 6022947
  have htrace : WordTrace (prefixWord ++ tailWord_6022947) baseStart_6022947 baseEnd_6022947 := by
    simpa [prefixWord, tailWord_6022947, baseEnd_6022947] using wordTrace_append hprefix tailTrace_6022947
  have hstable : (prefixWord ++ tailWord_6022947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6022947).length < 2 ^ (prefixWord ++ tailWord_6022947).sum := by decide
  have hdescent : baseEnd_6022947 < baseStart_6022947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6022947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023023 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_6023023 : Nat := 118140960795 + 6023023 * 2 ^ 59
def prefixEnd_6023023 : Nat := 4983230072969 + 3 ^ 40 * 6023023 * 2
def baseEnd_6023023 : Nat := 3092705792085093628513127

theorem tailTrace_6023023 : CollatzResearch.WordTrace tailWord_6023023 prefixEnd_6023023 3092705792085093628513127 := by
  unfold tailWord_6023023
  simp only [CollatzResearch.WordTrace]
  refine ⟨219677696058623796278465723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146451797372415864185643815 219677696058623796278465723)
  ·
    refine ⟨329516544087935694417698585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219677696058623796278465723 329516544087935694417698585)
    ·
      refine ⟨247137408065951770813273939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329516544087935694417698585 247137408065951770813273939)
      ·
        refine ⟨370706112098927656219910909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247137408065951770813273939 370706112098927656219910909)
        ·
          refine ⟨139014792037097871082466591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370706112098927656219910909 139014792037097871082466591)
          ·
            refine ⟨208522188055646806623699887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139014792037097871082466591 208522188055646806623699887)
            ·
              refine ⟨312783282083470209935549831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208522188055646806623699887 312783282083470209935549831)
              ·
                refine ⟨469174923125205314903324747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312783282083470209935549831 469174923125205314903324747)
                ·
                  refine ⟨703762384687807972354987121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469174923125205314903324747 703762384687807972354987121)
                  ·
                    refine ⟨527821788515855979266240341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 703762384687807972354987121 527821788515855979266240341)
                    ·
                      refine ⟨3092705792085093628513127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 527821788515855979266240341 3092705792085093628513127)
                      ·
                        rfl

theorem cell23_6023023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_6023023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023023 prefixEnd_6023023 := by exact prefixLift 6023023
  have htrace : WordTrace (prefixWord ++ tailWord_6023023) baseStart_6023023 baseEnd_6023023 := by
    simpa [prefixWord, tailWord_6023023, baseEnd_6023023] using wordTrace_append hprefix tailTrace_6023023
  have hstable : (prefixWord ++ tailWord_6023023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023023).length < 2 ^ (prefixWord ++ tailWord_6023023).sum := by decide
  have hdescent : baseEnd_6023023 < baseStart_6023023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023037 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 2, 4, 2]
def baseStart_6023037 : Nat := 118140960795 + 6023037 * 2 ^ 59
def prefixEnd_6023037 : Nat := 4983230072969 + 3 ^ 40 * 6023037 * 2
def baseEnd_6023037 : Nat := 3092712980814256573738063

theorem tailTrace_6023037 : CollatzResearch.WordTrace tailWord_6023037 prefixEnd_6023037 3092712980814256573738063 := by
  unfold tailWord_6023037
  simp only [CollatzResearch.WordTrace]
  refine ⟨219678206680573076669475365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146452137787048717779650243 219678206680573076669475365)
  ·
    refine ⟨41189663752607451875526631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219678206680573076669475365 41189663752607451875526631)
    ·
      refine ⟨61784495628911177813289947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41189663752607451875526631 61784495628911177813289947)
      ·
        refine ⟨92676743443366766719934921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61784495628911177813289947 92676743443366766719934921)
        ·
          refine ⟨69507557582525075039951191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92676743443366766719934921 69507557582525075039951191)
          ·
            refine ⟨104261336373787612559926787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69507557582525075039951191 104261336373787612559926787)
            ·
              refine ⟨156392004560681418839890181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104261336373787612559926787 156392004560681418839890181)
              ·
                refine ⟨29323500855127766032479409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156392004560681418839890181 29323500855127766032479409)
                ·
                  refine ⟨21992625641345824524359557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29323500855127766032479409 21992625641345824524359557)
                  ·
                    refine ⟨4123617307752342098317417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21992625641345824524359557 4123617307752342098317417)
                    ·
                      refine ⟨3092712980814256573738063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123617307752342098317417 3092712980814256573738063)
                      ·
                        rfl

theorem cell23_6023037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_6023037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023037 prefixEnd_6023037 := by exact prefixLift 6023037
  have htrace : WordTrace (prefixWord ++ tailWord_6023037) baseStart_6023037 baseEnd_6023037 := by
    simpa [prefixWord, tailWord_6023037, baseEnd_6023037] using wordTrace_append hprefix tailTrace_6023037
  have hstable : (prefixWord ++ tailWord_6023037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023037).length < 2 ^ (prefixWord ++ tailWord_6023037).sum := by decide
  have hdescent : baseEnd_6023037 < baseStart_6023037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023038 : List Nat := [4, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_6023038 : Nat := 118140960795 + 6023038 * 2 ^ 59
def prefixEnd_6023038 : Nat := 4983230072969 + 3 ^ 40 * 6023038 * 2
def baseEnd_6023038 : Nat := 343634832699434563313951

theorem tailTrace_6023038 : CollatzResearch.WordTrace tailWord_6023038 prefixEnd_6023038 343634832699434563313951 := by
  unfold tailWord_6023038
  simp only [CollatzResearch.WordTrace]
  refine ⟨27459780394196181730032721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146452162102379635893507845 27459780394196181730032721)
  ·
    refine ⟨20594835295647136297524541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27459780394196181730032721 20594835295647136297524541)
    ·
      refine ⟨7723063235867676111571703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20594835295647136297524541 7723063235867676111571703)
      ·
        refine ⟨11584594853801514167357555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7723063235867676111571703 11584594853801514167357555)
        ·
          refine ⟨17376892280702271251036333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11584594853801514167357555 17376892280702271251036333)
          ·
            refine ⟨6516334605263351719138625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17376892280702271251036333 6516334605263351719138625)
            ·
              refine ⟨4887250953947513789353969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6516334605263351719138625 4887250953947513789353969)
              ·
                refine ⟨3665438215460635342015477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4887250953947513789353969 3665438215460635342015477)
                ·
                  refine ⟨343634832699434563313951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3665438215460635342015477 343634832699434563313951)
                  ·
                    rfl

theorem cell23_6023038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_6023038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023038 prefixEnd_6023038 := by exact prefixLift 6023038
  have htrace : WordTrace (prefixWord ++ tailWord_6023038) baseStart_6023038 baseEnd_6023038 := by
    simpa [prefixWord, tailWord_6023038, baseEnd_6023038] using wordTrace_append hprefix tailTrace_6023038
  have hstable : (prefixWord ++ tailWord_6023038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023038).length < 2 ^ (prefixWord ++ tailWord_6023038).sum := by decide
  have hdescent : baseEnd_6023038 < baseStart_6023038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023071 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 2, 1, 4]
def baseStart_6023071 : Nat := 118140960795 + 6023071 * 2 ^ 59
def prefixEnd_6023071 : Nat := 4983230072969 + 3 ^ 40 * 6023071 * 2
def baseEnd_6023071 : Nat := 3092730439156509440712907

theorem tailTrace_6023071 : CollatzResearch.WordTrace tailWord_6023071 prefixEnd_6023071 3092730439156509440712907 := by
  unfold tailWord_6023071
  simp only [CollatzResearch.WordTrace]
  refine ⟨219679446762449900476213067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146452964508299933650808711 219679446762449900476213067)
  ·
    refine ⟨329519170143674850714319601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219679446762449900476213067 329519170143674850714319601)
    ·
      refine ⟨247139377607756138035739701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329519170143674850714319601 247139377607756138035739701)
      ·
        refine ⟨23169316650727137940850597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247139377607756138035739701 23169316650727137940850597)
        ·
          refine ⟨4344246872011338363909487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23169316650727137940850597 4344246872011338363909487)
          ·
            refine ⟨6516370308017007545864231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4344246872011338363909487 6516370308017007545864231)
            ·
              refine ⟨9774555462025511318796347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6516370308017007545864231 9774555462025511318796347)
              ·
                refine ⟨14661833193038266978194521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9774555462025511318796347 14661833193038266978194521)
                ·
                  refine ⟨10996374894778700233645891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14661833193038266978194521 10996374894778700233645891)
                  ·
                    refine ⟨16494562342168050350468837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10996374894778700233645891 16494562342168050350468837)
                    ·
                      refine ⟨3092730439156509440712907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16494562342168050350468837 3092730439156509440712907)
                      ·
                        rfl

theorem cell23_6023071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_6023071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023071 prefixEnd_6023071 := by exact prefixLift 6023071
  have htrace : WordTrace (prefixWord ++ tailWord_6023071) baseStart_6023071 baseEnd_6023071 := by
    simpa [prefixWord, tailWord_6023071, baseEnd_6023071] using wordTrace_append hprefix tailTrace_6023071
  have hstable : (prefixWord ++ tailWord_6023071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023071).length < 2 ^ (prefixWord ++ tailWord_6023071).sum := by decide
  have hdescent : baseEnd_6023071 < baseStart_6023071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023074 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_6023074 : Nat := 118140960795 + 6023074 * 2 ^ 59
def prefixEnd_6023074 : Nat := 4983230072969 + 3 ^ 40 * 6023074 * 2
def baseEnd_6023074 : Nat := 3092731979598472928975393

theorem tailTrace_6023074 : CollatzResearch.WordTrace tailWord_6023074 prefixEnd_6023074 3092731979598472928975393 := by
  unfold tailWord_6023074
  simp only [CollatzResearch.WordTrace]
  refine ⟨54919889045359757997143069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146453037454292687992381517 54919889045359757997143069)
  ·
    refine ⟨20594958392009909248928651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54919889045359757997143069 20594958392009909248928651)
    ·
      refine ⟨30892437588014863873392977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20594958392009909248928651 30892437588014863873392977)
      ·
        refine ⟨23169328191011147905044733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30892437588014863873392977 23169328191011147905044733)
        ·
          refine ⟨8688498071629180464391775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23169328191011147905044733 8688498071629180464391775)
          ·
            refine ⟨13032747107443770696587663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688498071629180464391775 13032747107443770696587663)
            ·
              refine ⟨19549120661165656044881495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13032747107443770696587663 19549120661165656044881495)
              ·
                refine ⟨29323680991748484067322243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19549120661165656044881495 29323680991748484067322243)
                ·
                  refine ⟨43985521487622726100983365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29323680991748484067322243 43985521487622726100983365)
                  ·
                    refine ⟨8247285278929261143934381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43985521487622726100983365 8247285278929261143934381)
                    ·
                      refine ⟨3092731979598472928975393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8247285278929261143934381 3092731979598472928975393)
                      ·
                        rfl

theorem cell23_6023074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_6023074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023074 prefixEnd_6023074 := by exact prefixLift 6023074
  have htrace : WordTrace (prefixWord ++ tailWord_6023074) baseStart_6023074 baseEnd_6023074 := by
    simpa [prefixWord, tailWord_6023074, baseEnd_6023074] using wordTrace_append hprefix tailTrace_6023074
  have hstable : (prefixWord ++ tailWord_6023074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023074).length < 2 ^ (prefixWord ++ tailWord_6023074).sum := by decide
  have hdescent : baseEnd_6023074 < baseStart_6023074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023087 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 5, 1, 3]
def baseStart_6023087 : Nat := 118140960795 + 6023087 * 2 ^ 59
def prefixEnd_6023087 : Nat := 4983230072969 + 3 ^ 40 * 6023087 * 2
def baseEnd_6023087 : Nat := 3092738654846981378112833

theorem tailTrace_6023087 : CollatzResearch.WordTrace tailWord_6023087 prefixEnd_6023087 3092738654846981378112833 := by
  unfold tailWord_6023087
  simp only [CollatzResearch.WordTrace]
  refine ⟨219680030330391935208795515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146453353553594623472530343 219680030330391935208795515)
  ·
    refine ⟨329520045495587902813193273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219680030330391935208795515 329520045495587902813193273)
    ·
      refine ⟨247140034121690927109894955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329520045495587902813193273 247140034121690927109894955)
      ·
        refine ⟨370710051182536390664842433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247140034121690927109894955 370710051182536390664842433)
        ·
          refine ⟨278032538386902292998631825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370710051182536390664842433 278032538386902292998631825)
          ·
            refine ⟨208524403790176719748973869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278032538386902292998631825 208524403790176719748973869)
            ·
              refine ⟨78196651421316269905865201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208524403790176719748973869 78196651421316269905865201)
              ·
                refine ⟨58647488565987202429398901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78196651421316269905865201 58647488565987202429398901)
                ·
                  refine ⟨5498202053061300227756147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58647488565987202429398901 5498202053061300227756147)
                  ·
                    refine ⟨8247303079591950341634221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5498202053061300227756147 8247303079591950341634221)
                    ·
                      refine ⟨3092738654846981378112833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8247303079591950341634221 3092738654846981378112833)
                      ·
                        rfl

theorem cell23_6023087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 1, 3].length) (baseStart_6023087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023087 prefixEnd_6023087 := by exact prefixLift 6023087
  have htrace : WordTrace (prefixWord ++ tailWord_6023087) baseStart_6023087 baseEnd_6023087 := by
    simpa [prefixWord, tailWord_6023087, baseEnd_6023087] using wordTrace_append hprefix tailTrace_6023087
  have hstable : (prefixWord ++ tailWord_6023087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023087).length < 2 ^ (prefixWord ++ tailWord_6023087).sum := by decide
  have hdescent : baseEnd_6023087 < baseStart_6023087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023104 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 3, 1, 3]
def baseStart_6023104 : Nat := 118140960795 + 6023104 * 2 ^ 59
def prefixEnd_6023104 : Nat := 4983230072969 + 3 ^ 40 * 6023104 * 2
def baseEnd_6023104 : Nat := 3092747384018107811600255

theorem tailTrace_6023104 : CollatzResearch.WordTrace tailWord_6023104 prefixEnd_6023104 3092747384018107811600255 := by
  unfold tailWord_6023104
  simp only [CollatzResearch.WordTrace]
  refine ⟨109840325185665173556082183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146453766914220231408109577 109840325185665173556082183)
  ·
    refine ⟨164760487778497760334123275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109840325185665173556082183 164760487778497760334123275)
    ·
      refine ⟨247140731667746640501184913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164760487778497760334123275 247140731667746640501184913)
      ·
        refine ⟨185355548750809980375888685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247140731667746640501184913 185355548750809980375888685)
        ·
          refine ⟨69508330781553742640958257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185355548750809980375888685 69508330781553742640958257)
          ·
            refine ⟨52131248086165306980718693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69508330781553742640958257 52131248086165306980718693)
            ·
              refine ⟨9774609016155995058884755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52131248086165306980718693 9774609016155995058884755)
              ·
                refine ⟨14661913524233992588327133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9774609016155995058884755 14661913524233992588327133)
                ·
                  refine ⟨5498217571587747220622675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14661913524233992588327133 5498217571587747220622675)
                  ·
                    refine ⟨8247326357381620830934013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5498217571587747220622675 8247326357381620830934013)
                    ·
                      refine ⟨3092747384018107811600255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8247326357381620830934013 3092747384018107811600255)
                      ·
                        rfl

theorem cell23_6023104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_6023104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023104 prefixEnd_6023104 := by exact prefixLift 6023104
  have htrace : WordTrace (prefixWord ++ tailWord_6023104) baseStart_6023104 baseEnd_6023104 := by
    simpa [prefixWord, tailWord_6023104, baseEnd_6023104] using wordTrace_append hprefix tailTrace_6023104
  have hstable : (prefixWord ++ tailWord_6023104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023104).length < 2 ^ (prefixWord ++ tailWord_6023104).sum := by decide
  have hdescent : baseEnd_6023104 < baseStart_6023104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023124 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_6023124 : Nat := 118140960795 + 6023124 * 2 ^ 59
def prefixEnd_6023124 : Nat := 4983230072969 + 3 ^ 40 * 6023124 * 2
def baseEnd_6023124 : Nat := 1030919217877065911116721

theorem tailTrace_6023124 : CollatzResearch.WordTrace tailWord_6023124 prefixEnd_6023124 1030919217877065911116721 := by
  unfold tailWord_6023124
  simp only [CollatzResearch.WordTrace]
  refine ⟨109840689915628945263946213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146454253220838593685261617 109840689915628945263946213)
  ·
    refine ⟨20595129359180427236989915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109840689915628945263946213 20595129359180427236989915)
    ·
      refine ⟨30892694038770640855484873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20595129359180427236989915 30892694038770640855484873)
      ·
        refine ⟨23169520529077980641613655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30892694038770640855484873 23169520529077980641613655)
        ·
          refine ⟨34754280793616970962420483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23169520529077980641613655 34754280793616970962420483)
          ·
            refine ⟨52131421190425456443630725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34754280793616970962420483 52131421190425456443630725)
            ·
              refine ⟨9774641473204773083180761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52131421190425456443630725 9774641473204773083180761)
              ·
                refine ⟨7330981104903579812385571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9774641473204773083180761 7330981104903579812385571)
                ·
                  refine ⟨10996471657355369718578357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7330981104903579812385571 10996471657355369718578357)
                  ·
                    refine ⟨1030919217877065911116721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10996471657355369718578357 1030919217877065911116721)
                    ·
                      rfl

theorem cell23_6023124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_6023124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023124 prefixEnd_6023124 := by exact prefixLift 6023124
  have htrace : WordTrace (prefixWord ++ tailWord_6023124) baseStart_6023124 baseEnd_6023124 := by
    simpa [prefixWord, tailWord_6023124, baseEnd_6023124] using wordTrace_append hprefix tailTrace_6023124
  have hstable : (prefixWord ++ tailWord_6023124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023124).length < 2 ^ (prefixWord ++ tailWord_6023124).sum := by decide
  have hdescent : baseEnd_6023124 < baseStart_6023124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023127 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 2, 6, 2]
def baseStart_6023127 : Nat := 118140960795 + 6023127 * 2 ^ 59
def prefixEnd_6023127 : Nat := 4983230072969 + 3 ^ 40 * 6023127 * 2
def baseEnd_6023127 : Nat := 3092759194073161221612649

theorem tailTrace_6023127 : CollatzResearch.WordTrace tailWord_6023127 prefixEnd_6023127 3092759194073161221612649 := by
  unfold tailWord_6023127
  simp only [CollatzResearch.WordTrace]
  refine ⟨219681489250247022040251635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146454326166831348026834423 219681489250247022040251635)
  ·
    refine ⟨329522233875370533060377453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219681489250247022040251635 329522233875370533060377453)
    ·
      refine ⟨123570837703263949897641545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329522233875370533060377453 123570837703263949897641545)
      ·
        refine ⟨92678128277447962423231159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123570837703263949897641545 92678128277447962423231159)
        ·
          refine ⟨139017192416171943634846739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92678128277447962423231159 139017192416171943634846739)
          ·
            refine ⟨208525788624257915452270109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139017192416171943634846739 208525788624257915452270109)
            ·
              refine ⟨78197170734096718294601291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208525788624257915452270109 78197170734096718294601291)
              ·
                refine ⟨117295756101145077441901937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78197170734096718294601291 117295756101145077441901937)
                ·
                  refine ⟨87971817075858808081426453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117295756101145077441901937 87971817075858808081426453)
                  ·
                    refine ⟨4123678925430881628816865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87971817075858808081426453 4123678925430881628816865)
                    ·
                      refine ⟨3092759194073161221612649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123678925430881628816865 3092759194073161221612649)
                      ·
                        rfl

theorem cell23_6023127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_6023127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023127 prefixEnd_6023127 := by exact prefixLift 6023127
  have htrace : WordTrace (prefixWord ++ tailWord_6023127) baseStart_6023127 baseEnd_6023127 := by
    simpa [prefixWord, tailWord_6023127, baseEnd_6023127] using wordTrace_append hprefix tailTrace_6023127
  have hstable : (prefixWord ++ tailWord_6023127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023127).length < 2 ^ (prefixWord ++ tailWord_6023127).sum := by decide
  have hdescent : baseEnd_6023127 < baseStart_6023127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023132 : List Nat := [2, 2, 6, 1, 1, 2, 1, 3, 1, 4]
def baseStart_6023132 : Nat := 118140960795 + 6023132 * 2 ^ 59
def prefixEnd_6023132 : Nat := 4983230072969 + 3 ^ 40 * 6023132 * 2
def baseEnd_6023132 : Nat := 1030920587158811234016709

theorem tailTrace_6023132 : CollatzResearch.WordTrace tailWord_6023132 prefixEnd_6023132 1030920587158811234016709 := by
  unfold tailWord_6023132
  simp only [CollatzResearch.WordTrace]
  refine ⟨109840835807614453947091825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146454447743485938596122433 109840835807614453947091825)
  ·
    refine ⟨82380626855710840460318869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109840835807614453947091825 82380626855710840460318869)
    ·
      refine ⟨3861591883861445646577447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82380626855710840460318869 3861591883861445646577447)
      ·
        refine ⟨5792387825792168469866171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3861591883861445646577447 5792387825792168469866171)
        ·
          refine ⟨8688581738688252704799257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5792387825792168469866171 8688581738688252704799257)
          ·
            refine ⟨6516436304016189528599443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8688581738688252704799257 6516436304016189528599443)
            ·
              refine ⟨9774654456024284292899165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6516436304016189528599443 9774654456024284292899165)
              ·
                refine ⟨3665495421009106609837187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9774654456024284292899165 3665495421009106609837187)
                ·
                  refine ⟨5498243131513659914755781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665495421009106609837187 5498243131513659914755781)
                  ·
                    refine ⟨1030920587158811234016709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5498243131513659914755781 1030920587158811234016709)
                    ·
                      rfl

theorem cell23_6023132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_6023132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023132 prefixEnd_6023132 := by exact prefixLift 6023132
  have htrace : WordTrace (prefixWord ++ tailWord_6023132) baseStart_6023132 baseEnd_6023132 := by
    simpa [prefixWord, tailWord_6023132, baseEnd_6023132] using wordTrace_append hprefix tailTrace_6023132
  have hstable : (prefixWord ++ tailWord_6023132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023132).length < 2 ^ (prefixWord ++ tailWord_6023132).sum := by decide
  have hdescent : baseEnd_6023132 < baseStart_6023132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023137 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 4, 4]
def baseStart_6023137 : Nat := 118140960795 + 6023137 * 2 ^ 59
def prefixEnd_6023137 : Nat := 4983230072969 + 3 ^ 40 * 6023137 * 2
def baseEnd_6023137 : Nat := 1030921442959902060829201

theorem tailTrace_6023137 : CollatzResearch.WordTrace tailWord_6023137 prefixEnd_6023137 1030921442959902060829201 := by
  unfold tailWord_6023137
  simp only [CollatzResearch.WordTrace]
  refine ⟨219681853980210793748115665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146454569320140529165410443 219681853980210793748115665)
  ·
    refine ⟨164761390485158095311086749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219681853980210793748115665 164761390485158095311086749)
    ·
      refine ⟨61785521431934285741657531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164761390485158095311086749 61785521431934285741657531)
      ·
        refine ⟨92678282147901428612486297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61785521431934285741657531 92678282147901428612486297)
        ·
          refine ⟨69508711610926071459364723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92678282147901428612486297 69508711610926071459364723)
          ·
            refine ⟨104263067416389107189047085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69508711610926071459364723 104263067416389107189047085)
            ·
              refine ⟨39098650281145915195892657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104263067416389107189047085 39098650281145915195892657)
              ·
                refine ⟨29323987710859436396919493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39098650281145915195892657 29323987710859436396919493)
                ·
                  refine ⟨5498247695786144324422405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29323987710859436396919493 5498247695786144324422405)
                  ·
                    refine ⟨1030921442959902060829201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5498247695786144324422405 1030921442959902060829201)
                    ·
                      rfl

theorem cell23_6023137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_6023137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023137 prefixEnd_6023137 := by exact prefixLift 6023137
  have htrace : WordTrace (prefixWord ++ tailWord_6023137) baseStart_6023137 baseEnd_6023137 := by
    simpa [prefixWord, tailWord_6023137, baseEnd_6023137] using wordTrace_append hprefix tailTrace_6023137
  have hstable : (prefixWord ++ tailWord_6023137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023137).length < 2 ^ (prefixWord ++ tailWord_6023137).sum := by decide
  have hdescent : baseEnd_6023137 < baseStart_6023137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023161 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 3, 2, 2]
def baseStart_6023161 : Nat := 118140960795 + 6023161 * 2 ^ 59
def prefixEnd_6023161 : Nat := 4983230072969 + 3 ^ 40 * 6023161 * 2
def baseEnd_6023161 : Nat := 3092776652415414088587493

theorem tailTrace_6023161 : CollatzResearch.WordTrace tailWord_6023161 prefixEnd_6023161 3092776652415414088587493 := by
  unfold tailWord_6023161
  simp only [CollatzResearch.WordTrace]
  refine ⟨219682729332123845846989337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146455152888082563897992891 219682729332123845846989337)
  ·
    refine ⟨164762046999092884385242003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219682729332123845846989337 164762046999092884385242003)
    ·
      refine ⟨247143070498639326577863005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164762046999092884385242003 247143070498639326577863005)
      ·
        refine ⟨92678651436989747466698627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247143070498639326577863005 92678651436989747466698627)
        ·
          refine ⟨139017977155484621200047941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92678651436989747466698627 139017977155484621200047941)
          ·
            refine ⟨26065870716653366475008989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139017977155484621200047941 26065870716653366475008989)
            ·
              refine ⟨9774701518745012428128371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26065870716653366475008989 9774701518745012428128371)
              ·
                refine ⟨14662052278117518642192557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9774701518745012428128371 14662052278117518642192557)
                ·
                  refine ⟨5498269604294069490822209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14662052278117518642192557 5498269604294069490822209)
                  ·
                    refine ⟨4123702203220552118116657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5498269604294069490822209 4123702203220552118116657)
                    ·
                      refine ⟨3092776652415414088587493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123702203220552118116657 3092776652415414088587493)
                      ·
                        rfl

theorem cell23_6023161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_6023161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023161 prefixEnd_6023161 := by exact prefixLift 6023161
  have htrace : WordTrace (prefixWord ++ tailWord_6023161) baseStart_6023161 baseEnd_6023161 := by
    simpa [prefixWord, tailWord_6023161, baseEnd_6023161] using wordTrace_append hprefix tailTrace_6023161
  have hstable : (prefixWord ++ tailWord_6023161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023161).length < 2 ^ (prefixWord ++ tailWord_6023161).sum := by decide
  have hdescent : baseEnd_6023161 < baseStart_6023161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023178 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4]
def baseStart_6023178 : Nat := 118140960795 + 6023178 * 2 ^ 59
def prefixEnd_6023178 : Nat := 4983230072969 + 3 ^ 40 * 6023178 * 2
def baseEnd_6023178 : Nat := 3092785381586540522074915

theorem tailTrace_6023178 : CollatzResearch.WordTrace tailWord_6023178 prefixEnd_6023178 3092785381586540522074915 := by
  unfold tailWord_6023178
  simp only [CollatzResearch.WordTrace]
  refine ⟨54920837343265564437589547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146455566248708171833572125 54920837343265564437589547)
  ·
    refine ⟨82381256014898346656384321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54920837343265564437589547 82381256014898346656384321)
    ·
      refine ⟨61785942011173759992288241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82381256014898346656384321 61785942011173759992288241)
      ·
        refine ⟨46339456508380319994216181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61785942011173759992288241 46339456508380319994216181)
        ·
          refine ⟨4344324047660654999457767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46339456508380319994216181 4344324047660654999457767)
          ·
            refine ⟨6516486071490982499186651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4344324047660654999457767 6516486071490982499186651)
            ·
              refine ⟨9774729107236473748779977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6516486071490982499186651 9774729107236473748779977)
              ·
                refine ⟨7331046830427355311584983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9774729107236473748779977 7331046830427355311584983)
                ·
                  refine ⟨10996570245641032967377475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7331046830427355311584983 10996570245641032967377475)
                  ·
                    refine ⟨16494855368461549451066213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10996570245641032967377475 16494855368461549451066213)
                    ·
                      refine ⟨3092785381586540522074915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16494855368461549451066213 3092785381586540522074915)
                      ·
                        rfl

theorem cell23_6023178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_6023178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023178 prefixEnd_6023178 := by exact prefixLift 6023178
  have htrace : WordTrace (prefixWord ++ tailWord_6023178) baseStart_6023178 baseEnd_6023178 := by
    simpa [prefixWord, tailWord_6023178, baseEnd_6023178] using wordTrace_append hprefix tailTrace_6023178
  have hstable : (prefixWord ++ tailWord_6023178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023178).length < 2 ^ (prefixWord ++ tailWord_6023178).sum := by decide
  have hdescent : baseEnd_6023178 < baseStart_6023178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023194 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3]
def baseStart_6023194 : Nat := 118140960795 + 6023194 * 2 ^ 59
def prefixEnd_6023194 : Nat := 4983230072969 + 3 ^ 40 * 6023194 * 2
def baseEnd_6023194 : Nat := 3092793597277012459474841

theorem tailTrace_6023194 : CollatzResearch.WordTrace tailWord_6023194 prefixEnd_6023194 3092793597277012459474841 := by
  unfold tailWord_6023194
  simp only [CollatzResearch.WordTrace]
  refine ⟨54920983235251073120735159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146455955294002861655293757 54920983235251073120735159)
  ·
    refine ⟨82381474852876609681102739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54920983235251073120735159 82381474852876609681102739)
    ·
      refine ⟨123572212279314914521654109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82381474852876609681102739 123572212279314914521654109)
      ·
        refine ⟨46339579604743092945620291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123572212279314914521654109 46339579604743092945620291)
        ·
          refine ⟨69509369407114639418430437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46339579604743092945620291 69509369407114639418430437)
          ·
            refine ⟨13033006763833994890955707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69509369407114639418430437 13033006763833994890955707)
            ·
              refine ⟨19549510145750992336433561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13033006763833994890955707 19549510145750992336433561)
              ·
                refine ⟨14662132609313244252325171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19549510145750992336433561 14662132609313244252325171)
                ·
                  refine ⟨21993198913969866378487757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14662132609313244252325171 21993198913969866378487757)
                  ·
                    refine ⟨8247449592738699891932909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21993198913969866378487757 8247449592738699891932909)
                    ·
                      refine ⟨3092793597277012459474841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8247449592738699891932909 3092793597277012459474841)
                      ·
                        rfl

theorem cell23_6023194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_6023194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023194 prefixEnd_6023194 := by exact prefixLift 6023194
  have htrace : WordTrace (prefixWord ++ tailWord_6023194) baseStart_6023194 baseEnd_6023194 := by
    simpa [prefixWord, tailWord_6023194, baseEnd_6023194] using wordTrace_append hprefix tailTrace_6023194
  have hstable : (prefixWord ++ tailWord_6023194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023194).length < 2 ^ (prefixWord ++ tailWord_6023194).sum := by decide
  have hdescent : baseEnd_6023194 < baseStart_6023194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023217 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_6023217 : Nat := 118140960795 + 6023217 * 2 ^ 59
def prefixEnd_6023217 : Nat := 4983230072969 + 3 ^ 40 * 6023217 * 2
def baseEnd_6023217 : Nat := 3092805407332065869487235

theorem tailTrace_6023217 : CollatzResearch.WordTrace tailWord_6023217 prefixEnd_6023217 3092805407332065869487235 := by
  unfold tailWord_6023217
  simp only [CollatzResearch.WordTrace]
  refine ⟨219684771819920967411027905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146456514546613978274018603 219684771819920967411027905)
  ·
    refine ⟨164763578864940725558270929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219684771819920967411027905 164763578864940725558270929)
    ·
      refine ⟨123572684148705544168703197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164763578864940725558270929 123572684148705544168703197)
      ·
        refine ⟨46339756555764579063263699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123572684148705544168703197 46339756555764579063263699)
        ·
          refine ⟨69509634833646868594895549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46339756555764579063263699 69509634833646868594895549)
          ·
            refine ⟨26066113062617575723085831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69509634833646868594895549 26066113062617575723085831)
            ·
              refine ⟨39099169593926363584628747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26066113062617575723085831 39099169593926363584628747)
              ·
                refine ⟨58648754390889545376943121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39099169593926363584628747 58648754390889545376943121)
                ·
                  refine ⟨43986565793167159032707341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58648754390889545376943121 43986565793167159032707341)
                  ·
                    refine ⟨16494962172437684637265253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43986565793167159032707341 16494962172437684637265253)
                    ·
                      refine ⟨3092805407332065869487235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16494962172437684637265253 3092805407332065869487235)
                      ·
                        rfl

theorem cell23_6023217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_6023217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023217 prefixEnd_6023217 := by exact prefixLift 6023217
  have htrace : WordTrace (prefixWord ++ tailWord_6023217) baseStart_6023217 baseEnd_6023217 := by
    simpa [prefixWord, tailWord_6023217, baseEnd_6023217] using wordTrace_append hprefix tailTrace_6023217
  have hstable : (prefixWord ++ tailWord_6023217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023217).length < 2 ^ (prefixWord ++ tailWord_6023217).sum := by decide
  have hdescent : baseEnd_6023217 < baseStart_6023217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023237 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 4, 4, 3]
def baseStart_6023237 : Nat := 118140960795 + 6023237 * 2 ^ 59
def prefixEnd_6023237 : Nat := 4983230072969 + 3 ^ 40 * 6023237 * 2
def baseEnd_6023237 : Nat := 3092815676945155791237143

theorem tailTrace_6023237 : CollatzResearch.WordTrace tailWord_6023237 prefixEnd_6023237 3092815676945155791237143 := by
  unfold tailWord_6023237
  simp only [CollatzResearch.WordTrace]
  refine ⟨219685501279848510826755965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146457000853232340551170643 219685501279848510826755965)
  ·
    refine ⟨82382062979943191560033487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219685501279848510826755965 82382062979943191560033487)
    ·
      refine ⟨123573094469914787340050231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82382062979943191560033487 123573094469914787340050231)
      ·
        refine ⟨185359641704872181010075347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123573094469914787340050231 185359641704872181010075347)
        ·
          refine ⟨278039462557308271515113021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185359641704872181010075347 278039462557308271515113021)
          ·
            refine ⟨104264798458990601818167383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278039462557308271515113021 104264798458990601818167383)
            ·
              refine ⟨156397197688485902727251075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104264798458990601818167383 156397197688485902727251075)
              ·
                refine ⟨234595796532728854090876613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156397197688485902727251075 234595796532728854090876613)
                ·
                  refine ⟨43986711849886660142039365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234595796532728854090876613 43986711849886660142039365)
                  ·
                    refine ⟨8247508471853748776632381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43986711849886660142039365 8247508471853748776632381)
                    ·
                      refine ⟨3092815676945155791237143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8247508471853748776632381 3092815676945155791237143)
                      ·
                        rfl

theorem cell23_6023237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_6023237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023237 prefixEnd_6023237 := by exact prefixLift 6023237
  have htrace : WordTrace (prefixWord ++ tailWord_6023237) baseStart_6023237 baseEnd_6023237 := by
    simpa [prefixWord, tailWord_6023237, baseEnd_6023237] using wordTrace_append hprefix tailTrace_6023237
  have hstable : (prefixWord ++ tailWord_6023237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023237).length < 2 ^ (prefixWord ++ tailWord_6023237).sum := by decide
  have hdescent : baseEnd_6023237 < baseStart_6023237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023238 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_6023238 : Nat := 118140960795 + 6023238 * 2 ^ 59
def prefixEnd_6023238 : Nat := 4983230072969 + 3 ^ 40 * 6023238 * 2
def baseEnd_6023238 : Nat := 3092816190425810287324639

theorem tailTrace_6023238 : CollatzResearch.WordTrace tailWord_6023238 prefixEnd_6023238 3092816190425810287324639 := by
  unfold tailWord_6023238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6865173054776402749923199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146457025168563258665028245 6865173054776402749923199)
  ·
    refine ⟨10297759582164604124884799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6865173054776402749923199 10297759582164604124884799)
    ·
      refine ⟨15446639373246906187327199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10297759582164604124884799 15446639373246906187327199)
      ·
        refine ⟨23169959059870359280990799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15446639373246906187327199 23169959059870359280990799)
        ·
          refine ⟨34754938589805538921486199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23169959059870359280990799 34754938589805538921486199)
          ·
            refine ⟨52132407884708308382229299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34754938589805538921486199 52132407884708308382229299)
            ·
              refine ⟨78198611827062462573343949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52132407884708308382229299 78198611827062462573343949)
              ·
                refine ⟨29324479435148423465003981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78198611827062462573343949 29324479435148423465003981)
                ·
                  refine ⟨10996679788180658799376493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29324479435148423465003981 10996679788180658799376493)
                  ·
                    refine ⟨4123754920567747049766185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10996679788180658799376493 4123754920567747049766185)
                    ·
                      refine ⟨3092816190425810287324639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123754920567747049766185 3092816190425810287324639)
                      ·
                        rfl

theorem cell23_6023238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_6023238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023238 prefixEnd_6023238 := by exact prefixLift 6023238
  have htrace : WordTrace (prefixWord ++ tailWord_6023238) baseStart_6023238 baseEnd_6023238 := by
    simpa [prefixWord, tailWord_6023238, baseEnd_6023238] using wordTrace_append hprefix tailTrace_6023238
  have hstable : (prefixWord ++ tailWord_6023238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023238).length < 2 ^ (prefixWord ++ tailWord_6023238).sum := by decide
  have hdescent : baseEnd_6023238 < baseStart_6023238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023268 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 2, 2, 2]
def baseStart_6023268 : Nat := 118140960795 + 6023268 * 2 ^ 59
def prefixEnd_6023268 : Nat := 4983230072969 + 3 ^ 40 * 6023268 * 2
def baseEnd_6023268 : Nat := 3092831594845445169949501

theorem tailTrace_6023268 : CollatzResearch.WordTrace tailWord_6023268 prefixEnd_6023268 3092831594845445169949501 := by
  unfold tailWord_6023268
  simp only [CollatzResearch.WordTrace]
  refine ⟨109843315971368101560567229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146457754628490802080756305 109843315971368101560567229)
  ·
    refine ⟨41191243489263038085212711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109843315971368101560567229 41191243489263038085212711)
    ·
      refine ⟨61786865233894557127819067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41191243489263038085212711 61786865233894557127819067)
      ·
        refine ⟨92680297850841835691728601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61786865233894557127819067 92680297850841835691728601)
        ·
          refine ⟨69510223388131376768796451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92680297850841835691728601 69510223388131376768796451)
          ·
            refine ⟨104265335082197065153194677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69510223388131376768796451 104265335082197065153194677)
            ·
              refine ⟨9774875163955974858112001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104265335082197065153194677 9774875163955974858112001)
              ·
                refine ⟨7331156372966981143584001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9774875163955974858112001 7331156372966981143584001)
                ·
                  refine ⟨5498367279725235857688001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7331156372966981143584001 5498367279725235857688001)
                  ·
                    refine ⟨4123775459793926893266001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5498367279725235857688001 4123775459793926893266001)
                    ·
                      refine ⟨3092831594845445169949501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123775459793926893266001 3092831594845445169949501)
                      ·
                        rfl

theorem cell23_6023268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_6023268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023268 prefixEnd_6023268 := by exact prefixLift 6023268
  have htrace : WordTrace (prefixWord ++ tailWord_6023268) baseStart_6023268 baseEnd_6023268 := by
    simpa [prefixWord, tailWord_6023268, baseEnd_6023268] using wordTrace_append hprefix tailTrace_6023268
  have hstable : (prefixWord ++ tailWord_6023268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023268).length < 2 ^ (prefixWord ++ tailWord_6023268).sum := by decide
  have hdescent : baseEnd_6023268 < baseStart_6023268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023287 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 1, 7]
def baseStart_6023287 : Nat := 118140960795 + 6023287 * 2 ^ 59
def prefixEnd_6023287 : Nat := 4983230072969 + 3 ^ 40 * 6023287 * 2
def baseEnd_6023287 : Nat := 1030947116992626865203971

theorem tailTrace_6023287 : CollatzResearch.WordTrace tailWord_6023287 prefixEnd_6023287 1030947116992626865203971 := by
  unfold tailWord_6023287
  simp only [CollatzResearch.WordTrace]
  refine ⟨219687324929667369366076115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146458216619778246244050743 219687324929667369366076115)
  ·
    refine ⟨329530987394501054049114173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219687324929667369366076115 329530987394501054049114173)
    ·
      refine ⟨123574120272937895268417815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329530987394501054049114173 123574120272937895268417815)
      ·
        refine ⟨185361180409406842902626723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123574120272937895268417815 185361180409406842902626723)
        ·
          refine ⟨278041770614110264353940085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185361180409406842902626723 278041770614110264353940085)
          ·
            refine ⟨26066415995072837283181883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278041770614110264353940085 26066415995072837283181883)
            ·
              refine ⟨39099623992609255924772825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26066415995072837283181883 39099623992609255924772825)
              ·
                refine ⟨29324717994456941943579619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39099623992609255924772825 29324717994456941943579619)
                ·
                  refine ⟨43987076991685412915369429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29324717994456941943579619 43987076991685412915369429)
                  ·
                    refine ⟨1030947116992626865203971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43987076991685412915369429 1030947116992626865203971)
                    ·
                      rfl

theorem cell23_6023287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_6023287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023287 prefixEnd_6023287 := by exact prefixLift 6023287
  have htrace : WordTrace (prefixWord ++ tailWord_6023287) baseStart_6023287 baseEnd_6023287 := by
    simpa [prefixWord, tailWord_6023287, baseEnd_6023287] using wordTrace_append hprefix tailTrace_6023287
  have hstable : (prefixWord ++ tailWord_6023287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023287).length < 2 ^ (prefixWord ++ tailWord_6023287).sum := by decide
  have hdescent : baseEnd_6023287 < baseStart_6023287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023304 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 1, 7]
def baseStart_6023304 : Nat := 118140960795 + 6023304 * 2 ^ 59
def prefixEnd_6023304 : Nat := 4983230072969 + 3 ^ 40 * 6023304 * 2
def baseEnd_6023304 : Nat := 1030950026716335676366445

theorem tailTrace_6023304 : CollatzResearch.WordTrace tailWord_6023304 prefixEnd_6023304 1030950026716335676366445 := by
  unfold tailWord_6023304
  simp only [CollatzResearch.WordTrace]
  refine ⟨109843972485302890634722483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146458629980403854179629977 109843972485302890634722483)
  ·
    refine ⟨164765958727954335952083725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109843972485302890634722483 164765958727954335952083725)
    ·
      refine ⟨61787234522982875982031397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164765958727954335952083725 61787234522982875982031397)
      ·
        refine ⟨11585106473059289246630887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61787234522982875982031397 11585106473059289246630887)
        ·
          refine ⟨17377659709588933869946331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11585106473059289246630887 17377659709588933869946331)
          ·
            refine ⟨26066489564383400804919497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17377659709588933869946331 26066489564383400804919497)
            ·
              refine ⟨19549867173287550603689623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26066489564383400804919497 19549867173287550603689623)
              ·
                refine ⟨29324800759931325905534435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19549867173287550603689623 29324800759931325905534435)
                ·
                  refine ⟨43987201139896988858301653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29324800759931325905534435 43987201139896988858301653)
                  ·
                    refine ⟨1030950026716335676366445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43987201139896988858301653 1030950026716335676366445)
                    ·
                      rfl

theorem cell23_6023304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_6023304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023304 prefixEnd_6023304 := by exact prefixLift 6023304
  have htrace : WordTrace (prefixWord ++ tailWord_6023304) baseStart_6023304 baseEnd_6023304 := by
    simpa [prefixWord, tailWord_6023304, baseEnd_6023304] using wordTrace_append hprefix tailTrace_6023304
  have hstable : (prefixWord ++ tailWord_6023304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023304).length < 2 ^ (prefixWord ++ tailWord_6023304).sum := by decide
  have hdescent : baseEnd_6023304 < baseStart_6023304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023314 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_6023314 : Nat := 118140960795 + 6023314 * 2 ^ 59
def prefixEnd_6023314 : Nat := 4983230072969 + 3 ^ 40 * 6023314 * 2
def baseEnd_6023314 : Nat := 3092855214955551989974289

theorem tailTrace_6023314 : CollatzResearch.WordTrace tailWord_6023314 prefixEnd_6023314 3092855214955551989974289 := by
  unfold tailWord_6023314
  simp only [CollatzResearch.WordTrace]
  refine ⟨54922077425142388244327249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146458873133713035318205997 54922077425142388244327249)
  ·
    refine ⟨41191558068856791183245437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54922077425142388244327249 41191558068856791183245437)
    ·
      refine ⟨15446834275821296693717039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41191558068856791183245437 15446834275821296693717039)
      ·
        refine ⟨23170251413731945040575559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15446834275821296693717039 23170251413731945040575559)
        ·
          refine ⟨34755377120597917560863339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23170251413731945040575559 34755377120597917560863339)
          ·
            refine ⟨52133065680896876341295009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34755377120597917560863339 52133065680896876341295009)
            ·
              refine ⟨39099799260672657255971257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52133065680896876341295009 39099799260672657255971257)
              ·
                refine ⟨29324849445504492941978443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39099799260672657255971257 29324849445504492941978443)
                ·
                  refine ⟨43987274168256739412967665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29324849445504492941978443 43987274168256739412967665)
                  ·
                    refine ⟨32990455626192554559725749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43987274168256739412967665 32990455626192554559725749)
                    ·
                      refine ⟨3092855214955551989974289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32990455626192554559725749 3092855214955551989974289)
                      ·
                        rfl

theorem cell23_6023314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_6023314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023314 prefixEnd_6023314 := by exact prefixLift 6023314
  have htrace : WordTrace (prefixWord ++ tailWord_6023314) baseStart_6023314 baseEnd_6023314 := by
    simpa [prefixWord, tailWord_6023314, baseEnd_6023314] using wordTrace_append hprefix tailTrace_6023314
  have hstable : (prefixWord ++ tailWord_6023314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023314).length < 2 ^ (prefixWord ++ tailWord_6023314).sum := by decide
  have hdescent : baseEnd_6023314 < baseStart_6023314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023358 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_6023358 : Nat := 118140960795 + 6023358 * 2 ^ 59
def prefixEnd_6023358 : Nat := 4983230072969 + 3 ^ 40 * 6023358 * 2
def baseEnd_6023358 : Nat := 3092877808104349817824087

theorem tailTrace_6023358 : CollatzResearch.WordTrace tailWord_6023358 prefixEnd_6023358 3092877808104349817824087 := by
  unfold tailWord_6023358
  simp only [CollatzResearch.WordTrace]
  refine ⟨27461239314051268561488841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146459943008273432327940485 27461239314051268561488841)
  ·
    refine ⟨20595929485538451421116631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27461239314051268561488841 20595929485538451421116631)
    ·
      refine ⟨30893894228307677131674947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20595929485538451421116631 30893894228307677131674947)
      ·
        refine ⟨46340841342461515697512421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30893894228307677131674947 46340841342461515697512421)
        ·
          refine ⟨8688907751711534193283579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46340841342461515697512421 8688907751711534193283579)
          ·
            refine ⟨13033361627567301289925369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688907751711534193283579 13033361627567301289925369)
            ·
              refine ⟨9775021220675475967444027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13033361627567301289925369 9775021220675475967444027)
              ·
                refine ⟨14662531831013213951166041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9775021220675475967444027 14662531831013213951166041)
                ·
                  refine ⟨10996898873259910463374531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14662531831013213951166041 10996898873259910463374531)
                  ·
                    refine ⟨16495348309889865695061797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10996898873259910463374531 16495348309889865695061797)
                    ·
                      refine ⟨3092877808104349817824087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16495348309889865695061797 3092877808104349817824087)
                      ·
                        rfl

theorem cell23_6023358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_6023358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023358 prefixEnd_6023358 := by exact prefixLift 6023358
  have htrace : WordTrace (prefixWord ++ tailWord_6023358) baseStart_6023358 baseEnd_6023358 := by
    simpa [prefixWord, tailWord_6023358, baseEnd_6023358] using wordTrace_append hprefix tailTrace_6023358
  have hstable : (prefixWord ++ tailWord_6023358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023358).length < 2 ^ (prefixWord ++ tailWord_6023358).sum := by decide
  have hdescent : baseEnd_6023358 < baseStart_6023358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023367 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_6023367 : Nat := 118140960795 + 6023367 * 2 ^ 59
def prefixEnd_6023367 : Nat := 4983230072969 + 3 ^ 40 * 6023367 * 2
def baseEnd_6023367 : Nat := 3092882429430240282611545

theorem tailTrace_6023367 : CollatzResearch.WordTrace tailWord_6023367 prefixEnd_6023367 3092882429430240282611545 := by
  unfold tailWord_6023367
  simp only [CollatzResearch.WordTrace]
  refine ⟨219690242769377543028988355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146460161846251695352658903 219690242769377543028988355)
  ·
    refine ⟨329535364154066314543482533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219690242769377543028988355 329535364154066314543482533)
    ·
      refine ⟨61787880778887433976902975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329535364154066314543482533 61787880778887433976902975)
      ·
        refine ⟨92681821168331150965354463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61787880778887433976902975 92681821168331150965354463)
        ·
          refine ⟨139022731752496726448031695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92681821168331150965354463 139022731752496726448031695)
          ·
            refine ⟨208534097628745089672047543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139022731752496726448031695 208534097628745089672047543)
            ·
              refine ⟨312801146443117634508071315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208534097628745089672047543 312801146443117634508071315)
              ·
                refine ⟨469201719664676451762106973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312801146443117634508071315 469201719664676451762106973)
                ·
                  refine ⟨175950644874253669410790115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469201719664676451762106973 175950644874253669410790115)
                  ·
                    refine ⟨263925967311380504116185173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175950644874253669410790115 263925967311380504116185173)
                    ·
                      refine ⟨3092882429430240282611545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 263925967311380504116185173 3092882429430240282611545)
                      ·
                        rfl

theorem cell23_6023367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_6023367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023367 prefixEnd_6023367 := by exact prefixLift 6023367
  have htrace : WordTrace (prefixWord ++ tailWord_6023367) baseStart_6023367 baseEnd_6023367 := by
    simpa [prefixWord, tailWord_6023367, baseEnd_6023367] using wordTrace_append hprefix tailTrace_6023367
  have hstable : (prefixWord ++ tailWord_6023367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023367).length < 2 ^ (prefixWord ++ tailWord_6023367).sum := by decide
  have hdescent : baseEnd_6023367 < baseStart_6023367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023387 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 7]
def baseStart_6023387 : Nat := 118140960795 + 6023387 * 2 ^ 59
def prefixEnd_6023387 : Nat := 4983230072969 + 3 ^ 40 * 6023387 * 2
def baseEnd_6023387 : Nat := 3092892699043330204361453

theorem tailTrace_6023387 : CollatzResearch.WordTrace tailWord_6023387 prefixEnd_6023387 3092892699043330204361453 := by
  unfold tailWord_6023387
  simp only [CollatzResearch.WordTrace]
  refine ⟨219690972229305086444716415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146460648152870057629810943 219690972229305086444716415)
  ·
    refine ⟨329536458343957629667074623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219690972229305086444716415 329536458343957629667074623)
    ·
      refine ⟨494304687515936444500611935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329536458343957629667074623 494304687515936444500611935)
      ·
        refine ⟨741457031273904666750917903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494304687515936444500611935 741457031273904666750917903)
        ·
          refine ⟨1112185546910857000126376855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741457031273904666750917903 1112185546910857000126376855)
          ·
            refine ⟨1668278320366285500189565283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112185546910857000126376855 1668278320366285500189565283)
            ·
              refine ⟨2502417480549428250284347925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668278320366285500189565283 2502417480549428250284347925)
              ·
                refine ⟨117300819400754449232078809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2502417480549428250284347925 117300819400754449232078809)
                ·
                  refine ⟨87975614550565836924059107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117300819400754449232078809 87975614550565836924059107)
                  ·
                    refine ⟨131963421825848755386088661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87975614550565836924059107 131963421825848755386088661)
                    ·
                      refine ⟨3092892699043330204361453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131963421825848755386088661 3092892699043330204361453)
                      ·
                        rfl

theorem cell23_6023387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_6023387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023387 prefixEnd_6023387 := by exact prefixLift 6023387
  have htrace : WordTrace (prefixWord ++ tailWord_6023387) baseStart_6023387 baseEnd_6023387 := by
    simpa [prefixWord, tailWord_6023387, baseEnd_6023387] using wordTrace_append hprefix tailTrace_6023387
  have hstable : (prefixWord ++ tailWord_6023387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023387).length < 2 ^ (prefixWord ++ tailWord_6023387).sum := by decide
  have hdescent : baseEnd_6023387 < baseStart_6023387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023391 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 3, 1, 3]
def baseStart_6023391 : Nat := 118140960795 + 6023391 * 2 ^ 59
def prefixEnd_6023391 : Nat := 4983230072969 + 3 ^ 40 * 6023391 * 2
def baseEnd_6023391 : Nat := 3092894752965948188711435

theorem tailTrace_6023391 : CollatzResearch.WordTrace tailWord_6023391 prefixEnd_6023391 3092894752965948188711435 := by
  unfold tailWord_6023391
  simp only [CollatzResearch.WordTrace]
  refine ⟨219691118121290595127862027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146460745414193730085241351 219691118121290595127862027)
  ·
    refine ⟨329536677181935892691793041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219691118121290595127862027 329536677181935892691793041)
    ·
      refine ⟨247152507886451919518844781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329536677181935892691793041 247152507886451919518844781)
      ·
        refine ⟨92682190457419469819566793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247152507886451919518844781 92682190457419469819566793)
        ·
          refine ⟨69511642843064602364675095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92682190457419469819566793 69511642843064602364675095)
          ·
            refine ⟨104267464264596903547012643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69511642843064602364675095 104267464264596903547012643)
            ·
              refine ⟨156401196396895355320518965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104267464264596903547012643 156401196396895355320518965)
              ·
                refine ⟨14662612162208939561298653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156401196396895355320518965 14662612162208939561298653)
                ·
                  refine ⟨5498479560828352335486995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14662612162208939561298653 5498479560828352335486995)
                  ·
                    refine ⟨8247719341242528503230493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5498479560828352335486995 8247719341242528503230493)
                    ·
                      refine ⟨3092894752965948188711435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8247719341242528503230493 3092894752965948188711435)
                      ·
                        rfl

theorem cell23_6023391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_6023391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023391 prefixEnd_6023391 := by exact prefixLift 6023391
  have htrace : WordTrace (prefixWord ++ tailWord_6023391) baseStart_6023391 baseEnd_6023391 := by
    simpa [prefixWord, tailWord_6023391, baseEnd_6023391] using wordTrace_append hprefix tailTrace_6023391
  have hstable : (prefixWord ++ tailWord_6023391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023391).length < 2 ^ (prefixWord ++ tailWord_6023391).sum := by decide
  have hdescent : baseEnd_6023391 < baseStart_6023391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023418 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2]
def baseStart_6023418 : Nat := 118140960795 + 6023418 * 2 ^ 59
def prefixEnd_6023418 : Nat := 4983230072969 + 3 ^ 40 * 6023418 * 2
def baseEnd_6023418 : Nat := 3092908616943619583073811

theorem tailTrace_6023418 : CollatzResearch.WordTrace tailWord_6023418 prefixEnd_6023418 3092908616943619583073811 := by
  unfold tailWord_6023418
  simp only [CollatzResearch.WordTrace]
  refine ⟨54923025723048194684773727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146461401928128519159396605 54923025723048194684773727)
  ·
    refine ⟨82384538584572292027160591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54923025723048194684773727 82384538584572292027160591)
    ·
      refine ⟨123576807876858438040740887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82384538584572292027160591 123576807876858438040740887)
      ·
        refine ⟨185365211815287657061111331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123576807876858438040740887 185365211815287657061111331)
        ·
          refine ⟨278047817722931485591666997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185365211815287657061111331 278047817722931485591666997)
          ·
            refine ⟨26066982911524826774218781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278047817722931485591666997 26066982911524826774218781)
            ·
              refine ⟨9775118591821810040332043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26066982911524826774218781 9775118591821810040332043)
              ·
                refine ⟨14662677887732715060498065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9775118591821810040332043 14662677887732715060498065)
                ·
                  refine ⟨10997008415799536295373549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14662677887732715060498065 10997008415799536295373549)
                  ·
                    refine ⟨4123878155924826110765081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10997008415799536295373549 4123878155924826110765081)
                    ·
                      refine ⟨3092908616943619583073811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123878155924826110765081 3092908616943619583073811)
                      ·
                        rfl

theorem cell23_6023418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_6023418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023418 prefixEnd_6023418 := by exact prefixLift 6023418
  have htrace : WordTrace (prefixWord ++ tailWord_6023418) baseStart_6023418 baseEnd_6023418 := by
    simpa [prefixWord, tailWord_6023418, baseEnd_6023418] using wordTrace_append hprefix tailTrace_6023418
  have hstable : (prefixWord ++ tailWord_6023418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023418).length < 2 ^ (prefixWord ++ tailWord_6023418).sum := by decide
  have hdescent : baseEnd_6023418 < baseStart_6023418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023424 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 1, 6]
def baseStart_6023424 : Nat := 118140960795 + 6023424 * 2 ^ 59
def prefixEnd_6023424 : Nat := 4983230072969 + 3 ^ 40 * 6023424 * 2
def baseEnd_6023424 : Nat := 1030970565942515519866261

theorem tailTrace_6023424 : CollatzResearch.WordTrace tailWord_6023424 prefixEnd_6023424 1030970565942515519866261 := by
  unfold tailWord_6023424
  simp only [CollatzResearch.WordTrace]
  refine ⟨109846160865085520881906663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146461547820114027842542217 109846160865085520881906663)
  ·
    refine ⟨164769241297628281322859995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109846160865085520881906663 164769241297628281322859995)
    ·
      refine ⟨247153861946442421984289993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164769241297628281322859995 247153861946442421984289993)
      ·
        refine ⟨185365396459831816488217495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247153861946442421984289993 185365396459831816488217495)
        ·
          refine ⟨278048094689747724732326243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185365396459831816488217495 278048094689747724732326243)
          ·
            refine ⟨417072142034621587098489365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278048094689747724732326243 417072142034621587098489365)
            ·
              refine ⟨19550256657872886895241689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 417072142034621587098489365 19550256657872886895241689)
              ·
                refine ⟨14662692493404665171431267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19550256657872886895241689 14662692493404665171431267)
                ·
                  refine ⟨21994038740106997757146901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14662692493404665171431267 21994038740106997757146901)
                  ·
                    refine ⟨1030970565942515519866261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21994038740106997757146901 1030970565942515519866261)
                    ·
                      rfl

theorem cell23_6023424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_6023424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023424 prefixEnd_6023424 := by exact prefixLift 6023424
  have htrace : WordTrace (prefixWord ++ tailWord_6023424) baseStart_6023424 baseEnd_6023424 := by
    simpa [prefixWord, tailWord_6023424, baseEnd_6023424] using wordTrace_append hprefix tailTrace_6023424
  have hstable : (prefixWord ++ tailWord_6023424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023424).length < 2 ^ (prefixWord ++ tailWord_6023424).sum := by decide
  have hdescent : baseEnd_6023424 < baseStart_6023424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023425 : List Nat := [1, 2, 4, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_6023425 : Nat := 118140960795 + 6023425 * 2 ^ 59
def prefixEnd_6023425 : Nat := 4983230072969 + 3 ^ 40 * 6023425 * 2
def baseEnd_6023425 : Nat := 3092912211308201055686279

theorem tailTrace_6023425 : CollatzResearch.WordTrace tailWord_6023425 prefixEnd_6023425 3092912211308201055686279 := by
  unfold tailWord_6023425
  simp only [CollatzResearch.WordTrace]
  refine ⟨219692358203167418934599729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146461572135444945956399819 219692358203167418934599729)
  ·
    refine ⟨164769268652375564200949797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219692358203167418934599729 164769268652375564200949797)
    ·
      refine ⟨30894237872320418287678087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164769268652375564200949797 30894237872320418287678087)
      ·
        refine ⟨46341356808480627431517131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30894237872320418287678087 46341356808480627431517131)
        ·
          refine ⟨69512035212720941147275697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46341356808480627431517131 69512035212720941147275697)
          ·
            refine ⟨52134026409540705860456773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69512035212720941147275697 52134026409540705860456773)
            ·
              refine ⟨9775129951788882348835645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52134026409540705860456773 9775129951788882348835645)
              ·
                refine ⟨3665673731920830880813367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9775129951788882348835645 3665673731920830880813367)
                ·
                  refine ⟨5498510597881246321220051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665673731920830880813367 5498510597881246321220051)
                  ·
                    refine ⟨8247765896821869481830077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5498510597881246321220051 8247765896821869481830077)
                    ·
                      refine ⟨3092912211308201055686279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8247765896821869481830077 3092912211308201055686279)
                      ·
                        rfl

theorem cell23_6023425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_6023425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023425 prefixEnd_6023425 := by exact prefixLift 6023425
  have htrace : WordTrace (prefixWord ++ tailWord_6023425) baseStart_6023425 baseEnd_6023425 := by
    simpa [prefixWord, tailWord_6023425, baseEnd_6023425] using wordTrace_append hprefix tailTrace_6023425
  have hstable : (prefixWord ++ tailWord_6023425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023425).length < 2 ^ (prefixWord ++ tailWord_6023425).sum := by decide
  have hdescent : baseEnd_6023425 < baseStart_6023425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023428 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_6023428 : Nat := 118140960795 + 6023428 * 2 ^ 59
def prefixEnd_6023428 : Nat := 4983230072969 + 3 ^ 40 * 6023428 * 2
def baseEnd_6023428 : Nat := 1030971250583388181316255

theorem tailTrace_6023428 : CollatzResearch.WordTrace tailWord_6023428 prefixEnd_6023428 1030971250583388181316255 := by
  unfold tailWord_6023428
  simp only [CollatzResearch.WordTrace]
  refine ⟨109846233811078275223479469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146461645081437700297972625 109846233811078275223479469)
  ·
    refine ⟨41192337679154353208804801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109846233811078275223479469 41192337679154353208804801)
    ·
      refine ⟨30894253259365764906603601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41192337679154353208804801 30894253259365764906603601)
      ·
        refine ⟨23170689944524323679952701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30894253259365764906603601 23170689944524323679952701)
        ·
          refine ⟨8689008729196621379982263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23170689944524323679952701 8689008729196621379982263)
          ·
            refine ⟨13033513093794932069973395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8689008729196621379982263 13033513093794932069973395)
            ·
              refine ⟨19550269640692398104960093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13033513093794932069973395 19550269640692398104960093)
              ·
                refine ⟨7331351115259649289360035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19550269640692398104960093 7331351115259649289360035)
                ·
                  refine ⟨10997026672889473934040053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7331351115259649289360035 10997026672889473934040053)
                  ·
                    refine ⟨1030971250583388181316255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10997026672889473934040053 1030971250583388181316255)
                    ·
                      rfl

theorem cell23_6023428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_6023428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023428 prefixEnd_6023428 := by exact prefixLift 6023428
  have htrace : WordTrace (prefixWord ++ tailWord_6023428) baseStart_6023428 baseEnd_6023428 := by
    simpa [prefixWord, tailWord_6023428, baseEnd_6023428] using wordTrace_append hprefix tailTrace_6023428
  have hstable : (prefixWord ++ tailWord_6023428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023428).length < 2 ^ (prefixWord ++ tailWord_6023428).sum := by decide
  have hdescent : baseEnd_6023428 < baseStart_6023428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023441 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 4, 4]
def baseStart_6023441 : Nat := 118140960795 + 6023441 * 2 ^ 59
def prefixEnd_6023441 : Nat := 4983230072969 + 3 ^ 40 * 6023441 * 2
def baseEnd_6023441 : Nat := 1030973475666224331028735

theorem tailTrace_6023441 : CollatzResearch.WordTrace tailWord_6023441 prefixEnd_6023441 1030973475666224331028735 := by
  unfold tailWord_6023441
  simp only [CollatzResearch.WordTrace]
  refine ⟨219692941771109453667182177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146461961180739635778121451 219692941771109453667182177)
  ·
    refine ⟨164769706328332090250386633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219692941771109453667182177 164769706328332090250386633)
    ·
      refine ⟨123577279746249067687789975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164769706328332090250386633 123577279746249067687789975)
      ·
        refine ⟨185365919619373601531684963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123577279746249067687789975 185365919619373601531684963)
        ·
          refine ⟨278048879429060402297527445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185365919619373601531684963 278048879429060402297527445)
          ·
            refine ⟨13033541223237206357696599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 278048879429060402297527445 13033541223237206357696599)
            ·
              refine ⟨19550311834855809536544899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13033541223237206357696599 19550311834855809536544899)
              ·
                refine ⟨29325467752283714304817349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19550311834855809536544899 29325467752283714304817349)
                ·
                  refine ⟨5498525203553196432153253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29325467752283714304817349 5498525203553196432153253)
                  ·
                    refine ⟨1030973475666224331028735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5498525203553196432153253 1030973475666224331028735)
                    ·
                      rfl

theorem cell23_6023441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_6023441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023441 prefixEnd_6023441 := by exact prefixLift 6023441
  have htrace : WordTrace (prefixWord ++ tailWord_6023441) baseStart_6023441 baseEnd_6023441 := by
    simpa [prefixWord, tailWord_6023441, baseEnd_6023441] using wordTrace_append hprefix tailTrace_6023441
  have hstable : (prefixWord ++ tailWord_6023441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023441).length < 2 ^ (prefixWord ++ tailWord_6023441).sum := by decide
  have hdescent : baseEnd_6023441 < baseStart_6023441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023458 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_6023458 : Nat := 118140960795 + 6023458 * 2 ^ 59
def prefixEnd_6023458 : Nat := 4983230072969 + 3 ^ 40 * 6023458 * 2
def baseEnd_6023458 : Nat := 1030976385389933142191209

theorem tailTrace_6023458 : CollatzResearch.WordTrace tailWord_6023458 prefixEnd_6023458 1030976385389933142191209 := by
  unfold tailWord_6023458
  simp only [CollatzResearch.WordTrace]
  refine ⟨54923390453011966392637757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146462374541365243713700685 54923390453011966392637757)
  ·
    refine ⟨20596271419879487397239159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54923390453011966392637757 20596271419879487397239159)
    ·
      refine ⟨30894407129819231095858739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20596271419879487397239159 30894407129819231095858739)
      ·
        refine ⟨46341610694728846643788109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30894407129819231095858739 46341610694728846643788109)
        ·
          refine ⟨17378104010523317491420541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46341610694728846643788109 17378104010523317491420541)
          ·
            refine ⟨6516789003946244059282703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17378104010523317491420541 6516789003946244059282703)
            ·
              refine ⟨9775183505919366088924055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6516789003946244059282703 9775183505919366088924055)
              ·
                refine ⟨14662775258879049133386083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9775183505919366088924055 14662775258879049133386083)
                ·
                  refine ⟨21994162888318573700079125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14662775258879049133386083 21994162888318573700079125)
                  ·
                    refine ⟨1030976385389933142191209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21994162888318573700079125 1030976385389933142191209)
                    ·
                      rfl

theorem cell23_6023458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_6023458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023458 prefixEnd_6023458 := by exact prefixLift 6023458
  have htrace : WordTrace (prefixWord ++ tailWord_6023458) baseStart_6023458 baseEnd_6023458 := by
    simpa [prefixWord, tailWord_6023458, baseEnd_6023458] using wordTrace_append hprefix tailTrace_6023458
  have hstable : (prefixWord ++ tailWord_6023458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023458).length < 2 ^ (prefixWord ++ tailWord_6023458).sum := by decide
  have hdescent : baseEnd_6023458 < baseStart_6023458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023461 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 6]
def baseStart_6023461 : Nat := 118140960795 + 6023461 * 2 ^ 59
def prefixEnd_6023461 : Nat := 4983230072969 + 3 ^ 40 * 6023461 * 2
def baseEnd_6023461 : Nat := 3092930696611762914836113

theorem tailTrace_6023461 : CollatzResearch.WordTrace tailWord_6023461 prefixEnd_6023461 3092930696611762914836113 := by
  unfold tailWord_6023461
  simp only [CollatzResearch.WordTrace]
  refine ⟨219693671231036997082910237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146462447487357998055273491 219693671231036997082910237)
  ·
    refine ⟨82385126711638873906091339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219693671231036997082910237 82385126711638873906091339)
    ·
      refine ⟨123577690067458310859137009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82385126711638873906091339 123577690067458310859137009)
      ·
        refine ⟨92683267550593733144352757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123577690067458310859137009 92683267550593733144352757)
        ·
          refine ⟨8689056332868162482283071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92683267550593733144352757 8689056332868162482283071)
          ·
            refine ⟨13033584499302243723424607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8689056332868162482283071 13033584499302243723424607)
            ·
              refine ⟨19550376748953365585136911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13033584499302243723424607 19550376748953365585136911)
              ·
                refine ⟨29325565123430048377705367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19550376748953365585136911 29325565123430048377705367)
                ·
                  refine ⟨43988347685145072566558051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29325565123430048377705367 43988347685145072566558051)
                  ·
                    refine ⟨65982521527717608849837077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43988347685145072566558051 65982521527717608849837077)
                    ·
                      refine ⟨3092930696611762914836113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65982521527717608849837077 3092930696611762914836113)
                      ·
                        rfl

theorem cell23_6023461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_6023461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023461 prefixEnd_6023461 := by exact prefixLift 6023461
  have htrace : WordTrace (prefixWord ++ tailWord_6023461) baseStart_6023461 baseEnd_6023461 := by
    simpa [prefixWord, tailWord_6023461, baseEnd_6023461] using wordTrace_append hprefix tailTrace_6023461
  have hstable : (prefixWord ++ tailWord_6023461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023461).length < 2 ^ (prefixWord ++ tailWord_6023461).sum := by decide
  have hdescent : baseEnd_6023461 < baseStart_6023461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023482 : List Nat := [3, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2]
def baseStart_6023482 : Nat := 118140960795 + 6023482 * 2 ^ 59
def prefixEnd_6023482 : Nat := 4983230072969 + 3 ^ 40 * 6023482 * 2
def baseEnd_6023482 : Nat := 3092941479705507332673517

theorem tailTrace_6023482 : CollatzResearch.WordTrace tailWord_6023482 prefixEnd_6023482 3092941479705507332673517 := by
  unfold tailWord_6023482
  simp only [CollatzResearch.WordTrace]
  refine ⟨54923609290990229417356175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146462958109307278446283133 54923609290990229417356175)
  ·
    refine ⟨82385413936485344126034263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54923609290990229417356175 82385413936485344126034263)
    ·
      refine ⟨123578120904728016189051395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82385413936485344126034263 123578120904728016189051395)
      ·
        refine ⟨185367181357092024283577093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123578120904728016189051395 185367181357092024283577093)
        ·
          refine ⟨34756346504454754553170705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185367181357092024283577093 34756346504454754553170705)
          ·
            refine ⟨26067259878341065914878029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34756346504454754553170705 26067259878341065914878029)
            ·
              refine ⟨9775222454377899718079261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26067259878341065914878029 9775222454377899718079261)
              ·
                refine ⟨3665708420391712394279723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9775222454377899718079261 3665708420391712394279723)
                ·
                  refine ⟨5498562630587568591419585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665708420391712394279723 5498562630587568591419585)
                  ·
                    refine ⟨4123921972940676443564689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5498562630587568591419585 4123921972940676443564689)
                    ·
                      refine ⟨3092941479705507332673517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123921972940676443564689 3092941479705507332673517)
                      ·
                        rfl

theorem cell23_6023482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2].length) (baseStart_6023482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023482 prefixEnd_6023482 := by exact prefixLift 6023482
  have htrace : WordTrace (prefixWord ++ tailWord_6023482) baseStart_6023482 baseEnd_6023482 := by
    simpa [prefixWord, tailWord_6023482, baseEnd_6023482] using wordTrace_append hprefix tailTrace_6023482
  have hstable : (prefixWord ++ tailWord_6023482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023482).length < 2 ^ (prefixWord ++ tailWord_6023482).sum := by decide
  have hdescent : baseEnd_6023482 < baseStart_6023482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023514 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_6023514 : Nat := 118140960795 + 6023514 * 2 ^ 59
def prefixEnd_6023514 : Nat := 4983230072969 + 3 ^ 40 * 6023514 * 2
def baseEnd_6023514 : Nat := 1030985970362150402491123

theorem tailTrace_6023514 : CollatzResearch.WordTrace tailWord_6023514 prefixEnd_6023514 1030985970362150402491123 := by
  unfold tailWord_6023514
  simp only [CollatzResearch.WordTrace]
  refine ⟨54923901074961246783647399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146463736199896658089726397 54923901074961246783647399)
  ·
    refine ⟨82385851612441870175471099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54923901074961246783647399 82385851612441870175471099)
    ·
      refine ⟨123578777418662805263206649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82385851612441870175471099 123578777418662805263206649)
      ·
        refine ⟨92684083063997103947404987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123578777418662805263206649 92684083063997103947404987)
        ·
          refine ⟨139026124595995655921107481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92684083063997103947404987 139026124595995655921107481)
          ·
            refine ⟨104269593446996741940830611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139026124595995655921107481 104269593446996741940830611)
            ·
              refine ⟨156404390170495112911245917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104269593446996741940830611 156404390170495112911245917)
              ·
                refine ⟨58651646313935667341717219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156404390170495112911245917 58651646313935667341717219)
                ·
                  refine ⟨87977469470903501012575829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58651646313935667341717219 87977469470903501012575829)
                  ·
                    refine ⟨1030985970362150402491123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87977469470903501012575829 1030985970362150402491123)
                    ·
                      rfl

theorem cell23_6023514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_6023514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023514 prefixEnd_6023514 := by exact prefixLift 6023514
  have htrace : WordTrace (prefixWord ++ tailWord_6023514) baseStart_6023514 baseEnd_6023514 := by
    simpa [prefixWord, tailWord_6023514, baseEnd_6023514] using wordTrace_append hprefix tailTrace_6023514
  have hstable : (prefixWord ++ tailWord_6023514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023514).length < 2 ^ (prefixWord ++ tailWord_6023514).sum := by decide
  have hdescent : baseEnd_6023514 < baseStart_6023514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023525 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 1, 3, 2]
def baseStart_6023525 : Nat := 118140960795 + 6023525 * 2 ^ 59
def prefixEnd_6023525 : Nat := 4983230072969 + 3 ^ 40 * 6023525 * 2
def baseEnd_6023525 : Nat := 3092963559373650664435819

theorem tailTrace_6023525 : CollatzResearch.WordTrace tailWord_6023525 prefixEnd_6023525 3092963559373650664435819 := by
  unfold tailWord_6023525
  simp only [CollatzResearch.WordTrace]
  refine ⟨219696005502805136013240029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146464003668536757342160019 219696005502805136013240029)
  ·
    refine ⟨82386002063551926004965011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219696005502805136013240029 82386002063551926004965011)
    ·
      refine ⟨123579003095327889007447517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82386002063551926004965011 123579003095327889007447517)
      ·
        refine ⟨46342126160747958377792819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123579003095327889007447517 46342126160747958377792819)
        ·
          refine ⟨69513189241121937566689229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46342126160747958377792819 69513189241121937566689229)
          ·
            refine ⟨26067445965420726587508461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69513189241121937566689229 26067445965420726587508461)
            ·
              refine ⟨9775292237032772470315673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26067445965420726587508461 9775292237032772470315673)
              ·
                refine ⟨7331469177774579352736755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9775292237032772470315673 7331469177774579352736755)
                ·
                  refine ⟨10997203766661869029105133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7331469177774579352736755 10997203766661869029105133)
                  ·
                    refine ⟨4123951412498200885914425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10997203766661869029105133 4123951412498200885914425)
                    ·
                      refine ⟨3092963559373650664435819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123951412498200885914425 3092963559373650664435819)
                      ·
                        rfl

theorem cell23_6023525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_6023525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023525 prefixEnd_6023525 := by exact prefixLift 6023525
  have htrace : WordTrace (prefixWord ++ tailWord_6023525) baseStart_6023525 baseEnd_6023525 := by
    simpa [prefixWord, tailWord_6023525, baseEnd_6023525] using wordTrace_append hprefix tailTrace_6023525
  have hstable : (prefixWord ++ tailWord_6023525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023525).length < 2 ^ (prefixWord ++ tailWord_6023525).sum := by decide
  have hdescent : baseEnd_6023525 < baseStart_6023525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023538 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 3, 4, 2]
def baseStart_6023538 : Nat := 118140960795 + 6023538 * 2 ^ 59
def prefixEnd_6023538 : Nat := 4983230072969 + 3 ^ 40 * 6023538 * 2
def baseEnd_6023538 : Nat := 3092970234622159113573259

theorem tailTrace_6023538 : CollatzResearch.WordTrace tailWord_6023538 prefixEnd_6023538 3092970234622159113573259 := by
  unfold tailWord_6023538
  simp only [CollatzResearch.WordTrace]
  refine ⟨54924119912939509808365817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146464319767838692822308845 54924119912939509808365817)
  ·
    refine ⟨41193089934704632356274363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54924119912939509808365817 41193089934704632356274363)
    ·
      refine ⟨61789634902056948534411545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41193089934704632356274363 61789634902056948534411545)
      ·
        refine ⟨46342226176542711400808659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61789634902056948534411545 46342226176542711400808659)
        ·
          refine ⟨69513339264814067101212989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46342226176542711400808659 69513339264814067101212989)
          ·
            refine ⟨26067502224305275162954871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69513339264814067101212989 26067502224305275162954871)
            ·
              refine ⟨39101253336457912744432307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26067502224305275162954871 39101253336457912744432307)
              ·
                refine ⟨58651880004686869116648461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39101253336457912744432307 58651880004686869116648461)
                ·
                  refine ⟨21994455001757575918743173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58651880004686869116648461 21994455001757575918743173)
                  ·
                    refine ⟨4123960312829545484764345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21994455001757575918743173 4123960312829545484764345)
                    ·
                      refine ⟨3092970234622159113573259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123960312829545484764345 3092970234622159113573259)
                      ·
                        rfl

theorem cell23_6023538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_6023538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023538 prefixEnd_6023538 := by exact prefixLift 6023538
  have htrace : WordTrace (prefixWord ++ tailWord_6023538) baseStart_6023538 baseEnd_6023538 := by
    simpa [prefixWord, tailWord_6023538, baseEnd_6023538] using wordTrace_append hprefix tailTrace_6023538
  have hstable : (prefixWord ++ tailWord_6023538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023538).length < 2 ^ (prefixWord ++ tailWord_6023538).sum := by decide
  have hdescent : baseEnd_6023538 < baseStart_6023538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023572 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_6023572 : Nat := 118140960795 + 6023572 * 2 ^ 59
def prefixEnd_6023572 : Nat := 4983230072969 + 3 ^ 40 * 6023572 * 2
def baseEnd_6023572 : Nat := 3092987692964411980548103

theorem tailTrace_6023572 : CollatzResearch.WordTrace tailWord_6023572 prefixEnd_6023572 3092987692964411980548103 := by
  unfold tailWord_6023572
  simp only [CollatzResearch.WordTrace]
  refine ⟨109848859866817431520100485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146465146489089908693467313 109848859866817431520100485)
  ·
    refine ⟨20596661225028268410018841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109848859866817431520100485 20596661225028268410018841)
    ·
      refine ⟨15447495918771201307514131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20596661225028268410018841 15447495918771201307514131)
      ·
        refine ⟨23171243878156801961271197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15447495918771201307514131 23171243878156801961271197)
        ·
          refine ⟨8689216454308800735476699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23171243878156801961271197 8689216454308800735476699)
          ·
            refine ⟨13033824681463201103215049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8689216454308800735476699 13033824681463201103215049)
            ·
              refine ⟨9775368511097400827411287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13033824681463201103215049 9775368511097400827411287)
              ·
                refine ⟨14663052766646101241116931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9775368511097400827411287 14663052766646101241116931)
                ·
                  refine ⟨21994579149969151861675397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14663052766646101241116931 21994579149969151861675397)
                  ·
                    refine ⟨4123983590619215974064137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21994579149969151861675397 4123983590619215974064137)
                    ·
                      refine ⟨3092987692964411980548103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4123983590619215974064137 3092987692964411980548103)
                      ·
                        rfl

theorem cell23_6023572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_6023572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023572 prefixEnd_6023572 := by exact prefixLift 6023572
  have htrace : WordTrace (prefixWord ++ tailWord_6023572) baseStart_6023572 baseEnd_6023572 := by
    simpa [prefixWord, tailWord_6023572, baseEnd_6023572] using wordTrace_append hprefix tailTrace_6023572
  have hstable : (prefixWord ++ tailWord_6023572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023572).length < 2 ^ (prefixWord ++ tailWord_6023572).sum := by decide
  have hdescent : baseEnd_6023572 < baseStart_6023572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023638 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_6023638 : Nat := 118140960795 + 6023638 * 2 ^ 59
def prefixEnd_6023638 : Nat := 4983230072969 + 3 ^ 40 * 6023638 * 2
def baseEnd_6023638 : Nat := 1031007194229202907440933

theorem tailTrace_6023638 : CollatzResearch.WordTrace tailWord_6023638 prefixEnd_6023638 1031007194229202907440933 := by
  unfold tailWord_6023638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13731257934462234769506473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146466751300930504208069045 13731257934462234769506473)
  ·
    refine ⟨10298443450846676077129855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13731257934462234769506473 10298443450846676077129855)
    ·
      refine ⟨15447665176270014115694783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10298443450846676077129855 15447665176270014115694783)
      ·
        refine ⟨23171497764405021173542175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15447665176270014115694783 23171497764405021173542175)
        ·
          refine ⟨34757246646607531760313263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23171497764405021173542175 34757246646607531760313263)
          ·
            refine ⟨52135869969911297640469895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34757246646607531760313263 52135869969911297640469895)
            ·
              refine ⟨78203804954866946460704843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52135869969911297640469895 78203804954866946460704843)
              ·
                refine ⟨117305707432300419691057265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78203804954866946460704843 117305707432300419691057265)
                ·
                  refine ⟨87979280574225314768292949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117305707432300419691057265 87979280574225314768292949)
                  ·
                    refine ⟨1031007194229202907440933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87979280574225314768292949 1031007194229202907440933)
                    ·
                      rfl

theorem cell23_6023638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_6023638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023638 prefixEnd_6023638 := by exact prefixLift 6023638
  have htrace : WordTrace (prefixWord ++ tailWord_6023638) baseStart_6023638 baseEnd_6023638 := by
    simpa [prefixWord, tailWord_6023638, baseEnd_6023638] using wordTrace_append hprefix tailTrace_6023638
  have hstable : (prefixWord ++ tailWord_6023638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023638).length < 2 ^ (prefixWord ++ tailWord_6023638).sum := by decide
  have hdescent : baseEnd_6023638 < baseStart_6023638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023641 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_6023641 : Nat := 118140960795 + 6023641 * 2 ^ 59
def prefixEnd_6023641 : Nat := 4983230072969 + 3 ^ 40 * 6023641 * 2
def baseEnd_6023641 : Nat := 3093023123129572210585285

theorem tailTrace_6023641 : CollatzResearch.WordTrace tailWord_6023641 prefixEnd_6023641 3093023123129572210585285 := by
  unfold tailWord_6023641
  simp only [CollatzResearch.WordTrace]
  refine ⟨219700236370384887824462777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146466824246923258549641851 219700236370384887824462777)
  ·
    refine ⟨164775177277788665868347083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219700236370384887824462777 164775177277788665868347083)
    ·
      refine ⟨247162765916682998802520625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164775177277788665868347083 247162765916682998802520625)
      ·
        refine ⟨185372074437512249101890469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247162765916682998802520625 185372074437512249101890469)
        ·
          refine ⟨34757263957033546706604463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185372074437512249101890469 34757263957033546706604463)
          ·
            refine ⟨52135895935550320059906695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34757263957033546706604463 52135895935550320059906695)
            ·
              refine ⟨78203843903325480089860043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52135895935550320059906695 78203843903325480089860043)
              ·
                refine ⟨117305765854988220134790065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78203843903325480089860043 117305765854988220134790065)
                ·
                  refine ⟨87979324391241165101092549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117305765854988220134790065 87979324391241165101092549)
                  ·
                    refine ⟨16496123323357718456454853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87979324391241165101092549 16496123323357718456454853)
                    ·
                      refine ⟨3093023123129572210585285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16496123323357718456454853 3093023123129572210585285)
                      ·
                        rfl

theorem cell23_6023641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_6023641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023641 prefixEnd_6023641 := by exact prefixLift 6023641
  have htrace : WordTrace (prefixWord ++ tailWord_6023641) baseStart_6023641 baseEnd_6023641 := by
    simpa [prefixWord, tailWord_6023641, baseEnd_6023641] using wordTrace_append hprefix tailTrace_6023641
  have hstable : (prefixWord ++ tailWord_6023641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023641).length < 2 ^ (prefixWord ++ tailWord_6023641).sum := by decide
  have hdescent : baseEnd_6023641 < baseStart_6023641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023648 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 3]
def baseStart_6023648 : Nat := 118140960795 + 6023648 * 2 ^ 59
def prefixEnd_6023648 : Nat := 4983230072969 + 3 ^ 40 * 6023648 * 2
def baseEnd_6023648 : Nat := 3093026717494153683197753

theorem tailTrace_6023648 : CollatzResearch.WordTrace tailWord_6023648 prefixEnd_6023648 3093026717494153683197753 := by
  unfold tailWord_6023648
  simp only [CollatzResearch.WordTrace]
  refine ⟨109850245840679764009983799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146466994454239685346645065 109850245840679764009983799)
  ·
    refine ⟨164775368761019646014975699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109850245840679764009983799 164775368761019646014975699)
    ·
      refine ⟨247163053141529469022463549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164775368761019646014975699 247163053141529469022463549)
      ·
        refine ⟨92686144928073550883423831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247163053141529469022463549 92686144928073550883423831)
        ·
          refine ⟨139029217392110326325135747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92686144928073550883423831 139029217392110326325135747)
          ·
            refine ⟨208543826088165489487703621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139029217392110326325135747 208543826088165489487703621)
            ·
              refine ⟨39101967391531029278944429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208543826088165489487703621 39101967391531029278944429)
              ·
                refine ⟨14663237771824135979604161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39101967391531029278944429 14663237771824135979604161)
                ·
                  refine ⟨10997428328868101984703121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14663237771824135979604161 10997428328868101984703121)
                  ·
                    refine ⟨8248071246651076488527341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10997428328868101984703121 8248071246651076488527341)
                    ·
                      refine ⟨3093026717494153683197753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8248071246651076488527341 3093026717494153683197753)
                      ·
                        rfl

theorem cell23_6023648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_6023648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023648 prefixEnd_6023648 := by exact prefixLift 6023648
  have htrace : WordTrace (prefixWord ++ tailWord_6023648) baseStart_6023648 baseEnd_6023648 := by
    simpa [prefixWord, tailWord_6023648, baseEnd_6023648] using wordTrace_append hprefix tailTrace_6023648
  have hstable : (prefixWord ++ tailWord_6023648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023648).length < 2 ^ (prefixWord ++ tailWord_6023648).sum := by decide
  have hdescent : baseEnd_6023648 < baseStart_6023648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023672 : List Nat := [2, 1, 2, 1, 1, 4, 5, 2, 1, 4]
def baseStart_6023672 : Nat := 118140960795 + 6023672 * 2 ^ 59
def prefixEnd_6023672 : Nat := 4983230072969 + 3 ^ 40 * 6023672 * 2
def baseEnd_6023672 : Nat := 1031013013676620529765881

theorem tailTrace_6023672 : CollatzResearch.WordTrace tailWord_6023672 prefixEnd_6023672 1031013013676620529765881 := by
  unfold tailWord_6023672
  simp only [CollatzResearch.WordTrace]
  refine ⟨109850683516636290059420635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146467578022181720079227513 109850683516636290059420635)
  ·
    refine ⟨164776025274954435089130953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109850683516636290059420635 164776025274954435089130953)
    ·
      refine ⟨123582018956215826316848215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164776025274954435089130953 123582018956215826316848215)
      ·
        refine ⟨185373028434323739475272323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123582018956215826316848215 185373028434323739475272323)
        ·
          refine ⟨278059542651485609212908485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185373028434323739475272323 278059542651485609212908485)
          ·
            refine ⟨52136164247153551727420341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278059542651485609212908485 52136164247153551727420341)
            ·
              refine ⟨4887765398170645474445657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52136164247153551727420341 4887765398170645474445657)
              ·
                refine ⟨3665824048627984105834243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4887765398170645474445657 3665824048627984105834243)
                ·
                  refine ⟨5498736072941976158751365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665824048627984105834243 5498736072941976158751365)
                  ·
                    refine ⟨1031013013676620529765881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5498736072941976158751365 1031013013676620529765881)
                    ·
                      rfl

theorem cell23_6023672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_6023672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023672 prefixEnd_6023672 := by exact prefixLift 6023672
  have htrace : WordTrace (prefixWord ++ tailWord_6023672) baseStart_6023672 baseEnd_6023672 := by
    simpa [prefixWord, tailWord_6023672, baseEnd_6023672] using wordTrace_append hprefix tailTrace_6023672
  have hstable : (prefixWord ++ tailWord_6023672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023672).length < 2 ^ (prefixWord ++ tailWord_6023672).sum := by decide
  have hdescent : baseEnd_6023672 < baseStart_6023672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023722 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_6023722 : Nat := 118140960795 + 6023722 * 2 ^ 59
def prefixEnd_6023722 : Nat := 4983230072969 + 3 ^ 40 * 6023722 * 2
def baseEnd_6023722 : Nat := 3093064715062586393672413

theorem tailTrace_6023722 : CollatzResearch.WordTrace tailWord_6023722 prefixEnd_6023722 3093064715062586393672413 := by
  unfold tailWord_6023722
  simp only [CollatzResearch.WordTrace]
  refine ⟨54925797670772859664540355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146468793788727625772107613 54925797670772859664540355)
  ·
    refine ⟨82388696506159289496810533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54925797670772859664540355 82388696506159289496810533)
    ·
      refine ⟨15447880594904866780651975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82388696506159289496810533 15447880594904866780651975)
      ·
        refine ⟨23171820892357300170977963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15447880594904866780651975 23171820892357300170977963)
        ·
          refine ⟨34757731338535950256466945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23171820892357300170977963 34757731338535950256466945)
          ·
            refine ⟨26068298503901962692350209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34757731338535950256466945 26068298503901962692350209)
            ·
              refine ⟨19551223877926472019262657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26068298503901962692350209 19551223877926472019262657)
              ·
                refine ⟨14663417908444854014446993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19551223877926472019262657 14663417908444854014446993)
                ·
                  refine ⟨10997563431333640510835245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14663417908444854014446993 10997563431333640510835245)
                  ·
                    refine ⟨4124086286750115191563217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10997563431333640510835245 4124086286750115191563217)
                    ·
                      refine ⟨3093064715062586393672413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124086286750115191563217 3093064715062586393672413)
                      ·
                        rfl

theorem cell23_6023722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_6023722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023722 prefixEnd_6023722 := by exact prefixLift 6023722
  have htrace : WordTrace (prefixWord ++ tailWord_6023722) baseStart_6023722 baseEnd_6023722 := by
    simpa [prefixWord, tailWord_6023722, baseEnd_6023722] using wordTrace_append hprefix tailTrace_6023722
  have hstable : (prefixWord ++ tailWord_6023722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023722).length < 2 ^ (prefixWord ++ tailWord_6023722).sum := by decide
  have hdescent : baseEnd_6023722 < baseStart_6023722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023728 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 4, 4]
def baseStart_6023728 : Nat := 118140960795 + 6023728 * 2 ^ 59
def prefixEnd_6023728 : Nat := 4983230072969 + 3 ^ 40 * 6023728 * 2
def baseEnd_6023728 : Nat := 1031022598648837790065795

theorem tailTrace_6023728 : CollatzResearch.WordTrace tailWord_6023728 prefixEnd_6023728 1031022598648837790065795 := by
  unfold tailWord_6023728
  simp only [CollatzResearch.WordTrace]
  refine ⟨109851704760534850841439919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146468939680713134455253225 109851704760534850841439919)
  ·
    refine ⟨164777557140802276262159879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109851704760534850841439919 164777557140802276262159879)
    ·
      refine ⟨247166335711203414393239819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164777557140802276262159879 247166335711203414393239819)
      ·
        refine ⟨370749503566805121589859729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247166335711203414393239819 370749503566805121589859729)
        ·
          refine ⟨278062127675103841192394797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370749503566805121589859729 278062127675103841192394797)
          ·
            refine ⟨104273297878163940447148049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278062127675103841192394797 104273297878163940447148049)
            ·
              refine ⟨78204973408622955335361037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104273297878163940447148049 78204973408622955335361037)
              ·
                refine ⟨29326865028233608250760389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78204973408622955335361037 29326865028233608250760389)
                ·
                  refine ⟨5498787192793801547017573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29326865028233608250760389 5498787192793801547017573)
                  ·
                    refine ⟨1031022598648837790065795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5498787192793801547017573 1031022598648837790065795)
                    ·
                      rfl

theorem cell23_6023728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4, 4].length) (baseStart_6023728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023728 prefixEnd_6023728 := by exact prefixLift 6023728
  have htrace : WordTrace (prefixWord ++ tailWord_6023728) baseStart_6023728 baseEnd_6023728 := by
    simpa [prefixWord, tailWord_6023728, baseEnd_6023728] using wordTrace_append hprefix tailTrace_6023728
  have hstable : (prefixWord ++ tailWord_6023728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023728).length < 2 ^ (prefixWord ++ tailWord_6023728).sum := by decide
  have hdescent : baseEnd_6023728 < baseStart_6023728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023729 : List Nat := [1, 2, 2, 3, 1, 1, 6, 2, 1, 1, 3]
def baseStart_6023729 : Nat := 118140960795 + 6023729 * 2 ^ 59
def prefixEnd_6023729 : Nat := 4983230072969 + 3 ^ 40 * 6023729 * 2
def baseEnd_6023729 : Nat := 3093068309427167866284881

theorem tailTrace_6023729 : CollatzResearch.WordTrace tailWord_6023729 prefixEnd_6023729 3093068309427167866284881 := by
  unfold tailWord_6023729
  simp only [CollatzResearch.WordTrace]
  refine ⟨219703445994066078853666241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146468963996044052569110827 219703445994066078853666241)
  ·
    refine ⟨164777584495549559140249681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219703445994066078853666241 164777584495549559140249681)
    ·
      refine ⟨123583188371662169355187261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164777584495549559140249681 123583188371662169355187261)
      ·
        refine ⟨46343695639373313508195223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123583188371662169355187261 46343695639373313508195223)
        ·
          refine ⟨69515543459059970262292835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46343695639373313508195223 69515543459059970262292835)
          ·
            refine ⟨104273315188589955393439253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69515543459059970262292835 104273315188589955393439253)
            ·
              refine ⟨4887811649465154159067465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104273315188589955393439253 4887811649465154159067465)
              ·
                refine ⟨3665858737098865619300599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4887811649465154159067465 3665858737098865619300599)
                ·
                  refine ⟨5498788105648298428950899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665858737098865619300599 5498788105648298428950899)
                  ·
                    refine ⟨8248182158472447643426349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5498788105648298428950899 8248182158472447643426349)
                    ·
                      refine ⟨3093068309427167866284881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8248182158472447643426349 3093068309427167866284881)
                      ·
                        rfl

theorem cell23_6023729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_6023729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023729 prefixEnd_6023729 := by exact prefixLift 6023729
  have htrace : WordTrace (prefixWord ++ tailWord_6023729) baseStart_6023729 baseEnd_6023729 := by
    simpa [prefixWord, tailWord_6023729, baseEnd_6023729] using wordTrace_append hprefix tailTrace_6023729
  have hstable : (prefixWord ++ tailWord_6023729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023729).length < 2 ^ (prefixWord ++ tailWord_6023729).sum := by decide
  have hdescent : baseEnd_6023729 < baseStart_6023729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023745 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 1, 6]
def baseStart_6023745 : Nat := 118140960795 + 6023745 * 2 ^ 59
def prefixEnd_6023745 : Nat := 4983230072969 + 3 ^ 40 * 6023745 * 2
def baseEnd_6023745 : Nat := 1031025508372546601228269

theorem tailTrace_6023745 : CollatzResearch.WordTrace tailWord_6023745 prefixEnd_6023745 1031025508372546601228269 := by
  unfold tailWord_6023745
  simp only [CollatzResearch.WordTrace]
  refine ⟨219704029562008113586248689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146469353041338742390832459 219704029562008113586248689)
  ·
    refine ⟨164778022171506085189686517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219704029562008113586248689 164778022171506085189686517)
    ·
      refine ⟨15447939578578695486533111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164778022171506085189686517 15447939578578695486533111)
      ·
        refine ⟨23171909367868043229799667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15447939578578695486533111 23171909367868043229799667)
        ·
          refine ⟨34757864051802064844699501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23171909367868043229799667 34757864051802064844699501)
          ·
            refine ⟨13034199019425774316762313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34757864051802064844699501 13034199019425774316762313)
            ·
              refine ⟨9775649264569330737571735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13034199019425774316762313 9775649264569330737571735)
              ·
                refine ⟨14663473896853996106357603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9775649264569330737571735 14663473896853996106357603)
                ·
                  refine ⟨21995210845280994159536405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14663473896853996106357603 21995210845280994159536405)
                  ·
                    refine ⟨1031025508372546601228269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21995210845280994159536405 1031025508372546601228269)
                    ·
                      rfl

theorem cell23_6023745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_6023745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023745 prefixEnd_6023745 := by exact prefixLift 6023745
  have htrace : WordTrace (prefixWord ++ tailWord_6023745) baseStart_6023745 baseEnd_6023745 := by
    simpa [prefixWord, tailWord_6023745, baseEnd_6023745] using wordTrace_append hprefix tailTrace_6023745
  have hstable : (prefixWord ++ tailWord_6023745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023745).length < 2 ^ (prefixWord ++ tailWord_6023745).sum := by decide
  have hdescent : baseEnd_6023745 < baseStart_6023745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023795 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 3, 3, 2]
def baseStart_6023795 : Nat := 118140960795 + 6023795 * 2 ^ 59
def prefixEnd_6023795 : Nat := 4983230072969 + 3 ^ 40 * 6023795 * 2
def baseEnd_6023795 : Nat := 3093102199150364608059577

theorem tailTrace_6023795 : CollatzResearch.WordTrace tailWord_6023795 prefixEnd_6023795 3093102199150364608059577 := by
  unfold tailWord_6023795
  simp only [CollatzResearch.WordTrace]
  refine ⟨219705853211826972125568839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146470568807884648083712559 219705853211826972125568839)
  ·
    refine ⟨329558779817740458188353259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219705853211826972125568839 329558779817740458188353259)
    ·
      refine ⟨494338169726610687282529889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329558779817740458188353259 494338169726610687282529889)
      ·
        refine ⟨370753627294958015461897417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494338169726610687282529889 370753627294958015461897417)
        ·
          refine ⟨278065220471218511596423063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370753627294958015461897417 278065220471218511596423063)
          ·
            refine ⟨417097830706827767394634595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278065220471218511596423063 417097830706827767394634595)
            ·
              refine ⟨625646746060241651091951893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417097830706827767394634595 625646746060241651091951893)
              ·
                refine ⟨29327191221573827394935245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 625646746060241651091951893 29327191221573827394935245)
                ·
                  refine ⟨10997696708090185273100717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29327191221573827394935245 10997696708090185273100717)
                  ·
                    refine ⟨4124136265533819477412769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10997696708090185273100717 4124136265533819477412769)
                    ·
                      refine ⟨3093102199150364608059577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124136265533819477412769 3093102199150364608059577)
                      ·
                        rfl

theorem cell23_6023795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 3, 2].length) (baseStart_6023795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023795 prefixEnd_6023795 := by exact prefixLift 6023795
  have htrace : WordTrace (prefixWord ++ tailWord_6023795) baseStart_6023795 baseEnd_6023795 := by
    simpa [prefixWord, tailWord_6023795, baseEnd_6023795] using wordTrace_append hprefix tailTrace_6023795
  have hstable : (prefixWord ++ tailWord_6023795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023795).length < 2 ^ (prefixWord ++ tailWord_6023795).sum := by decide
  have hdescent : baseEnd_6023795 < baseStart_6023795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023859 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 2, 2, 2]
def baseStart_6023859 : Nat := 118140960795 + 6023859 * 2 ^ 59
def prefixEnd_6023859 : Nat := 4983230072969 + 3 ^ 40 * 6023859 * 2
def baseEnd_6023859 : Nat := 3093135061912252357659283

theorem tailTrace_6023859 : CollatzResearch.WordTrace tailWord_6023859 prefixEnd_6023859 3093135061912252357659283 := by
  unfold tailWord_6023859
  simp only [CollatzResearch.WordTrace]
  refine ⟨219708187483595111055898631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146472124989063407370599087 219708187483595111055898631)
  ·
    refine ⟨329562281225392666583847947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219708187483595111055898631 329562281225392666583847947)
    ·
      refine ⟨494343421838088999875771921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329562281225392666583847947 494343421838088999875771921)
      ·
        refine ⟨370757566378566749906828941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494343421838088999875771921 370757566378566749906828941)
        ·
          refine ⟨139034087391962531215060853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370757566378566749906828941 139034087391962531215060853)
          ·
            refine ⟨13034445692996487301411955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139034087391962531215060853 13034445692996487301411955)
            ·
              refine ⟨19551668539494730952117933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13034445692996487301411955 19551668539494730952117933)
              ·
                refine ⟨7331875702310524107044225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19551668539494730952117933 7331875702310524107044225)
                ·
                  refine ⟨5498906776732893080283169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7331875702310524107044225 5498906776732893080283169)
                  ·
                    refine ⟨4124180082549669810212377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5498906776732893080283169 4124180082549669810212377)
                    ·
                      refine ⟨3093135061912252357659283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124180082549669810212377 3093135061912252357659283)
                      ·
                        rfl

theorem cell23_6023859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 2, 2].length) (baseStart_6023859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023859 prefixEnd_6023859 := by exact prefixLift 6023859
  have htrace : WordTrace (prefixWord ++ tailWord_6023859) baseStart_6023859 baseEnd_6023859 := by
    simpa [prefixWord, tailWord_6023859, baseEnd_6023859] using wordTrace_append hprefix tailTrace_6023859
  have hstable : (prefixWord ++ tailWord_6023859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023859).length < 2 ^ (prefixWord ++ tailWord_6023859).sum := by decide
  have hdescent : baseEnd_6023859 < baseStart_6023859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023893 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6023893 : Nat := 118140960795 + 6023893 * 2 ^ 59
def prefixEnd_6023893 : Nat := 4983230072969 + 3 ^ 40 * 6023893 * 2
def baseEnd_6023893 : Nat := 3093152520254505224634127

theorem tailTrace_6023893 : CollatzResearch.WordTrace tailWord_6023893 prefixEnd_6023893 3093152520254505224634127 := by
  unfold tailWord_6023893
  simp only [CollatzResearch.WordTrace]
  refine ⟨219709427565471934862636333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146472951710314623241757555 219709427565471934862636333)
  ·
    refine ⟨82391035337051975573488625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219709427565471934862636333 82391035337051975573488625)
    ·
      refine ⟨61793276502788981680116469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82391035337051975573488625 61793276502788981680116469)
      ·
        refine ⟨5793119672136467032510919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61793276502788981680116469 5793119672136467032510919)
        ·
          refine ⟨8689679508204700548766379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793119672136467032510919 8689679508204700548766379)
          ·
            refine ⟨13034519262307050823149569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8689679508204700548766379 13034519262307050823149569)
            ·
              refine ⟨9775889446730288117362177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13034519262307050823149569 9775889446730288117362177)
              ·
                refine ⟨7331917085047716088021633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9775889446730288117362177 7331917085047716088021633)
                ·
                  refine ⟨5498937813785787066016225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7331917085047716088021633 5498937813785787066016225)
                  ·
                    refine ⟨4124203360339340299512169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5498937813785787066016225 4124203360339340299512169)
                    ·
                      refine ⟨3093152520254505224634127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124203360339340299512169 3093152520254505224634127)
                      ·
                        rfl

theorem cell23_6023893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6023893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023893 prefixEnd_6023893 := by exact prefixLift 6023893
  have htrace : WordTrace (prefixWord ++ tailWord_6023893) baseStart_6023893 baseEnd_6023893 := by
    simpa [prefixWord, tailWord_6023893, baseEnd_6023893] using wordTrace_append hprefix tailTrace_6023893
  have hstable : (prefixWord ++ tailWord_6023893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023893).length < 2 ^ (prefixWord ++ tailWord_6023893).sum := by decide
  have hdescent : baseEnd_6023893 < baseStart_6023893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023895 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 2, 5]
def baseStart_6023895 : Nat := 118140960795 + 6023895 * 2 ^ 59
def prefixEnd_6023895 : Nat := 4983230072969 + 3 ^ 40 * 6023895 * 2
def baseEnd_6023895 : Nat := 1031051182405271405603039

theorem tailTrace_6023895 : CollatzResearch.WordTrace tailWord_6023895 prefixEnd_6023895 1031051182405271405603039 := by
  unfold tailWord_6023895
  simp only [CollatzResearch.WordTrace]
  refine ⟨219709500511464689204209139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146473000340976459469472759 219709500511464689204209139)
  ·
    refine ⟨329564250767197033806313709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219709500511464689204209139 329564250767197033806313709)
    ·
      refine ⟨123586594037698887677367641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329564250767197033806313709 123586594037698887677367641)
      ·
        refine ⟨92689945528274165758025731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123586594037698887677367641 92689945528274165758025731)
        ·
          refine ⟨139034918292411248637038597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92689945528274165758025731 139034918292411248637038597)
          ·
            refine ⟨26069047179827109119444737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139034918292411248637038597 26069047179827109119444737)
            ·
              refine ⟨19551785384870331839583553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26069047179827109119444737 19551785384870331839583553)
              ·
                refine ⟨14663839038652748879687665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19551785384870331839583553 14663839038652748879687665)
                ·
                  refine ⟨10997879278989561659765749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14663839038652748879687665 10997879278989561659765749)
                  ·
                    refine ⟨1031051182405271405603039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10997879278989561659765749 1031051182405271405603039)
                    ·
                      rfl

theorem cell23_6023895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_6023895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023895 prefixEnd_6023895 := by exact prefixLift 6023895
  have htrace : WordTrace (prefixWord ++ tailWord_6023895) baseStart_6023895 baseEnd_6023895 := by
    simpa [prefixWord, tailWord_6023895, baseEnd_6023895] using wordTrace_append hprefix tailTrace_6023895
  have hstable : (prefixWord ++ tailWord_6023895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023895).length < 2 ^ (prefixWord ++ tailWord_6023895).sum := by decide
  have hdescent : baseEnd_6023895 < baseStart_6023895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023905 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_6023905 : Nat := 118140960795 + 6023905 * 2 ^ 59
def prefixEnd_6023905 : Nat := 4983230072969 + 3 ^ 40 * 6023905 * 2
def baseEnd_6023905 : Nat := 3093158682022359177684071

theorem tailTrace_6023905 : CollatzResearch.WordTrace tailWord_6023905 prefixEnd_6023905 3093158682022359177684071 := by
  unfold tailWord_6023905
  simp only [CollatzResearch.WordTrace]
  refine ⟨219709865241428460912073169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146473243494285640608048779 219709865241428460912073169)
  ·
    refine ⟨164782398931071345684054877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219709865241428460912073169 164782398931071345684054877)
    ·
      refine ⟨61793399599151754631520579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164782398931071345684054877 61793399599151754631520579)
      ·
        refine ⟨92690099398727631947280869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61793399599151754631520579 92690099398727631947280869)
        ·
          refine ⟨17379393637261430990115163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92690099398727631947280869 17379393637261430990115163)
          ·
            refine ⟨26069090455892146485172745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17379393637261430990115163 26069090455892146485172745)
            ·
              refine ⟨19551817841919109863879559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26069090455892146485172745 19551817841919109863879559)
              ·
                refine ⟨29327726762878664795819339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19551817841919109863879559 29327726762878664795819339)
                ·
                  refine ⟨43991590144317997193729009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29327726762878664795819339 43991590144317997193729009)
                  ·
                    refine ⟨32993692608238497895296757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43991590144317997193729009 32993692608238497895296757)
                    ·
                      refine ⟨3093158682022359177684071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32993692608238497895296757 3093158682022359177684071)
                      ·
                        rfl

theorem cell23_6023905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_6023905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023905 prefixEnd_6023905 := by exact prefixLift 6023905
  have htrace : WordTrace (prefixWord ++ tailWord_6023905) baseStart_6023905 baseEnd_6023905 := by
    simpa [prefixWord, tailWord_6023905, baseEnd_6023905] using wordTrace_append hprefix tailTrace_6023905
  have hstable : (prefixWord ++ tailWord_6023905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023905).length < 2 ^ (prefixWord ++ tailWord_6023905).sum := by decide
  have hdescent : baseEnd_6023905 < baseStart_6023905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023932 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_6023932 : Nat := 118140960795 + 6023932 * 2 ^ 59
def prefixEnd_6023932 : Nat := 4983230072969 + 3 ^ 40 * 6023932 * 2
def baseEnd_6023932 : Nat := 3093172546000030572046447

theorem tailTrace_6023932 : CollatzResearch.WordTrace tailWord_6023932 prefixEnd_6023932 3093172546000030572046447 := by
  unfold tailWord_6023932
  simp only [CollatzResearch.WordTrace]
  refine ⟨109855425006165322261653025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146473900008220429682204033 109855425006165322261653025)
  ·
    refine ⟨82391568754623991696239769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109855425006165322261653025 82391568754623991696239769)
    ·
      refine ⟨61793676565967993772179827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82391568754623991696239769 61793676565967993772179827)
      ·
        refine ⟨92690514848951990658269741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61793676565967993772179827 92690514848951990658269741)
        ·
          refine ⟨34758943068356996496851153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92690514848951990658269741 34758943068356996496851153)
          ·
            refine ⟨26069207301267747372638365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34758943068356996496851153 26069207301267747372638365)
            ·
              refine ⟨9775952737975405264739387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26069207301267747372638365 9775952737975405264739387)
              ·
                refine ⟨14663929106963107897109081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9775952737975405264739387 14663929106963107897109081)
                ·
                  refine ⟨10997946830222330922831811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14663929106963107897109081 10997946830222330922831811)
                  ·
                    refine ⟨16496920245333496384247717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10997946830222330922831811 16496920245333496384247717)
                    ·
                      refine ⟨3093172546000030572046447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16496920245333496384247717 3093172546000030572046447)
                      ·
                        rfl

theorem cell23_6023932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_6023932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023932 prefixEnd_6023932 := by exact prefixLift 6023932
  have htrace : WordTrace (prefixWord ++ tailWord_6023932) baseStart_6023932 baseEnd_6023932 := by
    simpa [prefixWord, tailWord_6023932, baseEnd_6023932] using wordTrace_append hprefix tailTrace_6023932
  have hstable : (prefixWord ++ tailWord_6023932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023932).length < 2 ^ (prefixWord ++ tailWord_6023932).sum := by decide
  have hdescent : baseEnd_6023932 < baseStart_6023932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023959 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 3, 4]
def baseStart_6023959 : Nat := 118140960795 + 6023959 * 2 ^ 59
def prefixEnd_6023959 : Nat := 4983230072969 + 3 ^ 40 * 6023959 * 2
def baseEnd_6023959 : Nat := 1031062136659233988802941

theorem tailTrace_6023959 : CollatzResearch.WordTrace tailWord_6023959 prefixEnd_6023959 1031062136659233988802941 := by
  unfold tailWord_6023959
  simp only [CollatzResearch.WordTrace]
  refine ⟨219711834783232828134538931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146474556522155218756359287 219711834783232828134538931)
  ·
    refine ⟨329567752174849242201808397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219711834783232828134538931 329567752174849242201808397)
    ·
      refine ⟨123587907065568465825678149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329567752174849242201808397 123587907065568465825678149)
      ·
        refine ⟨23172732574794087342314653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123587907065568465825678149 23172732574794087342314653)
        ·
          refine ⟨8689774715547782753367995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23172732574794087342314653 8689774715547782753367995)
          ·
            refine ⟨13034662073321674130051993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8689774715547782753367995 13034662073321674130051993)
            ·
              refine ⟨9775996554991255597538995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13034662073321674130051993 9775996554991255597538995)
              ·
                refine ⟨14663994832486883396308493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9775996554991255597538995 14663994832486883396308493)
                ·
                  refine ⟨5498998062182581273615685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14663994832486883396308493 5498998062182581273615685)
                  ·
                    refine ⟨1031062136659233988802941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5498998062182581273615685 1031062136659233988802941)
                    ·
                      rfl

theorem cell23_6023959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_6023959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023959 prefixEnd_6023959 := by exact prefixLift 6023959
  have htrace : WordTrace (prefixWord ++ tailWord_6023959) baseStart_6023959 baseEnd_6023959 := by
    simpa [prefixWord, tailWord_6023959, baseEnd_6023959] using wordTrace_append hprefix tailTrace_6023959
  have hstable : (prefixWord ++ tailWord_6023959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023959).length < 2 ^ (prefixWord ++ tailWord_6023959).sum := by decide
  have hdescent : baseEnd_6023959 < baseStart_6023959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6023992 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 1, 5, 2]
def baseStart_6023992 : Nat := 118140960795 + 6023992 * 2 ^ 59
def prefixEnd_6023992 : Nat := 4983230072969 + 3 ^ 40 * 6023992 * 2
def baseEnd_6023992 : Nat := 3093203354839300337296171

theorem tailTrace_6023992 : CollatzResearch.WordTrace tailWord_6023992 prefixEnd_6023992 3093203354839300337296171 := by
  unfold tailWord_6023992
  simp only [CollatzResearch.WordTrace]
  refine ⟨109856519196056637385245115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146475358928075516513660153 109856519196056637385245115)
  ·
    refine ⟨164784778794084956077867673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109856519196056637385245115 164784778794084956077867673)
    ·
      refine ⟨123588584095563717058400755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164784778794084956077867673 123588584095563717058400755)
      ·
        refine ⟨185382876143345575587601133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123588584095563717058400755 185382876143345575587601133)
        ·
          refine ⟨69518578553754590845350425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185382876143345575587601133 69518578553754590845350425)
          ·
            refine ⟨52138933915315943134012819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69518578553754590845350425 52138933915315943134012819)
            ·
              refine ⟨78208400872973914701019229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52138933915315943134012819 78208400872973914701019229)
              ·
                refine ⟨29328150327365218012882211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78208400872973914701019229 29328150327365218012882211)
                ·
                  refine ⟨43992225491047827019323317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29328150327365218012882211 43992225491047827019323317)
                  ·
                    refine ⟨4124271139785733783061561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43992225491047827019323317 4124271139785733783061561)
                    ·
                      refine ⟨3093203354839300337296171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124271139785733783061561 3093203354839300337296171)
                      ·
                        rfl

theorem cell23_6023992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_6023992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6023992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6023992 prefixEnd_6023992 := by exact prefixLift 6023992
  have htrace : WordTrace (prefixWord ++ tailWord_6023992) baseStart_6023992 baseEnd_6023992 := by
    simpa [prefixWord, tailWord_6023992, baseEnd_6023992] using wordTrace_append hprefix tailTrace_6023992
  have hstable : (prefixWord ++ tailWord_6023992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6023992).length < 2 ^ (prefixWord ++ tailWord_6023992).sum := by decide
  have hdescent : baseEnd_6023992 < baseStart_6023992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6023992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024009 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 2, 3, 2]
def baseStart_6024009 : Nat := 118140960795 + 6024009 * 2 ^ 59
def prefixEnd_6024009 : Nat := 4983230072969 + 3 ^ 40 * 6024009 * 2
def baseEnd_6024009 : Nat := 3093212084010426770783593

theorem tailTrace_6024009 : CollatzResearch.WordTrace tailWord_6024009 prefixEnd_6024009 3093212084010426770783593 := by
  unfold tailWord_6024009
  simp only [CollatzResearch.WordTrace]
  refine ⟨219713658433051686673859081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146475772288701124449239387 219713658433051686673859081)
  ·
    refine ⟨164785243824788765005394311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219713658433051686673859081 164785243824788765005394311)
    ·
      refine ⟨247177865737183147508091467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164785243824788765005394311 247177865737183147508091467)
      ·
        refine ⟨370766798605774721262137201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247177865737183147508091467 370766798605774721262137201)
        ·
          refine ⟨278075098954331040946602901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370766798605774721262137201 278075098954331040946602901)
          ·
            refine ⟨13034770263484267544372011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 278075098954331040946602901 13034770263484267544372011)
            ·
              refine ⟨19552155395226401316558017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13034770263484267544372011 19552155395226401316558017)
              ·
                refine ⟨14664116546419800987418513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19552155395226401316558017 14664116546419800987418513)
                ·
                  refine ⟨10998087409814850740563885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14664116546419800987418513 10998087409814850740563885)
                  ·
                    refine ⟨4124282778680569027711457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10998087409814850740563885 4124282778680569027711457)
                    ·
                      refine ⟨3093212084010426770783593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124282778680569027711457 3093212084010426770783593)
                      ·
                        rfl

theorem cell23_6024009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 3, 2].length) (baseStart_6024009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024009 prefixEnd_6024009 := by exact prefixLift 6024009
  have htrace : WordTrace (prefixWord ++ tailWord_6024009) baseStart_6024009 baseEnd_6024009 := by
    simpa [prefixWord, tailWord_6024009, baseEnd_6024009] using wordTrace_append hprefix tailTrace_6024009
  have hstable : (prefixWord ++ tailWord_6024009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024009).length < 2 ^ (prefixWord ++ tailWord_6024009).sum := by decide
  have hdescent : baseEnd_6024009 < baseStart_6024009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024039 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_6024039 : Nat := 118140960795 + 6024039 * 2 ^ 59
def prefixEnd_6024039 : Nat := 4983230072969 + 3 ^ 40 * 6024039 * 2
def baseEnd_6024039 : Nat := 3093227488430061653408455

theorem tailTrace_6024039 : CollatzResearch.WordTrace tailWord_6024039 prefixEnd_6024039 3093227488430061653408455 := by
  unfold tailWord_6024039
  simp only [CollatzResearch.WordTrace]
  refine ⟨219714752622943001797451171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146476501748628667864967447 219714752622943001797451171)
  ·
    refine ⟨329572128934414502696176757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219714752622943001797451171 329572128934414502696176757)
    ·
      refine ⟨30897387087601359627766571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 329572128934414502696176757 30897387087601359627766571)
      ·
        refine ⟨46346080631402039441649857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30897387087601359627766571 46346080631402039441649857)
        ·
          refine ⟨34759560473551529581237393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46346080631402039441649857 34759560473551529581237393)
          ·
            refine ⟨26069670355163647185928045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34759560473551529581237393 26069670355163647185928045)
            ·
              refine ⟨9776126383186367694723017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26069670355163647185928045 9776126383186367694723017)
              ·
                refine ⟨7332094787389775771042263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9776126383186367694723017 7332094787389775771042263)
                ·
                  refine ⟨10998142181084663656563395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7332094787389775771042263 10998142181084663656563395)
                  ·
                    refine ⟨16497213271626995484845093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10998142181084663656563395 16497213271626995484845093)
                    ·
                      refine ⟨3093227488430061653408455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16497213271626995484845093 3093227488430061653408455)
                      ·
                        rfl

theorem cell23_6024039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_6024039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024039 prefixEnd_6024039 := by exact prefixLift 6024039
  have htrace : WordTrace (prefixWord ++ tailWord_6024039) baseStart_6024039 baseEnd_6024039 := by
    simpa [prefixWord, tailWord_6024039, baseEnd_6024039] using wordTrace_append hprefix tailTrace_6024039
  have hstable : (prefixWord ++ tailWord_6024039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024039).length < 2 ^ (prefixWord ++ tailWord_6024039).sum := by decide
  have hdescent : baseEnd_6024039 < baseStart_6024039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024062 : List Nat := [4, 2, 3, 1, 13]
def baseStart_6024062 : Nat := 118140960795 + 6024062 * 2 ^ 59
def prefixEnd_6024062 : Nat := 4983230072969 + 3 ^ 40 * 6024062 * 2
def baseEnd_6024062 : Nat := 4243126609718950704281

theorem tailTrace_6024062 : CollatzResearch.WordTrace tailWord_6024062 prefixEnd_6024062 4243126609718950704281 := by
  unfold tailWord_6024062
  simp only [CollatzResearch.WordTrace]
  refine ⟨27464448937732459590692305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146477061001239784483692293 27464448937732459590692305)
  ·
    refine ⟨20598336703299344693019229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27464448937732459590692305 20598336703299344693019229)
    ·
      refine ⟨7724376263737254259882211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20598336703299344693019229 7724376263737254259882211)
      ·
        refine ⟨11586564395605881389823317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7724376263737254259882211 11586564395605881389823317)
        ·
          refine ⟨4243126609718950704281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11586564395605881389823317 4243126609718950704281)
          ·
            rfl

theorem cell23_6024062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 13].length) (baseStart_6024062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024062 prefixEnd_6024062 := by exact prefixLift 6024062
  have htrace : WordTrace (prefixWord ++ tailWord_6024062) baseStart_6024062 baseEnd_6024062 := by
    simpa [prefixWord, tailWord_6024062, baseEnd_6024062] using wordTrace_append hprefix tailTrace_6024062
  have hstable : (prefixWord ++ tailWord_6024062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024062).length < 2 ^ (prefixWord ++ tailWord_6024062).sum := by decide
  have hdescent : baseEnd_6024062 < baseStart_6024062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024073 : List Nat := [1, 2, 1, 1, 5, 3, 1, 4, 1, 2, 2]
def baseStart_6024073 : Nat := 118140960795 + 6024073 * 2 ^ 59
def prefixEnd_6024073 : Nat := 4983230072969 + 3 ^ 40 * 6024073 * 2
def baseEnd_6024073 : Nat := 3093244946772314520383299

theorem tailTrace_6024073 : CollatzResearch.WordTrace tailWord_6024073 prefixEnd_6024073 3093244946772314520383299 := by
  unfold tailWord_6024073
  simp only [CollatzResearch.WordTrace]
  refine ⟨219715992704819825604188873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146477328469879883736125915 219715992704819825604188873)
  ·
    refine ⟨164786994528614869203141655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219715992704819825604188873 164786994528614869203141655)
    ·
      refine ⟨247180491792922303804712483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164786994528614869203141655 247180491792922303804712483)
      ·
        refine ⟨370770737689383455707068725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247180491792922303804712483 370770737689383455707068725)
        ·
          refine ⟨34759756658379698972537693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 370770737689383455707068725 34759756658379698972537693)
          ·
            refine ⟨13034908746892387114701635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34759756658379698972537693 13034908746892387114701635)
            ·
              refine ⟨19552363120338580672052453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13034908746892387114701635 19552363120338580672052453)
              ·
                refine ⟨3666068085063483876009835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19552363120338580672052453 3666068085063483876009835)
                ·
                  refine ⟨5499102127595225814014753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666068085063483876009835 5499102127595225814014753)
                  ·
                    refine ⟨4124326595696419360511065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5499102127595225814014753 4124326595696419360511065)
                    ·
                      refine ⟨3093244946772314520383299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124326595696419360511065 3093244946772314520383299)
                      ·
                        rfl

theorem cell23_6024073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 1, 2, 2].length) (baseStart_6024073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024073 prefixEnd_6024073 := by exact prefixLift 6024073
  have htrace : WordTrace (prefixWord ++ tailWord_6024073) baseStart_6024073 baseEnd_6024073 := by
    simpa [prefixWord, tailWord_6024073, baseEnd_6024073] using wordTrace_append hprefix tailTrace_6024073
  have hstable : (prefixWord ++ tailWord_6024073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024073).length < 2 ^ (prefixWord ++ tailWord_6024073).sum := by decide
  have hdescent : baseEnd_6024073 < baseStart_6024073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024075 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 2, 7]
def baseStart_6024075 : Nat := 118140960795 + 6024075 * 2 ^ 59
def prefixEnd_6024075 : Nat := 4983230072969 + 3 ^ 40 * 6024075 * 2
def baseEnd_6024075 : Nat := 1031081991244541170852763

theorem tailTrace_6024075 : CollatzResearch.WordTrace tailWord_6024075 prefixEnd_6024075 1031081991244541170852763 := by
  unfold tailWord_6024075
  simp only [CollatzResearch.WordTrace]
  refine ⟨219716065650812579945761679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146477377100541719963841119 219716065650812579945761679)
  ·
    refine ⟨329574098476218869918642519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219716065650812579945761679 329574098476218869918642519)
    ·
      refine ⟨494361147714328304877963779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329574098476218869918642519 494361147714328304877963779)
      ·
        refine ⟨741541721571492457316945669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494361147714328304877963779 741541721571492457316945669)
        ·
          refine ⟨139039072794654835746927313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 741541721571492457316945669 139039072794654835746927313)
          ·
            refine ⟨104279304595991126810195485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139039072794654835746927313 104279304595991126810195485)
            ·
              refine ⟨39104739223496672553823307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104279304595991126810195485 39104739223496672553823307)
              ·
                refine ⟨58657108835245008830734961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39104739223496672553823307 58657108835245008830734961)
                ·
                  refine ⟨43992831626433756623051221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58657108835245008830734961 43992831626433756623051221)
                  ·
                    refine ⟨1031081991244541170852763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43992831626433756623051221 1031081991244541170852763)
                    ·
                      rfl

theorem cell23_6024075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 7].length) (baseStart_6024075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024075 prefixEnd_6024075 := by exact prefixLift 6024075
  have htrace : WordTrace (prefixWord ++ tailWord_6024075) baseStart_6024075 baseEnd_6024075 := by
    simpa [prefixWord, tailWord_6024075, baseEnd_6024075] using wordTrace_append hprefix tailTrace_6024075
  have hstable : (prefixWord ++ tailWord_6024075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024075).length < 2 ^ (prefixWord ++ tailWord_6024075).sum := by decide
  have hdescent : baseEnd_6024075 < baseStart_6024075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024099 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 3, 3, 2]
def baseStart_6024099 : Nat := 118140960795 + 6024099 * 2 ^ 59
def prefixEnd_6024099 : Nat := 4983230072969 + 3 ^ 40 * 6024099 * 2
def baseEnd_6024099 : Nat := 3093258297269331418658179

theorem tailTrace_6024099 : CollatzResearch.WordTrace tailWord_6024099 prefixEnd_6024099 3093258297269331418658179 := by
  unfold tailWord_6024099
  simp only [CollatzResearch.WordTrace]
  refine ⟨219716941002725632044635351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146477960668483754696423567 219716941002725632044635351)
  ·
    refine ⟨329575411504088448066953027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219716941002725632044635351 329575411504088448066953027)
    ·
      refine ⟨494363117256132672100429541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329575411504088448066953027 494363117256132672100429541)
      ·
        refine ⟨92693084485524876018830539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 494363117256132672100429541 92693084485524876018830539)
        ·
          refine ⟨139039626728287314028245809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92693084485524876018830539 139039626728287314028245809)
          ·
            refine ⟨104279720046215485521184357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139039626728287314028245809 104279720046215485521184357)
            ·
              refine ⟨19552447508665403535222067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104279720046215485521184357 19552447508665403535222067)
              ·
                refine ⟨29328671262998105302833101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19552447508665403535222067 29328671262998105302833101)
                ·
                  refine ⟨10998251723624289488562413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29328671262998105302833101 10998251723624289488562413)
                  ·
                    refine ⟨4124344396359108558210905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10998251723624289488562413 4124344396359108558210905)
                    ·
                      refine ⟨3093258297269331418658179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124344396359108558210905 3093258297269331418658179)
                      ·
                        rfl

theorem cell23_6024099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_6024099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024099 prefixEnd_6024099 := by exact prefixLift 6024099
  have htrace : WordTrace (prefixWord ++ tailWord_6024099) baseStart_6024099 baseEnd_6024099 := by
    simpa [prefixWord, tailWord_6024099, baseEnd_6024099] using wordTrace_append hprefix tailTrace_6024099
  have hstable : (prefixWord ++ tailWord_6024099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024099).length < 2 ^ (prefixWord ++ tailWord_6024099).sum := by decide
  have hdescent : baseEnd_6024099 < baseStart_6024099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024105 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 1, 8]
def baseStart_6024105 : Nat := 118140960795 + 6024105 * 2 ^ 59
def prefixEnd_6024105 : Nat := 4983230072969 + 3 ^ 40 * 6024105 * 2
def baseEnd_6024105 : Nat := 1031087126051086131727717

theorem tailTrace_6024105 : CollatzResearch.WordTrace tailWord_6024105 prefixEnd_6024105 1031087126051086131727717 := by
  unfold tailWord_6024105
  simp only [CollatzResearch.WordTrace]
  refine ⟨219717159840703895069353769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146478106560469263379569179 219717159840703895069353769)
  ·
    refine ⟨164787869880527921302015327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219717159840703895069353769 164787869880527921302015327)
    ·
      refine ⟨247181804820791881953022991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164787869880527921302015327 247181804820791881953022991)
      ·
        refine ⟨370772707231187822929534487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247181804820791881953022991 370772707231187822929534487)
        ·
          refine ⟨556159060846781734394301731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370772707231187822929534487 556159060846781734394301731)
          ·
            refine ⟨834238591270172601591452597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556159060846781734394301731 834238591270172601591452597)
            ·
              refine ⟨78209867931578681399198681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 834238591270172601591452597 78209867931578681399198681)
              ·
                refine ⟨58657400948684011049399011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78209867931578681399198681 58657400948684011049399011)
                ·
                  refine ⟨87986101423026016574098517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58657400948684011049399011 87986101423026016574098517)
                  ·
                    refine ⟨1031087126051086131727717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87986101423026016574098517 1031087126051086131727717)
                    ·
                      rfl

theorem cell23_6024105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_6024105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024105 prefixEnd_6024105 := by exact prefixLift 6024105
  have htrace : WordTrace (prefixWord ++ tailWord_6024105) baseStart_6024105 baseEnd_6024105 := by
    simpa [prefixWord, tailWord_6024105, baseEnd_6024105] using wordTrace_append hprefix tailTrace_6024105
  have hstable : (prefixWord ++ tailWord_6024105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024105).length < 2 ^ (prefixWord ++ tailWord_6024105).sum := by decide
  have hdescent : baseEnd_6024105 < baseStart_6024105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024134 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6024134 : Nat := 118140960795 + 6024134 * 2 ^ 59
def prefixEnd_6024134 : Nat := 4983230072969 + 3 ^ 40 * 6024134 * 2
def baseEnd_6024134 : Nat := 1031092089697412927240173

theorem tailTrace_6024134 : CollatzResearch.WordTrace tailWord_6024134 prefixEnd_6024134 1031092089697412927240173 := by
  unfold tailWord_6024134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6866194298674963531942483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146478811705065888681439637 6866194298674963531942483)
  ·
    refine ⟨10299291448012445297913725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6866194298674963531942483 10299291448012445297913725)
    ·
      refine ⟨3862234293004666986717647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10299291448012445297913725 3862234293004666986717647)
      ·
        refine ⟨5793351439507000480076471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3862234293004666986717647 5793351439507000480076471)
        ·
          refine ⟨8690027159260500720114707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793351439507000480076471 8690027159260500720114707)
          ·
            refine ⟨13035040738890751080172061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8690027159260500720114707 13035040738890751080172061)
            ·
              refine ⟨4888140277084031655064523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13035040738890751080172061 4888140277084031655064523)
              ·
                refine ⟨7332210415626047482596785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888140277084031655064523 7332210415626047482596785)
                ·
                  refine ⟨5499157811719535611947589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7332210415626047482596785 5499157811719535611947589)
                  ·
                    refine ⟨1031092089697412927240173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5499157811719535611947589 1031092089697412927240173)
                    ·
                      rfl

theorem cell23_6024134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6024134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024134 prefixEnd_6024134 := by exact prefixLift 6024134
  have htrace : WordTrace (prefixWord ++ tailWord_6024134) baseStart_6024134 baseEnd_6024134 := by
    simpa [prefixWord, tailWord_6024134, baseEnd_6024134] using wordTrace_append hprefix tailTrace_6024134
  have hstable : (prefixWord ++ tailWord_6024134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024134).length < 2 ^ (prefixWord ++ tailWord_6024134).sum := by decide
  have hdescent : baseEnd_6024134 < baseStart_6024134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024150 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_6024150 : Nat := 118140960795 + 6024150 * 2 ^ 59
def prefixEnd_6024150 : Nat := 4983230072969 + 3 ^ 40 * 6024150 * 2
def baseEnd_6024150 : Nat := 3093284484782710719120445

theorem tailTrace_6024150 : CollatzResearch.WordTrace tailWord_6024150 prefixEnd_6024150 3093284484782710719120445 := by
  unfold tailWord_6024150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732425070346304234671369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146479200750360578503161269 13732425070346304234671369)
  ·
    refine ⟨10299318802759728176003527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13732425070346304234671369 10299318802759728176003527)
    ·
      refine ⟨15448978204139592264005291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10299318802759728176003527 15448978204139592264005291)
      ·
        refine ⟨23173467306209388396007937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15448978204139592264005291 23173467306209388396007937)
        ·
          refine ⟨17380100479657041297005953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23173467306209388396007937 17380100479657041297005953)
          ·
            refine ⟨13035075359742780972754465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17380100479657041297005953 13035075359742780972754465)
            ·
              refine ⟨9776306519807085729565849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13035075359742780972754465 9776306519807085729565849)
              ·
                refine ⟨7332229889855314297174387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9776306519807085729565849 7332229889855314297174387)
                ·
                  refine ⟨10998344834782971445761581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7332229889855314297174387 10998344834782971445761581)
                  ·
                    refine ⟨4124379313043614292160593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10998344834782971445761581 4124379313043614292160593)
                    ·
                      refine ⟨3093284484782710719120445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124379313043614292160593 3093284484782710719120445)
                      ·
                        rfl

theorem cell23_6024150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_6024150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024150 prefixEnd_6024150 := by exact prefixLift 6024150
  have htrace : WordTrace (prefixWord ++ tailWord_6024150) baseStart_6024150 baseEnd_6024150 := by
    simpa [prefixWord, tailWord_6024150, baseEnd_6024150] using wordTrace_append hprefix tailTrace_6024150
  have hstable : (prefixWord ++ tailWord_6024150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024150).length < 2 ^ (prefixWord ++ tailWord_6024150).sum := by decide
  have hdescent : baseEnd_6024150 < baseStart_6024150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024152 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 7]
def baseStart_6024152 : Nat := 118140960795 + 6024152 * 2 ^ 59
def prefixEnd_6024152 : Nat := 4983230072969 + 3 ^ 40 * 6024152 * 2
def baseEnd_6024152 : Nat := 343698390193779967921715

theorem tailTrace_6024152 : CollatzResearch.WordTrace tailWord_6024152 prefixEnd_6024152 343698390193779967921715 := by
  unfold tailWord_6024152
  simp only [CollatzResearch.WordTrace]
  refine ⟨109859437035766811048157355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146479249381022414730876473 109859437035766811048157355)
  ·
    refine ⟨164789155553650216572236033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109859437035766811048157355 164789155553650216572236033)
    ·
      refine ⟨123591866665237662429177025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164789155553650216572236033 123591866665237662429177025)
      ·
        refine ⟨92693899998928246821882769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123591866665237662429177025 92693899998928246821882769)
        ·
          refine ⟨69520424999196185116412077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92693899998928246821882769 69520424999196185116412077)
          ·
            refine ⟨26070159374698569418654529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69520424999196185116412077 26070159374698569418654529)
            ·
              refine ⟨19552619531023927063990897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26070159374698569418654529 19552619531023927063990897)
              ·
                refine ⟨14664464648267945297993173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19552619531023927063990897 14664464648267945297993173)
                ·
                  refine ⟨343698390193779967921715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14664464648267945297993173 343698390193779967921715)
                  ·
                    rfl

theorem cell23_6024152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 7].length) (baseStart_6024152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024152 prefixEnd_6024152 := by exact prefixLift 6024152
  have htrace : WordTrace (prefixWord ++ tailWord_6024152) baseStart_6024152 baseEnd_6024152 := by
    simpa [prefixWord, tailWord_6024152, baseEnd_6024152] using wordTrace_append hprefix tailTrace_6024152
  have hstable : (prefixWord ++ tailWord_6024152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024152).length < 2 ^ (prefixWord ++ tailWord_6024152).sum := by decide
  have hdescent : baseEnd_6024152 < baseStart_6024152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024189 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 2, 5, 2]
def baseStart_6024189 : Nat := 118140960795 + 6024189 * 2 ^ 59
def prefixEnd_6024189 : Nat := 4983230072969 + 3 ^ 40 * 6024189 * 2
def baseEnd_6024189 : Nat := 3093304510528236066532765

theorem tailTrace_6024189 : CollatzResearch.WordTrace tailWord_6024189 prefixEnd_6024189 3093304510528236066532765 := by
  unfold tailWord_6024189
  simp only [CollatzResearch.WordTrace]
  refine ⟨219720223572399577415411621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146480149048266384943607747 219720223572399577415411621)
  ·
    refine ⟨41197541919824920765389679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219720223572399577415411621 41197541919824920765389679)
    ·
      refine ⟨61796312879737381148084519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41197541919824920765389679 61796312879737381148084519)
      ·
        refine ⟨92694469319606071722126779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61796312879737381148084519 92694469319606071722126779)
        ·
          refine ⟨139041703979409107583190169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92694469319606071722126779 139041703979409107583190169)
          ·
            refine ⟨104281277984556830687392627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139041703979409107583190169 104281277984556830687392627)
            ·
              refine ⟨156421916976835246031088941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104281277984556830687392627 156421916976835246031088941)
              ·
                refine ⟨58658218866313217261658353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156421916976835246031088941 58658218866313217261658353)
                ·
                  refine ⟨43993664149734912946243765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58658218866313217261658353 43993664149734912946243765)
                  ·
                    refine ⟨4124406014037648088710353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43993664149734912946243765 4124406014037648088710353)
                    ·
                      refine ⟨3093304510528236066532765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124406014037648088710353 3093304510528236066532765)
                      ·
                        rfl

theorem cell23_6024189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_6024189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024189 prefixEnd_6024189 := by exact prefixLift 6024189
  have htrace : WordTrace (prefixWord ++ tailWord_6024189) baseStart_6024189 baseEnd_6024189 := by
    simpa [prefixWord, tailWord_6024189, baseEnd_6024189] using wordTrace_append hprefix tailTrace_6024189
  have hstable : (prefixWord ++ tailWord_6024189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024189).length < 2 ^ (prefixWord ++ tailWord_6024189).sum := by decide
  have hdescent : baseEnd_6024189 < baseStart_6024189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024303 : List Nat := [1, 1, 2, 1, 3, 3, 1, 6, 1, 1, 3]
def baseStart_6024303 : Nat := 118140960795 + 6024303 * 2 ^ 59
def prefixEnd_6024303 : Nat := 4983230072969 + 3 ^ 40 * 6024303 * 2
def baseEnd_6024303 : Nat := 3093363047322848620507241

theorem tailTrace_6024303 : CollatzResearch.WordTrace tailWord_6024303 prefixEnd_6024303 3093363047322848620507241 := by
  unfold tailWord_6024303
  simp only [CollatzResearch.WordTrace]
  refine ⟨219724381493986574885061563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146482920995991049923374375 219724381493986574885061563)
  ·
    refine ⟨329586572240979862327592345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219724381493986574885061563 329586572240979862327592345)
    ·
      refine ⟨247189929180734896745694259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329586572240979862327592345 247189929180734896745694259)
      ·
        refine ⟨370784893771102345118541389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247189929180734896745694259 370784893771102345118541389)
        ·
          refine ⟨139044335164163379419453021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370784893771102345118541389 139044335164163379419453021)
          ·
            refine ⟨52141625686561267282294883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139044335164163379419453021 52141625686561267282294883)
            ·
              refine ⟨78212438529841900923442325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52141625686561267282294883 78212438529841900923442325)
              ·
                refine ⟨3666208056086339105786359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78212438529841900923442325 3666208056086339105786359)
                ·
                  refine ⟨5499312084129508658679539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666208056086339105786359 5499312084129508658679539)
                  ·
                    refine ⟨8248968126194262988019309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5499312084129508658679539 8248968126194262988019309)
                    ·
                      refine ⟨3093363047322848620507241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8248968126194262988019309 3093363047322848620507241)
                      ·
                        rfl

theorem cell23_6024303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 1, 1, 3].length) (baseStart_6024303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024303 prefixEnd_6024303 := by exact prefixLift 6024303
  have htrace : WordTrace (prefixWord ++ tailWord_6024303) baseStart_6024303 baseEnd_6024303 := by
    simpa [prefixWord, tailWord_6024303, baseEnd_6024303] using wordTrace_append hprefix tailTrace_6024303
  have hstable : (prefixWord ++ tailWord_6024303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024303).length < 2 ^ (prefixWord ++ tailWord_6024303).sum := by decide
  have hdescent : baseEnd_6024303 < baseStart_6024303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024339 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 4]
def baseStart_6024339 : Nat := 118140960795 + 6024339 * 2 ^ 59
def prefixEnd_6024339 : Nat := 4983230072969 + 3 ^ 40 * 6024339 * 2
def baseEnd_6024339 : Nat := 3093381532626410479657075

theorem tailTrace_6024339 : CollatzResearch.WordTrace tailWord_6024339 prefixEnd_6024339 3093381532626410479657075 := by
  unfold tailWord_6024339
  simp only [CollatzResearch.WordTrace]
  refine ⟨219725694521856153033372071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146483796347904102022248047 219725694521856153033372071)
  ·
    refine ⟨329588541782784229550058107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219725694521856153033372071 329588541782784229550058107)
    ·
      refine ⟨494382812674176344325087161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329588541782784229550058107 494382812674176344325087161)
      ·
        refine ⟨370787109505632258243815371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494382812674176344325087161 370787109505632258243815371)
        ·
          refine ⟨556180664258448387365723057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370787109505632258243815371 556180664258448387365723057)
          ·
            refine ⟨417135498193836290524292293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556180664258448387365723057 417135498193836290524292293)
            ·
              refine ⟨78212905911344304473304805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 417135498193836290524292293 78212905911344304473304805)
              ·
                refine ⟨14664919858377057088744651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78212905911344304473304805 14664919858377057088744651)
                ·
                  refine ⟨21997379787565585633116977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14664919858377057088744651 21997379787565585633116977)
                  ·
                    refine ⟨16498034840674189224837733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21997379787565585633116977 16498034840674189224837733)
                    ·
                      refine ⟨3093381532626410479657075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16498034840674189224837733 3093381532626410479657075)
                      ·
                        rfl

theorem cell23_6024339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_6024339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024339 prefixEnd_6024339 := by exact prefixLift 6024339
  have htrace : WordTrace (prefixWord ++ tailWord_6024339) baseStart_6024339 baseEnd_6024339 := by
    simpa [prefixWord, tailWord_6024339, baseEnd_6024339] using wordTrace_append hprefix tailTrace_6024339
  have hstable : (prefixWord ++ tailWord_6024339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024339).length < 2 ^ (prefixWord ++ tailWord_6024339).sum := by decide
  have hdescent : baseEnd_6024339 < baseStart_6024339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024346 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6024346 : Nat := 118140960795 + 6024346 * 2 ^ 59
def prefixEnd_6024346 : Nat := 4983230072969 + 3 ^ 40 * 6024346 * 2
def baseEnd_6024346 : Nat := 3093385126990991952269543

theorem tailTrace_6024346 : CollatzResearch.WordTrace tailWord_6024346 prefixEnd_6024346 3093385126990991952269543 := by
  unfold tailWord_6024346
  simp only [CollatzResearch.WordTrace]
  refine ⟨54931487458207698307219223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146483966555220528819251261 54931487458207698307219223)
  ·
    refine ⟨82397231187311547460828835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54931487458207698307219223 82397231187311547460828835)
    ·
      refine ⟨123595846780967321191243253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82397231187311547460828835 123595846780967321191243253)
      ·
        refine ⟨11587110635715686361679055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123595846780967321191243253 11587110635715686361679055)
        ·
          refine ⟨17380665953573529542518583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11587110635715686361679055 17380665953573529542518583)
          ·
            refine ⟨26070998930360294313777875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17380665953573529542518583 26070998930360294313777875)
            ·
              refine ⟨39106498395540441470666813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26070998930360294313777875 39106498395540441470666813)
              ·
                refine ⟨14664936898327665551500055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39106498395540441470666813 14664936898327665551500055)
                ·
                  refine ⟨21997405347491498327250083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14664936898327665551500055 21997405347491498327250083)
                  ·
                    refine ⟨32996108021237247490875125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21997405347491498327250083 32996108021237247490875125)
                    ·
                      refine ⟨3093385126990991952269543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32996108021237247490875125 3093385126990991952269543)
                      ·
                        rfl

theorem cell23_6024346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6024346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024346 prefixEnd_6024346 := by exact prefixLift 6024346
  have htrace : WordTrace (prefixWord ++ tailWord_6024346) baseStart_6024346 baseEnd_6024346 := by
    simpa [prefixWord, tailWord_6024346, baseEnd_6024346] using wordTrace_append hprefix tailTrace_6024346
  have hstable : (prefixWord ++ tailWord_6024346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024346).length < 2 ^ (prefixWord ++ tailWord_6024346).sum := by decide
  have hdescent : baseEnd_6024346 < baseStart_6024346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024354 : List Nat := [3, 3, 1, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_6024354 : Nat := 118140960795 + 6024354 * 2 ^ 59
def prefixEnd_6024354 : Nat := 4983230072969 + 3 ^ 40 * 6024354 * 2
def baseEnd_6024354 : Nat := 3093389234836227920969507

theorem tailTrace_6024354 : CollatzResearch.WordTrace tailWord_6024354 prefixEnd_6024354 3093389234836227920969507 := by
  unfold tailWord_6024354
  simp only [CollatzResearch.WordTrace]
  refine ⟨54931560404200452648792029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146484161077867873730112077 54931560404200452648792029)
  ·
    refine ⟨20599335151575169743297011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54931560404200452648792029 20599335151575169743297011)
    ·
      refine ⟨30899002727362754614945517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20599335151575169743297011 30899002727362754614945517)
      ·
        refine ⟨11587126022761032980604569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30899002727362754614945517 11587126022761032980604569)
        ·
          refine ⟨8690344517070774735453427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11587126022761032980604569 8690344517070774735453427)
          ·
            refine ⟨13035516775606162103180141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8690344517070774735453427 13035516775606162103180141)
            ·
              refine ⟨4888318790852310788692553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13035516775606162103180141 4888318790852310788692553)
              ·
                refine ⟨3666239093139233091519415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4888318790852310788692553 3666239093139233091519415)
                ·
                  refine ⟨5499358639708849637279123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666239093139233091519415 5499358639708849637279123)
                  ·
                    refine ⟨8249037959563274455918685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5499358639708849637279123 8249037959563274455918685)
                    ·
                      refine ⟨3093389234836227920969507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8249037959563274455918685 3093389234836227920969507)
                      ·
                        rfl

theorem cell23_6024354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_6024354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024354 prefixEnd_6024354 := by exact prefixLift 6024354
  have htrace : WordTrace (prefixWord ++ tailWord_6024354) baseStart_6024354 baseEnd_6024354 := by
    simpa [prefixWord, tailWord_6024354, baseEnd_6024354] using wordTrace_append hprefix tailTrace_6024354
  have hstable : (prefixWord ++ tailWord_6024354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024354).length < 2 ^ (prefixWord ++ tailWord_6024354).sum := by decide
  have hdescent : baseEnd_6024354 < baseStart_6024354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024370 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_6024370 : Nat := 118140960795 + 6024370 * 2 ^ 59
def prefixEnd_6024370 : Nat := 4983230072969 + 3 ^ 40 * 6024370 * 2
def baseEnd_6024370 : Nat := 1031132483508899952789811

theorem tailTrace_6024370 : CollatzResearch.WordTrace tailWord_6024370 prefixEnd_6024370 1031132483508899952789811 := by
  unfold tailWord_6024370
  simp only [CollatzResearch.WordTrace]
  refine ⟨54931706296185961331937641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146484550123162563551833709 54931706296185961331937641)
  ·
    refine ⟨41198779722139470998953231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54931706296185961331937641 41198779722139470998953231)
    ·
      refine ⟨61798169583209206498429847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41198779722139470998953231 61798169583209206498429847)
      ·
        refine ⟨92697254374813809747644771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61798169583209206498429847 92697254374813809747644771)
        ·
          refine ⟨139045881562220714621467157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92697254374813809747644771 139045881562220714621467157)
          ·
            refine ⟨6517775698229095997881273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139045881562220714621467157 6517775698229095997881273)
            ·
              refine ⟨4888331773671821998410955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6517775698229095997881273 4888331773671821998410955)
              ·
                refine ⟨7332497660507732997616433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888331773671821998410955 7332497660507732997616433)
                ·
                  refine ⟨5499373245380799748212325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7332497660507732997616433 5499373245380799748212325)
                  ·
                    refine ⟨1031132483508899952789811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5499373245380799748212325 1031132483508899952789811)
                    ·
                      rfl

theorem cell23_6024370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_6024370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024370 prefixEnd_6024370 := by exact prefixLift 6024370
  have htrace : WordTrace (prefixWord ++ tailWord_6024370) baseStart_6024370 baseEnd_6024370 := by
    simpa [prefixWord, tailWord_6024370, baseEnd_6024370] using wordTrace_append hprefix tailTrace_6024370
  have hstable : (prefixWord ++ tailWord_6024370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024370).length < 2 ^ (prefixWord ++ tailWord_6024370).sum := by decide
  have hdescent : baseEnd_6024370 < baseStart_6024370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024374 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6024374 : Nat := 118140960795 + 6024374 * 2 ^ 59
def prefixEnd_6024374 : Nat := 4983230072969 + 3 ^ 40 * 6024374 * 2
def baseEnd_6024374 : Nat := 1031133168149772614239805

theorem tailTrace_6024374 : CollatzResearch.WordTrace tailWord_6024374 prefixEnd_6024374 1031133168149772614239805 := by
  unfold tailWord_6024374
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732935692295584625681011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146484647384486236007264117 13732935692295584625681011)
  ·
    refine ⟨20599403538443376938521517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13732935692295584625681011 20599403538443376938521517)
    ·
      refine ⟨7724776326916266351945569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20599403538443376938521517 7724776326916266351945569)
      ·
        refine ⟨5793582245187199763959177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7724776326916266351945569 5793582245187199763959177)
        ·
          refine ⟨4345186683890399822969383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5793582245187199763959177 4345186683890399822969383)
          ·
            refine ⟨6517780025835599734454075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345186683890399822969383 6517780025835599734454075)
            ·
              refine ⟨9776670038753399601681113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6517780025835599734454075 9776670038753399601681113)
              ·
                refine ⟨7332502529065049701260835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9776670038753399601681113 7332502529065049701260835)
                ·
                  refine ⟨10998753793597574551891253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7332502529065049701260835 10998753793597574551891253)
                  ·
                    refine ⟨1031133168149772614239805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10998753793597574551891253 1031133168149772614239805)
                    ·
                      rfl

theorem cell23_6024374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6024374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024374 prefixEnd_6024374 := by exact prefixLift 6024374
  have htrace : WordTrace (prefixWord ++ tailWord_6024374) baseStart_6024374 baseEnd_6024374 := by
    simpa [prefixWord, tailWord_6024374, baseEnd_6024374] using wordTrace_append hprefix tailTrace_6024374
  have hstable : (prefixWord ++ tailWord_6024374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024374).length < 2 ^ (prefixWord ++ tailWord_6024374).sum := by decide
  have hdescent : baseEnd_6024374 < baseStart_6024374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024376 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 6, 1, 3]
def baseStart_6024376 : Nat := 118140960795 + 6024376 * 2 ^ 59
def prefixEnd_6024376 : Nat := 4983230072969 + 3 ^ 40 * 6024376 * 2
def baseEnd_6024376 : Nat := 3093400531410626834894405

theorem tailTrace_6024376 : CollatzResearch.WordTrace tailWord_6024376 prefixEnd_6024376 3093400531410626834894405 := by
  unfold tailWord_6024376
  simp only [CollatzResearch.WordTrace]
  refine ⟨109863522011361054176234491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146484696015148072234979321 109863522011361054176234491)
  ·
    refine ⟨164795283017041581264351737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109863522011361054176234491 164795283017041581264351737)
    ·
      refine ⟨123596462262781185948263803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164795283017041581264351737 123596462262781185948263803)
      ·
        refine ⟨185394693394171778922395705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123596462262781185948263803 185394693394171778922395705)
        ·
          refine ⟨139046020045628834191796779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185394693394171778922395705 139046020045628834191796779)
          ·
            refine ⟨208569030068443251287695169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139046020045628834191796779 208569030068443251287695169)
            ·
              refine ⟨156426772551332438465771377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208569030068443251287695169 156426772551332438465771377)
              ·
                refine ⟨117320079413499328849328533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156426772551332438465771377 117320079413499328849328533)
                ·
                  refine ⟨5499378722507781039812275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117320079413499328849328533 5499378722507781039812275)
                  ·
                    refine ⟨8249068083761671559718413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5499378722507781039812275 8249068083761671559718413)
                    ·
                      refine ⟨3093400531410626834894405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8249068083761671559718413 3093400531410626834894405)
                      ·
                        rfl

theorem cell23_6024376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_6024376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024376 prefixEnd_6024376 := by exact prefixLift 6024376
  have htrace : WordTrace (prefixWord ++ tailWord_6024376) baseStart_6024376 baseEnd_6024376 := by
    simpa [prefixWord, tailWord_6024376, baseEnd_6024376] using wordTrace_append hprefix tailTrace_6024376
  have hstable : (prefixWord ++ tailWord_6024376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024376).length < 2 ^ (prefixWord ++ tailWord_6024376).sum := by decide
  have hdescent : baseEnd_6024376 < baseStart_6024376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024380 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_6024380 : Nat := 118140960795 + 6024380 * 2 ^ 59
def prefixEnd_6024380 : Nat := 4983230072969 + 3 ^ 40 * 6024380 * 2
def baseEnd_6024380 : Nat := 3093402585333244819244387

theorem tailTrace_6024380 : CollatzResearch.WordTrace tailWord_6024380 prefixEnd_6024380 3093402585333244819244387 := by
  unfold tailWord_6024380
  simp only [CollatzResearch.WordTrace]
  refine ⟨109863594957353808517807297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146484793276471744690409729 109863594957353808517807297)
  ·
    refine ⟨82397696218015356388355473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109863594957353808517807297 82397696218015356388355473)
    ·
      refine ⟨61798272163511517291266605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82397696218015356388355473 61798272163511517291266605)
      ·
        refine ⟨23174352061316818984224977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61798272163511517291266605 23174352061316818984224977)
        ·
          refine ⟨17380764045987614238168733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23174352061316818984224977 17380764045987614238168733)
          ·
            refine ⟨6517786517245355339313275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17380764045987614238168733 6517786517245355339313275)
            ·
              refine ⟨9776679775868033008969913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6517786517245355339313275 9776679775868033008969913)
              ·
                refine ⟨7332509831901024756727435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9776679775868033008969913 7332509831901024756727435)
                ·
                  refine ⟨10998764747851537135091153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7332509831901024756727435 10998764747851537135091153)
                  ·
                    refine ⟨8249073560888652851318365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10998764747851537135091153 8249073560888652851318365)
                    ·
                      refine ⟨3093402585333244819244387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8249073560888652851318365 3093402585333244819244387)
                      ·
                        rfl

theorem cell23_6024380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_6024380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024380 prefixEnd_6024380 := by exact prefixLift 6024380
  have htrace : WordTrace (prefixWord ++ tailWord_6024380) baseStart_6024380 baseEnd_6024380 := by
    simpa [prefixWord, tailWord_6024380, baseEnd_6024380] using wordTrace_append hprefix tailTrace_6024380
  have hstable : (prefixWord ++ tailWord_6024380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024380).length < 2 ^ (prefixWord ++ tailWord_6024380).sum := by decide
  have hdescent : baseEnd_6024380 < baseStart_6024380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024397 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_6024397 : Nat := 118140960795 + 6024397 * 2 ^ 59
def prefixEnd_6024397 : Nat := 4983230072969 + 3 ^ 40 * 6024397 * 2
def baseEnd_6024397 : Nat := 3093411314504371252731809

theorem tailTrace_6024397 : CollatzResearch.WordTrace tailWord_6024397 prefixEnd_6024397 3093411314504371252731809 := by
  unfold tailWord_6024397
  simp only [CollatzResearch.WordTrace]
  refine ⟨219727809955646028938983445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146485206637097352625988963 219727809955646028938983445)
  ·
    refine ⟨10299741091670907606514849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 219727809955646028938983445 10299741091670907606514849)
    ·
      refine ⟨7724805818753180704886137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10299741091670907606514849 7724805818753180704886137)
      ·
        refine ⟨5793604364064885528664603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7724805818753180704886137 5793604364064885528664603)
        ·
          refine ⟨8690406546097328292996905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793604364064885528664603 8690406546097328292996905)
          ·
            refine ⟨6517804909572996219747679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8690406546097328292996905 6517804909572996219747679)
            ·
              refine ⟨9776707364359494329621519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6517804909572996219747679 9776707364359494329621519)
              ·
                refine ⟨14665061046539241494432279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9776707364359494329621519 14665061046539241494432279)
                ·
                  refine ⟨21997591569808862241648419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14665061046539241494432279 21997591569808862241648419)
                  ·
                    refine ⟨32996387354713293362472629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21997591569808862241648419 32996387354713293362472629)
                    ·
                      refine ⟨3093411314504371252731809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32996387354713293362472629 3093411314504371252731809)
                      ·
                        rfl

theorem cell23_6024397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_6024397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024397 prefixEnd_6024397 := by exact prefixLift 6024397
  have htrace : WordTrace (prefixWord ++ tailWord_6024397) baseStart_6024397 baseEnd_6024397 := by
    simpa [prefixWord, tailWord_6024397, baseEnd_6024397] using wordTrace_append hprefix tailTrace_6024397
  have hstable : (prefixWord ++ tailWord_6024397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024397).length < 2 ^ (prefixWord ++ tailWord_6024397).sum := by decide
  have hdescent : baseEnd_6024397 < baseStart_6024397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024409 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 2, 6]
def baseStart_6024409 : Nat := 118140960795 + 6024409 * 2 ^ 59
def prefixEnd_6024409 : Nat := 4983230072969 + 3 ^ 40 * 6024409 * 2
def baseEnd_6024409 : Nat := 1031139158757408401927251

theorem tailTrace_6024409 : CollatzResearch.WordTrace tailWord_6024409 prefixEnd_6024409 1031139158757408401927251 := by
  unfold tailWord_6024409
  simp only [CollatzResearch.WordTrace]
  refine ⟨219728247631602554988420281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146485498421068369992280187 219728247631602554988420281)
  ·
    refine ⟨164796185723701916241315211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219728247631602554988420281 164796185723701916241315211)
    ·
      refine ⟨247194278585552874361972817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164796185723701916241315211 247194278585552874361972817)
      ·
        refine ⟨185395708939164655771479613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247194278585552874361972817 185395708939164655771479613)
        ·
          refine ⟨69523390852186745914304855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185395708939164655771479613 69523390852186745914304855)
          ·
            refine ⟨104285086278280118871457283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69523390852186745914304855 104285086278280118871457283)
            ·
              refine ⟨156427629417420178307185925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104285086278280118871457283 156427629417420178307185925)
              ·
                refine ⟨29330180515766283432597361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156427629417420178307185925 29330180515766283432597361)
                ·
                  refine ⟨21997635386824712574448021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29330180515766283432597361 21997635386824712574448021)
                  ·
                    refine ⟨1031139158757408401927251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21997635386824712574448021 1031139158757408401927251)
                    ·
                      rfl

theorem cell23_6024409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_6024409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024409 prefixEnd_6024409 := by exact prefixLift 6024409
  have htrace : WordTrace (prefixWord ++ tailWord_6024409) baseStart_6024409 baseEnd_6024409 := by
    simpa [prefixWord, tailWord_6024409, baseEnd_6024409] using wordTrace_append hprefix tailTrace_6024409
  have hstable : (prefixWord ++ tailWord_6024409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024409).length < 2 ^ (prefixWord ++ tailWord_6024409).sum := by decide
  have hdescent : baseEnd_6024409 < baseStart_6024409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024426 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_6024426 : Nat := 118140960795 + 6024426 * 2 ^ 59
def prefixEnd_6024426 : Nat := 4983230072969 + 3 ^ 40 * 6024426 * 2
def baseEnd_6024426 : Nat := 1031142068481117213089725

theorem tailTrace_6024426 : CollatzResearch.WordTrace tailWord_6024426 prefixEnd_6024426 1031142068481117213089725 := by
  unfold tailWord_6024426
  simp only [CollatzResearch.WordTrace]
  refine ⟨54932216918135241722947283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146485911781693977927859421 54932216918135241722947283)
  ·
    refine ⟨82398325377202862584420925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54932216918135241722947283 82398325377202862584420925)
    ·
      refine ⟨30899372016451073469157847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82398325377202862584420925 30899372016451073469157847)
      ·
        refine ⟨46349058024676610203736771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30899372016451073469157847 46349058024676610203736771)
        ·
          refine ⟨69523587037014915305605157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46349058024676610203736771 69523587037014915305605157)
          ·
            refine ⟨13035672569440296619800967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69523587037014915305605157 13035672569440296619800967)
            ·
              refine ⟨19553508854160444929701451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13035672569440296619800967 19553508854160444929701451)
              ·
                refine ⟨29330263281240667394552177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19553508854160444929701451 29330263281240667394552177)
                ·
                  refine ⟨21997697460930500545914133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29330263281240667394552177 21997697460930500545914133)
                  ·
                    refine ⟨1031142068481117213089725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21997697460930500545914133 1031142068481117213089725)
                    ·
                      rfl

theorem cell23_6024426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_6024426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024426 prefixEnd_6024426 := by exact prefixLift 6024426
  have htrace : WordTrace (prefixWord ++ tailWord_6024426) baseStart_6024426 baseEnd_6024426 := by
    simpa [prefixWord, tailWord_6024426, baseEnd_6024426] using wordTrace_append hprefix tailTrace_6024426
  have hstable : (prefixWord ++ tailWord_6024426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024426).length < 2 ^ (prefixWord ++ tailWord_6024426).sum := by decide
  have hdescent : baseEnd_6024426 < baseStart_6024426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024433 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 6, 2, 2]
def baseStart_6024433 : Nat := 118140960795 + 6024433 * 2 ^ 59
def prefixEnd_6024433 : Nat := 4983230072969 + 3 ^ 40 * 6024433 * 2
def baseEnd_6024433 : Nat := 3093429799807933111881643

theorem tailTrace_6024433 : CollatzResearch.WordTrace tailWord_6024433 prefixEnd_6024433 3093429799807933111881643 := by
  unfold tailWord_6024433
  simp only [CollatzResearch.WordTrace]
  refine ⟨219729122983515607087293953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146486081989010404724862635 219729122983515607087293953)
  ·
    refine ⟨164796842237636705315470465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219729122983515607087293953 164796842237636705315470465)
    ·
      refine ⟨123597631678227528986602849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164796842237636705315470465 123597631678227528986602849)
      ·
        refine ⟨92698223758670646739952137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123597631678227528986602849 92698223758670646739952137)
        ·
          refine ⟨69523667819002985054964103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92698223758670646739952137 69523667819002985054964103)
          ·
            refine ⟨104285501728504477582446155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69523667819002985054964103 104285501728504477582446155)
            ·
              refine ⟨156428252592756716373669233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104285501728504477582446155 156428252592756716373669233)
              ·
                refine ⟨117321189444567537280251925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156428252592756716373669233 117321189444567537280251925)
                ·
                  refine ⟨5499430755214103310011809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117321189444567537280251925 5499430755214103310011809)
                  ·
                    refine ⟨4124573066410577482508857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5499430755214103310011809 4124573066410577482508857)
                    ·
                      refine ⟨3093429799807933111881643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124573066410577482508857 3093429799807933111881643)
                      ·
                        rfl

theorem cell23_6024433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_6024433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024433 prefixEnd_6024433 := by exact prefixLift 6024433
  have htrace : WordTrace (prefixWord ++ tailWord_6024433) baseStart_6024433 baseEnd_6024433 := by
    simpa [prefixWord, tailWord_6024433, baseEnd_6024433] using wordTrace_append hprefix tailTrace_6024433
  have hstable : (prefixWord ++ tailWord_6024433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024433).length < 2 ^ (prefixWord ++ tailWord_6024433).sum := by decide
  have hdescent : baseEnd_6024433 < baseStart_6024433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024439 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 7]
def baseStart_6024439 : Nat := 118140960795 + 6024439 * 2 ^ 59
def prefixEnd_6024439 : Nat := 4983230072969 + 3 ^ 40 * 6024439 * 2
def baseEnd_6024439 : Nat := 343714764521317787600735

theorem tailTrace_6024439 : CollatzResearch.WordTrace tailWord_6024439 prefixEnd_6024439 343714764521317787600735 := by
  unfold tailWord_6024439
  simp only [CollatzResearch.WordTrace]
  refine ⟨219729341821493870112012371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146486227880995913408008247 219729341821493870112012371)
  ·
    refine ⟨329594012732240805168018557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219729341821493870112012371 329594012732240805168018557)
    ·
      refine ⟨123597754774590301938006959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329594012732240805168018557 123597754774590301938006959)
      ·
        refine ⟨185396632161885452907010439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123597754774590301938006959 185396632161885452907010439)
        ·
          refine ⟨278094948242828179360515659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185396632161885452907010439 278094948242828179360515659)
          ·
            refine ⟨417142422364242269040773489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278094948242828179360515659 417142422364242269040773489)
            ·
              refine ⟨312856816773181701780580117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417142422364242269040773489 312856816773181701780580117)
              ·
                refine ⟨14665163286242892270964693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 312856816773181701780580117 14665163286242892270964693)
                ·
                  refine ⟨343714764521317787600735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14665163286242892270964693 343714764521317787600735)
                  ·
                    rfl

theorem cell23_6024439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 7].length) (baseStart_6024439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024439 prefixEnd_6024439 := by exact prefixLift 6024439
  have htrace : WordTrace (prefixWord ++ tailWord_6024439) baseStart_6024439 baseEnd_6024439 := by
    simpa [prefixWord, tailWord_6024439, baseEnd_6024439] using wordTrace_append hprefix tailTrace_6024439
  have hstable : (prefixWord ++ tailWord_6024439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024439).length < 2 ^ (prefixWord ++ tailWord_6024439).sum := by decide
  have hdescent : baseEnd_6024439 < baseStart_6024439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024506 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_6024506 : Nat := 118140960795 + 6024506 * 2 ^ 59
def prefixEnd_6024506 : Nat := 4983230072969 + 3 ^ 40 * 6024506 * 2
def baseEnd_6024506 : Nat := 3093467283895711326268807

theorem tailTrace_6024506 : CollatzResearch.WordTrace tailWord_6024506 prefixEnd_6024506 3093467283895711326268807 := by
  unfold tailWord_6024506
  simp only [CollatzResearch.WordTrace]
  refine ⟨54932946378062785138675343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146487857008167427036467581 54932946378062785138675343)
  ·
    refine ⟨82399419567094177708013015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54932946378062785138675343 82399419567094177708013015)
    ·
      refine ⟨123599129350641266562019523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82399419567094177708013015 123599129350641266562019523)
      ·
        refine ⟨185398694025961899843029285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123599129350641266562019523 185398694025961899843029285)
        ·
          refine ⟨34762255129867856220567991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185398694025961899843029285 34762255129867856220567991)
          ·
            refine ⟨52143382694801784330851987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34762255129867856220567991 52143382694801784330851987)
            ·
              refine ⟨78215074042202676496277981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52143382694801784330851987 78215074042202676496277981)
              ·
                refine ⟨29330652765826003686104243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78215074042202676496277981 29330652765826003686104243)
                ·
                  refine ⟨43995979148739005529156365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29330652765826003686104243 43995979148739005529156365)
                  ·
                    refine ⟨16498492180777127073433637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43995979148739005529156365 16498492180777127073433637)
                    ·
                      refine ⟨3093467283895711326268807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16498492180777127073433637 3093467283895711326268807)
                      ·
                        rfl

theorem cell23_6024506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_6024506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024506 prefixEnd_6024506 := by exact prefixLift 6024506
  have htrace : WordTrace (prefixWord ++ tailWord_6024506) baseStart_6024506 baseEnd_6024506 := by
    simpa [prefixWord, tailWord_6024506, baseEnd_6024506] using wordTrace_append hprefix tailTrace_6024506
  have hstable : (prefixWord ++ tailWord_6024506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024506).length < 2 ^ (prefixWord ++ tailWord_6024506).sum := by decide
  have hdescent : baseEnd_6024506 < baseStart_6024506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024584 : List Nat := [2, 1, 3, 3, 1, 4, 2, 2, 1, 4]
def baseStart_6024584 : Nat := 118140960795 + 6024584 * 2 ^ 59
def prefixEnd_6024584 : Nat := 4983230072969 + 3 ^ 40 * 6024584 * 2
def baseEnd_6024584 : Nat := 1031169111795587340364483

theorem tailTrace_6024584 : CollatzResearch.WordTrace tailWord_6024584 prefixEnd_6024584 1031169111795587340364483 := by
  unfold tailWord_6024584
  simp only [CollatzResearch.WordTrace]
  refine ⟨109867315202984279938020403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146489753603979039917360537 109867315202984279938020403)
  ·
    refine ⟨164800972804476419907030605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109867315202984279938020403 164800972804476419907030605)
    ·
      refine ⟨61800364801678657465136477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164800972804476419907030605 61800364801678657465136477)
      ·
        refine ⟨23175136800629496549426179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61800364801678657465136477 23175136800629496549426179)
        ·
          refine ⟨34762705200944244824139269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23175136800629496549426179 34762705200944244824139269)
          ·
            refine ⟨6518007225177045904526113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34762705200944244824139269 6518007225177045904526113)
            ·
              refine ⟨4888505418882784428394585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6518007225177045904526113 4888505418882784428394585)
              ·
                refine ⟨3666379064162088321295939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4888505418882784428394585 3666379064162088321295939)
                ·
                  refine ⟨5499568596243132481943909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666379064162088321295939 5499568596243132481943909)
                  ·
                    refine ⟨1031169111795587340364483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5499568596243132481943909 1031169111795587340364483)
                    ·
                      rfl

theorem cell23_6024584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_6024584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024584 prefixEnd_6024584 := by exact prefixLift 6024584
  have htrace : WordTrace (prefixWord ++ tailWord_6024584) baseStart_6024584 baseEnd_6024584 := by
    simpa [prefixWord, tailWord_6024584, baseEnd_6024584] using wordTrace_append hprefix tailTrace_6024584
  have hstable : (prefixWord ++ tailWord_6024584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024584).length < 2 ^ (prefixWord ++ tailWord_6024584).sum := by decide
  have hdescent : baseEnd_6024584 < baseStart_6024584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024613 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 1, 8, 2]
def baseStart_6024613 : Nat := 118140960795 + 6024613 * 2 ^ 59
def prefixEnd_6024613 : Nat := 4983230072969 + 3 ^ 40 * 6024613 * 2
def baseEnd_6024613 : Nat := 3093522226325742407630815

theorem tailTrace_6024613 : CollatzResearch.WordTrace tailWord_6024613 prefixEnd_6024613 3093522226325742407630815 := by
  unfold tailWord_6024613
  simp only [CollatzResearch.WordTrace]
  refine ⟨219735688122863497828846493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146490458748575665219230995 219735688122863497828846493)
  ·
    refine ⟨82400883046073811685817435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219735688122863497828846493 82400883046073811685817435)
    ·
      refine ⟨123601324569110717528726153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82400883046073811685817435 123601324569110717528726153)
      ·
        refine ⟨92700993426833038146544615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123601324569110717528726153 92700993426833038146544615)
        ·
          refine ⟨139051490140249557219816923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92700993426833038146544615 139051490140249557219816923)
          ·
            refine ⟨208577235210374335829725385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139051490140249557219816923 208577235210374335829725385)
            ·
              refine ⟨156432926407780751872294039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208577235210374335829725385 156432926407780751872294039)
              ·
                refine ⟨234649389611671127808441059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156432926407780751872294039 234649389611671127808441059)
                ·
                  refine ⟨351974084417506691712661589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234649389611671127808441059 351974084417506691712661589)
                  ·
                    refine ⟨4124696301767656543507753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 351974084417506691712661589 4124696301767656543507753)
                    ·
                      refine ⟨3093522226325742407630815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124696301767656543507753 3093522226325742407630815)
                      ·
                        rfl

theorem cell23_6024613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_6024613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024613 prefixEnd_6024613 := by exact prefixLift 6024613
  have htrace : WordTrace (prefixWord ++ tailWord_6024613) baseStart_6024613 baseEnd_6024613 := by
    simpa [prefixWord, tailWord_6024613, baseEnd_6024613] using wordTrace_append hprefix tailTrace_6024613
  have hstable : (prefixWord ++ tailWord_6024613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024613).length < 2 ^ (prefixWord ++ tailWord_6024613).sum := by decide
  have hdescent : baseEnd_6024613 < baseStart_6024613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024640 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 2, 4]
def baseStart_6024640 : Nat := 118140960795 + 6024640 * 2 ^ 59
def prefixEnd_6024640 : Nat := 4983230072969 + 3 ^ 40 * 6024640 * 2
def baseEnd_6024640 : Nat := 1031178696767804600664397

theorem tailTrace_6024640 : CollatzResearch.WordTrace tailWord_6024640 prefixEnd_6024640 1031178696767804600664397 := by
  unfold tailWord_6024640
  simp only [CollatzResearch.WordTrace]
  refine ⟨109868336446882840720039687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146491115262510454293386249 109868336446882840720039687)
  ·
    refine ⟨164802504670324261080059531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109868336446882840720039687 164802504670324261080059531)
    ·
      refine ⟨247203757005486391620089297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164802504670324261080059531 247203757005486391620089297)
      ·
        refine ⟨185402817754114793715066973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247203757005486391620089297 185402817754114793715066973)
        ·
          refine ⟨69526056657793047643150115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185402817754114793715066973 69526056657793047643150115)
          ·
            refine ⟨104289084986689571464725173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69526056657793047643150115 104289084986689571464725173)
            ·
              refine ⟨9777101717502147324817985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104289084986689571464725173 9777101717502147324817985)
              ·
                refine ⟨7332826288126610493613489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9777101717502147324817985 7332826288126610493613489)
                ·
                  refine ⟨5499619716094957870210117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7332826288126610493613489 5499619716094957870210117)
                  ·
                    refine ⟨1031178696767804600664397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5499619716094957870210117 1031178696767804600664397)
                    ·
                      rfl

theorem cell23_6024640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2, 4].length) (baseStart_6024640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024640 prefixEnd_6024640 := by exact prefixLift 6024640
  have htrace : WordTrace (prefixWord ++ tailWord_6024640) baseStart_6024640 baseEnd_6024640 := by
    simpa [prefixWord, tailWord_6024640, baseEnd_6024640] using wordTrace_append hprefix tailTrace_6024640
  have hstable : (prefixWord ++ tailWord_6024640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024640).length < 2 ^ (prefixWord ++ tailWord_6024640).sum := by decide
  have hdescent : baseEnd_6024640 < baseStart_6024640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024647 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 3, 2, 2]
def baseStart_6024647 : Nat := 118140960795 + 6024647 * 2 ^ 59
def prefixEnd_6024647 : Nat := 4983230072969 + 3 ^ 40 * 6024647 * 2
def baseEnd_6024647 : Nat := 3093539684667995274605659

theorem tailTrace_6024647 : CollatzResearch.WordTrace tailWord_6024647 prefixEnd_6024647 3093539684667995274605659 := by
  unfold tailWord_6024647
  simp only [CollatzResearch.WordTrace]
  refine ⟨219736928204740321635584195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146491285469826881090389463 219736928204740321635584195)
  ·
    refine ⟨329605392307110482453376293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219736928204740321635584195 329605392307110482453376293)
    ·
      refine ⟨61801011057583215460008055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329605392307110482453376293 61801011057583215460008055)
      ·
        refine ⟨92701516586374823190012083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61801011057583215460008055 92701516586374823190012083)
        ·
          refine ⟨139052274879562234785018125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92701516586374823190012083 139052274879562234785018125)
          ·
            refine ⟨52144603079835838044381797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139052274879562234785018125 52144603079835838044381797)
            ·
              refine ⟨9777113077469219633321587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52144603079835838044381797 9777113077469219633321587)
              ·
                refine ⟨14665669616203829449982381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9777113077469219633321587 14665669616203829449982381)
                ·
                  refine ⟨5499626106076436043743393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14665669616203829449982381 5499626106076436043743393)
                  ·
                    refine ⟨4124719579557327032807545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5499626106076436043743393 4124719579557327032807545)
                    ·
                      refine ⟨3093539684667995274605659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124719579557327032807545 3093539684667995274605659)
                      ·
                        rfl

theorem cell23_6024647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_6024647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024647 prefixEnd_6024647 := by exact prefixLift 6024647
  have htrace : WordTrace (prefixWord ++ tailWord_6024647) baseStart_6024647 baseEnd_6024647 := by
    simpa [prefixWord, tailWord_6024647, baseEnd_6024647] using wordTrace_append hprefix tailTrace_6024647
  have hstable : (prefixWord ++ tailWord_6024647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024647).length < 2 ^ (prefixWord ++ tailWord_6024647).sum := by decide
  have hdescent : baseEnd_6024647 < baseStart_6024647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024656 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_6024656 : Nat := 118140960795 + 6024656 * 2 ^ 59
def prefixEnd_6024656 : Nat := 4983230072969 + 3 ^ 40 * 6024656 * 2
def baseEnd_6024656 : Nat := 3093544305993885739393117

theorem tailTrace_6024656 : CollatzResearch.WordTrace tailWord_6024656 prefixEnd_6024656 3093544305993885739393117 := by
  unfold tailWord_6024656
  simp only [CollatzResearch.WordTrace]
  refine ⟨109868628230853858086330911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146491504307805144115107881 109868628230853858086330911)
  ·
    refine ⟨164802942346280787129496367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109868628230853858086330911 164802942346280787129496367)
    ·
      refine ⟨247204413519421180694244551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164802942346280787129496367 247204413519421180694244551)
      ·
        refine ⟨370806620279131771041366827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247204413519421180694244551 370806620279131771041366827)
        ·
          refine ⟨556209930418697656562050241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370806620279131771041366827 556209930418697656562050241)
          ·
            refine ⟨417157447814023242421537681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556209930418697656562050241 417157447814023242421537681)
            ·
              refine ⟨312868085860517431816153261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417157447814023242421537681 312868085860517431816153261)
              ·
                refine ⟨117325532197694036931057473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312868085860517431816153261 117325532197694036931057473)
                ·
                  refine ⟨87994149148270527698293105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117325532197694036931057473 87994149148270527698293105)
                  ·
                    refine ⟨65995611861202895773719829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87994149148270527698293105 65995611861202895773719829)
                    ·
                      refine ⟨3093544305993885739393117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65995611861202895773719829 3093544305993885739393117)
                      ·
                        rfl

theorem cell23_6024656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_6024656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024656 prefixEnd_6024656 := by exact prefixLift 6024656
  have htrace : WordTrace (prefixWord ++ tailWord_6024656) baseStart_6024656 baseEnd_6024656 := by
    simpa [prefixWord, tailWord_6024656, baseEnd_6024656] using wordTrace_append hprefix tailTrace_6024656
  have hstable : (prefixWord ++ tailWord_6024656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024656).length < 2 ^ (prefixWord ++ tailWord_6024656).sum := by decide
  have hdescent : baseEnd_6024656 < baseStart_6024656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024660 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_6024660 : Nat := 118140960795 + 6024660 * 2 ^ 59
def prefixEnd_6024660 : Nat := 4983230072969 + 3 ^ 40 * 6024660 * 2
def baseEnd_6024660 : Nat := 3093546359916503723743099

theorem tailTrace_6024660 : CollatzResearch.WordTrace tailWord_6024660 prefixEnd_6024660 3093546359916503723743099 := by
  unfold tailWord_6024660
  simp only [CollatzResearch.WordTrace]
  refine ⟨109868701176846612427903717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146491601569128816570538289 109868701176846612427903717)
  ·
    refine ⟨20600381470658739830231947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109868701176846612427903717 20600381470658739830231947)
    ·
      refine ⟨30900572205988109745347921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20600381470658739830231947 30900572205988109745347921)
      ·
        refine ⟨23175429154491082309010941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30900572205988109745347921 23175429154491082309010941)
        ·
          refine ⟨8690785932934155865879103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23175429154491082309010941 8690785932934155865879103)
          ·
            refine ⟨13036178899401233798818655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8690785932934155865879103 13036178899401233798818655)
            ·
              refine ⟨19554268349101850698227983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13036178899401233798818655 19554268349101850698227983)
              ·
                refine ⟨29331402523652776047341975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19554268349101850698227983 29331402523652776047341975)
                ·
                  refine ⟨43997103785479164071012963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29331402523652776047341975 43997103785479164071012963)
                  ·
                    refine ⟨65995655678218746106519445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43997103785479164071012963 65995655678218746106519445)
                    ·
                      refine ⟨3093546359916503723743099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65995655678218746106519445 3093546359916503723743099)
                      ·
                        rfl

theorem cell23_6024660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_6024660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024660 prefixEnd_6024660 := by exact prefixLift 6024660
  have htrace : WordTrace (prefixWord ++ tailWord_6024660) baseStart_6024660 baseEnd_6024660 := by
    simpa [prefixWord, tailWord_6024660, baseEnd_6024660] using wordTrace_append hprefix tailTrace_6024660
  have hstable : (prefixWord ++ tailWord_6024660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024660).length < 2 ^ (prefixWord ++ tailWord_6024660).sum := by decide
  have hdescent : baseEnd_6024660 < baseStart_6024660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024680 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_6024680 : Nat := 118140960795 + 6024680 * 2 ^ 59
def prefixEnd_6024680 : Nat := 4983230072969 + 3 ^ 40 * 6024680 * 2
def baseEnd_6024680 : Nat := 3093556629529593645493007

theorem tailTrace_6024680 : CollatzResearch.WordTrace tailWord_6024680 prefixEnd_6024680 3093556629529593645493007 := by
  unfold tailWord_6024680
  simp only [CollatzResearch.WordTrace]
  refine ⟨109869065906810384135767747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146492087875747178847690329 109869065906810384135767747)
  ·
    refine ⟨164803598860215576203651621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109869065906810384135767747 164803598860215576203651621)
    ·
      refine ⟨30900674786290420538184679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164803598860215576203651621 30900674786290420538184679)
      ·
        refine ⟨46351012179435630807277019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30900674786290420538184679 46351012179435630807277019)
        ·
          refine ⟨69526518269153446210915529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46351012179435630807277019 69526518269153446210915529)
          ·
            refine ⟨52144888701865084658186647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69526518269153446210915529 52144888701865084658186647)
            ·
              refine ⟨78217333052797626987279971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52144888701865084658186647 78217333052797626987279971)
              ·
                refine ⟨117325999579196440480919957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78217333052797626987279971 117325999579196440480919957)
                ·
                  refine ⟨5499656230274833147543123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117325999579196440480919957 5499656230274833147543123)
                  ·
                    refine ⟨8249484345412249721314685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5499656230274833147543123 8249484345412249721314685)
                    ·
                      refine ⟨3093556629529593645493007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8249484345412249721314685 3093556629529593645493007)
                      ·
                        rfl

theorem cell23_6024680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_6024680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024680 prefixEnd_6024680 := by exact prefixLift 6024680
  have htrace : WordTrace (prefixWord ++ tailWord_6024680) baseStart_6024680 baseEnd_6024680 := by
    simpa [prefixWord, tailWord_6024680, baseEnd_6024680] using wordTrace_append hprefix tailTrace_6024680
  have hstable : (prefixWord ++ tailWord_6024680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024680).length < 2 ^ (prefixWord ++ tailWord_6024680).sum := by decide
  have hdescent : baseEnd_6024680 < baseStart_6024680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024714 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3]
def baseStart_6024714 : Nat := 118140960795 + 6024714 * 2 ^ 59
def prefixEnd_6024714 : Nat := 4983230072969 + 3 ^ 40 * 6024714 * 2
def baseEnd_6024714 : Nat := 3093574087871846512467851

theorem tailTrace_6024714 : CollatzResearch.WordTrace tailWord_6024714 prefixEnd_6024714 3093574087871846512467851 := by
  unfold tailWord_6024714
  simp only [CollatzResearch.WordTrace]
  refine ⟨54934842973874398019568299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146492914596998394718848797 54934842973874398019568299)
  ·
    refine ⟨82402264460811597029352449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54934842973874398019568299 82402264460811597029352449)
    ·
      refine ⟨61801698345608697772014337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82402264460811597029352449 61801698345608697772014337)
      ·
        refine ⟨46351273759206523329010753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61801698345608697772014337 46351273759206523329010753)
        ·
          refine ⟨34763455319404892496758065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46351273759206523329010753 34763455319404892496758065)
          ·
            refine ⟨26072591489553669372568549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34763455319404892496758065 26072591489553669372568549)
            ·
              refine ⟨4888610904291313007356603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26072591489553669372568549 4888610904291313007356603)
              ·
                refine ⟨7332916356436969511034905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888610904291313007356603 7332916356436969511034905)
                ·
                  refine ⟨5499687267327727133276179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7332916356436969511034905 5499687267327727133276179)
                  ·
                    refine ⟨8249530900991590699914269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5499687267327727133276179 8249530900991590699914269)
                    ·
                      refine ⟨3093574087871846512467851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8249530900991590699914269 3093574087871846512467851)
                      ·
                        rfl

theorem cell23_6024714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_6024714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024714 prefixEnd_6024714 := by exact prefixLift 6024714
  have htrace : WordTrace (prefixWord ++ tailWord_6024714) baseStart_6024714 baseEnd_6024714 := by
    simpa [prefixWord, tailWord_6024714, baseEnd_6024714] using wordTrace_append hprefix tailTrace_6024714
  have hstable : (prefixWord ++ tailWord_6024714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024714).length < 2 ^ (prefixWord ++ tailWord_6024714).sum := by decide
  have hdescent : baseEnd_6024714 < baseStart_6024714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024723 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 5]
def baseStart_6024723 : Nat := 118140960795 + 6024723 * 2 ^ 59
def prefixEnd_6024723 : Nat := 4983230072969 + 3 ^ 40 * 6024723 * 2
def baseEnd_6024723 : Nat := 3093578709197736977255309

theorem tailTrace_6024723 : CollatzResearch.WordTrace tailWord_6024723 prefixEnd_6024723 3093578709197736977255309 := by
  unfold tailWord_6024723
  simp only [CollatzResearch.WordTrace]
  refine ⟨219739700152464986615350823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146493133434976657743567215 219739700152464986615350823)
  ·
    refine ⟨329609550228697479923026235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219739700152464986615350823 329609550228697479923026235)
    ·
      refine ⟨494414325343046219884539353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329609550228697479923026235 494414325343046219884539353)
      ·
        refine ⟨370810744007284664913404515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494414325343046219884539353 370810744007284664913404515)
        ·
          refine ⟨556216116010926997370106773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370810744007284664913404515 556216116010926997370106773)
          ·
            refine ⟨26072630438012203001723755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 556216116010926997370106773 26072630438012203001723755)
            ·
              refine ⟨39108945657018304502585633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26072630438012203001723755 39108945657018304502585633)
              ·
                refine ⟨29331709242763728376939225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39108945657018304502585633 29331709242763728376939225)
                ·
                  refine ⟨21998781932072796282704419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29331709242763728376939225 21998781932072796282704419)
                  ·
                    refine ⟨32998172898109194424056629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21998781932072796282704419 32998172898109194424056629)
                    ·
                      refine ⟨3093578709197736977255309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32998172898109194424056629 3093578709197736977255309)
                      ·
                        rfl

theorem cell23_6024723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_6024723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024723 prefixEnd_6024723 := by exact prefixLift 6024723
  have htrace : WordTrace (prefixWord ++ tailWord_6024723) baseStart_6024723 baseEnd_6024723 := by
    simpa [prefixWord, tailWord_6024723, baseEnd_6024723] using wordTrace_append hprefix tailTrace_6024723
  have hstable : (prefixWord ++ tailWord_6024723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024723).length < 2 ^ (prefixWord ++ tailWord_6024723).sum := by decide
  have hdescent : baseEnd_6024723 < baseStart_6024723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024737 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 1, 4, 2]
def baseStart_6024737 : Nat := 118140960795 + 6024737 * 2 ^ 59
def prefixEnd_6024737 : Nat := 4983230072969 + 3 ^ 40 * 6024737 * 2
def baseEnd_6024737 : Nat := 3093585897926899922480245

theorem tailTrace_6024737 : CollatzResearch.WordTrace tailWord_6024737 prefixEnd_6024737 3093585897926899922480245 := by
  unfold tailWord_6024737
  simp only [CollatzResearch.WordTrace]
  refine ⟨219740210774414267006360465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146493473849609511337573643 219740210774414267006360465)
  ·
    refine ⟨164805158080810700254770349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219740210774414267006360465 164805158080810700254770349)
    ·
      refine ⟨61801934280304012595538881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164805158080810700254770349 61801934280304012595538881)
      ·
        refine ⟨46351450710228009446654161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61801934280304012595538881 46351450710228009446654161)
        ·
          refine ⟨34763588032671007084990621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46351450710228009446654161 34763588032671007084990621)
          ·
            refine ⟨13036345512251627656871483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34763588032671007084990621 13036345512251627656871483)
            ·
              refine ⟨19554518268377441485307225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13036345512251627656871483 19554518268377441485307225)
              ·
                refine ⟨14665888701283081113980419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19554518268377441485307225 14665888701283081113980419)
                ·
                  refine ⟨21998833051924621670970629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14665888701283081113980419 21998833051924621670970629)
                  ·
                    refine ⟨4124781197235866563306993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21998833051924621670970629 4124781197235866563306993)
                    ·
                      refine ⟨3093585897926899922480245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124781197235866563306993 3093585897926899922480245)
                      ·
                        rfl

theorem cell23_6024737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_6024737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024737 prefixEnd_6024737 := by exact prefixLift 6024737
  have htrace : WordTrace (prefixWord ++ tailWord_6024737) baseStart_6024737 baseEnd_6024737 := by
    simpa [prefixWord, tailWord_6024737, baseEnd_6024737] using wordTrace_append hprefix tailTrace_6024737
  have hstable : (prefixWord ++ tailWord_6024737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024737).length < 2 ^ (prefixWord ++ tailWord_6024737).sum := by decide
  have hdescent : baseEnd_6024737 < baseStart_6024737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024773 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_6024773 : Nat := 118140960795 + 6024773 * 2 ^ 59
def prefixEnd_6024773 : Nat := 4983230072969 + 3 ^ 40 * 6024773 * 2
def baseEnd_6024773 : Nat := 1031201461076820593876693

theorem tailTrace_6024773 : CollatzResearch.WordTrace tailWord_6024773 prefixEnd_6024773 1031201461076820593876693 := by
  unfold tailWord_6024773
  simp only [CollatzResearch.WordTrace]
  refine ⟨219741523802283845154670973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146494349201522563436447315 219741523802283845154670973)
  ·
    refine ⟨82403071425856441933001615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219741523802283845154670973 82403071425856441933001615)
    ·
      refine ⟨123604607138784662899502423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82403071425856441933001615 123604607138784662899502423)
      ·
        refine ⟨185406910708176994349253635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123604607138784662899502423 185406910708176994349253635)
        ·
          refine ⟨278110366062265491523880453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185406910708176994349253635 278110366062265491523880453)
          ·
            refine ⟨52145693636674779660727585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278110366062265491523880453 52145693636674779660727585)
            ·
              refine ⟨39109270227506084745545689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52145693636674779660727585 39109270227506084745545689)
              ·
                refine ⟨29331952670629563559159267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39109270227506084745545689 29331952670629563559159267)
                ·
                  refine ⟨43997929005944345338738901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29331952670629563559159267 43997929005944345338738901)
                  ·
                    refine ⟨1031201461076820593876693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43997929005944345338738901 1031201461076820593876693)
                    ·
                      rfl

theorem cell23_6024773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_6024773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024773 prefixEnd_6024773 := by exact prefixLift 6024773
  have htrace : WordTrace (prefixWord ++ tailWord_6024773) baseStart_6024773 baseEnd_6024773 := by
    simpa [prefixWord, tailWord_6024773, baseEnd_6024773] using wordTrace_append hprefix tailTrace_6024773
  have hstable : (prefixWord ++ tailWord_6024773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024773).length < 2 ^ (prefixWord ++ tailWord_6024773).sum := by decide
  have hdescent : baseEnd_6024773 < baseStart_6024773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024823 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_6024823 : Nat := 118140960795 + 6024823 * 2 ^ 59
def prefixEnd_6024823 : Nat := 4983230072969 + 3 ^ 40 * 6024823 * 2
def baseEnd_6024823 : Nat := 3093630057263186586004849

theorem tailTrace_6024823 : CollatzResearch.WordTrace tailWord_6024823 prefixEnd_6024823 3093630057263186586004849 := by
  unfold tailWord_6024823
  simp only [CollatzResearch.WordTrace]
  refine ⟨219743347452102703693991123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146495564968068469129327415 219743347452102703693991123)
  ·
    refine ⟨329615021178154055540986685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219743347452102703693991123 329615021178154055540986685)
    ·
      refine ⟨123605632941807770827870007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329615021178154055540986685 123605632941807770827870007)
      ·
        refine ⟨185408449412711656241805011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123605632941807770827870007 185408449412711656241805011)
        ·
          refine ⟨278112674119067484362707517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185408449412711656241805011 278112674119067484362707517)
          ·
            refine ⟨104292252794650306636015319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278112674119067484362707517 104292252794650306636015319)
            ·
              refine ⟨156438379191975459954022979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104292252794650306636015319 156438379191975459954022979)
              ·
                refine ⟨234657568787963189931034469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156438379191975459954022979 234657568787963189931034469)
                ·
                  refine ⟨43998294147743098112068963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234657568787963189931034469 43998294147743098112068963)
                  ·
                    refine ⟨65997441221614647168103445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43998294147743098112068963 65997441221614647168103445)
                    ·
                      refine ⟨3093630057263186586004849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65997441221614647168103445 3093630057263186586004849)
                      ·
                        rfl

theorem cell23_6024823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_6024823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024823 prefixEnd_6024823 := by exact prefixLift 6024823
  have htrace : WordTrace (prefixWord ++ tailWord_6024823) baseStart_6024823 baseEnd_6024823 := by
    simpa [prefixWord, tailWord_6024823, baseEnd_6024823] using wordTrace_append hprefix tailTrace_6024823
  have hstable : (prefixWord ++ tailWord_6024823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024823).length < 2 ^ (prefixWord ++ tailWord_6024823).sum := by decide
  have hdescent : baseEnd_6024823 < baseStart_6024823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024904 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 2, 3, 2]
def baseStart_6024904 : Nat := 118140960795 + 6024904 * 2 ^ 59
def prefixEnd_6024904 : Nat := 4983230072969 + 3 ^ 40 * 6024904 * 2
def baseEnd_6024904 : Nat := 3093671649196200769091977

theorem tailTrace_6024904 : CollatzResearch.WordTrace tailWord_6024904 prefixEnd_6024904 3093671649196200769091977 := by
  unfold tailWord_6024904
  simp only [CollatzResearch.WordTrace]
  refine ⟨109873150882404627263844883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146497534509872836351793177 109873150882404627263844883)
  ·
    refine ⟨164809726323606940895767325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109873150882404627263844883 164809726323606940895767325)
    ·
      refine ⟨61803647371352602835912747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164809726323606940895767325 61803647371352602835912747)
      ·
        refine ⟨92705471057028904253869121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61803647371352602835912747 92705471057028904253869121)
        ·
          refine ⟨69529103292771678190401841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92705471057028904253869121 69529103292771678190401841)
          ·
            refine ⟨52146827469578758642801381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69529103292771678190401841 52146827469578758642801381)
            ·
              refine ⟨9777530150546017245525259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52146827469578758642801381 9777530150546017245525259)
              ·
                refine ⟨14666295225819025868287889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9777530150546017245525259 14666295225819025868287889)
                ·
                  refine ⟨10999721419364269401215917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14666295225819025868287889 10999721419364269401215917)
                  ·
                    refine ⟨4124895532261601025455969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10999721419364269401215917 4124895532261601025455969)
                    ·
                      refine ⟨3093671649196200769091977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124895532261601025455969 3093671649196200769091977)
                      ·
                        rfl

theorem cell23_6024904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_6024904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024904 prefixEnd_6024904 := by exact prefixLift 6024904
  have htrace : WordTrace (prefixWord ++ tailWord_6024904) baseStart_6024904 baseEnd_6024904 := by
    simpa [prefixWord, tailWord_6024904, baseEnd_6024904] using wordTrace_append hprefix tailTrace_6024904
  have hstable : (prefixWord ++ tailWord_6024904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024904).length < 2 ^ (prefixWord ++ tailWord_6024904).sum := by decide
  have hdescent : baseEnd_6024904 < baseStart_6024904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024940 : List Nat := [2, 2, 1, 1, 2, 2, 5, 8]
def baseStart_6024940 : Nat := 118140960795 + 6024940 * 2 ^ 59
def prefixEnd_6024940 : Nat := 4983230072969 + 3 ^ 40 * 6024940 * 2
def baseEnd_6024940 : Nat := 114581116092583801045993

theorem tailTrace_6024940 : CollatzResearch.WordTrace tailWord_6024940 prefixEnd_6024940 114581116092583801045993 := by
  unfold tailWord_6024940
  simp only [CollatzResearch.WordTrace]
  refine ⟨109873807396339416338000137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146498409861785888450666849 109873807396339416338000137)
  ·
    refine ⟨82405355547254562253500103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109873807396339416338000137 82405355547254562253500103)
    ·
      refine ⟨123608033320881843380250155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82405355547254562253500103 123608033320881843380250155)
      ·
        refine ⟨185412049981322765070375233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123608033320881843380250155 185412049981322765070375233)
        ·
          refine ⟨139059037485992073802781425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185412049981322765070375233 139059037485992073802781425)
          ·
            refine ⟨104294278114494055352086069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139059037485992073802781425 104294278114494055352086069)
            ·
              refine ⟨9777588573233817689258069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104294278114494055352086069 9777588573233817689258069)
              ·
                refine ⟨114581116092583801045993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9777588573233817689258069 114581116092583801045993)
                ·
                  rfl

theorem cell23_6024940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 8].length) (baseStart_6024940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024940 prefixEnd_6024940 := by exact prefixLift 6024940
  have htrace : WordTrace (prefixWord ++ tailWord_6024940) baseStart_6024940 baseEnd_6024940 := by
    simpa [prefixWord, tailWord_6024940, baseEnd_6024940] using wordTrace_append hprefix tailTrace_6024940
  have hstable : (prefixWord ++ tailWord_6024940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024940).length < 2 ^ (prefixWord ++ tailWord_6024940).sum := by decide
  have hdescent : baseEnd_6024940 < baseStart_6024940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024968 : List Nat := [2, 1, 3, 2, 2, 1, 4, 3, 1, 2, 2]
def baseStart_6024968 : Nat := 118140960795 + 6024968 * 2 ^ 59
def prefixEnd_6024968 : Nat := 4983230072969 + 3 ^ 40 * 6024968 * 2
def baseEnd_6024968 : Nat := 3093704511958088518691683

theorem tailTrace_6024968 : CollatzResearch.WordTrace tailWord_6024968 prefixEnd_6024968 3093704511958088518691683 := by
  unfold tailWord_6024968
  simp only [CollatzResearch.WordTrace]
  refine ⟨109874318018288696729009779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146499090691051595638679705 109874318018288696729009779)
  ·
    refine ⟨164811477027433045093514669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109874318018288696729009779 164811477027433045093514669)
    ·
      refine ⟨61804303885287391910068001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164811477027433045093514669 61804303885287391910068001)
      ·
        refine ⟨46353227913965543932551001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61804303885287391910068001 46353227913965543932551001)
        ·
          refine ⟨34764920935474157949413251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46353227913965543932551001 34764920935474157949413251)
          ·
            refine ⟨52147381403211236924119877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34764920935474157949413251 52147381403211236924119877)
            ·
              refine ⟨9777634013102106923272477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52147381403211236924119877 9777634013102106923272477)
              ·
                refine ⟨3666612754913290096227179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9777634013102106923272477 3666612754913290096227179)
                ·
                  refine ⟨5499919132369935144340769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666612754913290096227179 5499919132369935144340769)
                  ·
                    refine ⟨4124939349277451358255577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5499919132369935144340769 4124939349277451358255577)
                    ·
                      refine ⟨3093704511958088518691683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124939349277451358255577 3093704511958088518691683)
                      ·
                        rfl

theorem cell23_6024968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_6024968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024968 prefixEnd_6024968 := by exact prefixLift 6024968
  have htrace : WordTrace (prefixWord ++ tailWord_6024968) baseStart_6024968 baseEnd_6024968 := by
    simpa [prefixWord, tailWord_6024968, baseEnd_6024968] using wordTrace_append hprefix tailTrace_6024968
  have hstable : (prefixWord ++ tailWord_6024968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024968).length < 2 ^ (prefixWord ++ tailWord_6024968).sum := by decide
  have hdescent : baseEnd_6024968 < baseStart_6024968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6024978 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_6024978 : Nat := 118140960795 + 6024978 * 2 ^ 59
def prefixEnd_6024978 : Nat := 4983230072969 + 3 ^ 40 * 6024978 * 2
def baseEnd_6024978 : Nat := 1031236548921544493188879

theorem tailTrace_6024978 : CollatzResearch.WordTrace tailWord_6024978 prefixEnd_6024978 1031236548921544493188879 := by
  unfold tailWord_6024978
  simp only [CollatzResearch.WordTrace]
  refine ⟨54937250191635291291470897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146499333844360776777255725 54937250191635291291470897)
  ·
    refine ⟨41202937643726468468603173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54937250191635291291470897 41202937643726468468603173)
    ·
      refine ⟨7725550808198712837863095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41202937643726468468603173 7725550808198712837863095)
      ·
        refine ⟨11588326212298069256794643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7725550808198712837863095 11588326212298069256794643)
        ·
          refine ⟨17382489318447103885191965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11588326212298069256794643 17382489318447103885191965)
          ·
            refine ⟨6518433494417663956946987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17382489318447103885191965 6518433494417663956946987)
            ·
              refine ⟨9777650241626495935420481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6518433494417663956946987 9777650241626495935420481)
              ·
                refine ⟨7333237681219871951565361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9777650241626495935420481 7333237681219871951565361)
                ·
                  refine ⟨5499928260914903963674021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7333237681219871951565361 5499928260914903963674021)
                  ·
                    refine ⟨1031236548921544493188879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5499928260914903963674021 1031236548921544493188879)
                    ·
                      rfl

theorem cell23_6024978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_6024978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6024978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6024978 prefixEnd_6024978 := by exact prefixLift 6024978
  have htrace : WordTrace (prefixWord ++ tailWord_6024978) baseStart_6024978 baseEnd_6024978 := by
    simpa [prefixWord, tailWord_6024978, baseEnd_6024978] using wordTrace_append hprefix tailTrace_6024978
  have hstable : (prefixWord ++ tailWord_6024978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6024978).length < 2 ^ (prefixWord ++ tailWord_6024978).sum := by decide
  have hdescent : baseEnd_6024978 < baseStart_6024978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6024978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025014 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6025014 : Nat := 118140960795 + 6025014 * 2 ^ 59
def prefixEnd_6025014 : Nat := 4983230072969 + 3 ^ 40 * 6025014 * 2
def baseEnd_6025014 : Nat := 3093728132068195338716471

theorem tailTrace_6025014 : CollatzResearch.WordTrace tailWord_6025014 prefixEnd_6025014 3093728132068195338716471 := by
  unfold tailWord_6025014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13734394612150671457137131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146500209196273828876129397 13734394612150671457137131)
  ·
    refine ⟨20601591918226007185705697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13734394612150671457137131 20601591918226007185705697)
    ·
      refine ⟨15451193938669505389279273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20601591918226007185705697 15451193938669505389279273)
      ·
        refine ⟨11588395454002129041959455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15451193938669505389279273 11588395454002129041959455)
        ·
          refine ⟨17382593181003193562939183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11588395454002129041959455 17382593181003193562939183)
          ·
            refine ⟨26073889771504790344408775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17382593181003193562939183 26073889771504790344408775)
            ·
              refine ⟨39110834657257185516613163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26073889771504790344408775 39110834657257185516613163)
              ·
                refine ⟨58666251985885778274919745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39110834657257185516613163 58666251985885778274919745)
                ·
                  refine ⟨43999688989414333706189809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58666251985885778274919745 43999688989414333706189809)
                  ·
                    refine ⟨32999766742060750279642357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43999688989414333706189809 32999766742060750279642357)
                    ·
                      refine ⟨3093728132068195338716471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32999766742060750279642357 3093728132068195338716471)
                      ·
                        rfl

theorem cell23_6025014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6025014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025014 prefixEnd_6025014 := by exact prefixLift 6025014
  have htrace : WordTrace (prefixWord ++ tailWord_6025014) baseStart_6025014 baseEnd_6025014 := by
    simpa [prefixWord, tailWord_6025014, baseEnd_6025014] using wordTrace_append hprefix tailTrace_6025014
  have hstable : (prefixWord ++ tailWord_6025014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025014).length < 2 ^ (prefixWord ++ tailWord_6025014).sum := by decide
  have hdescent : baseEnd_6025014 < baseStart_6025014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025027 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 5]
def baseStart_6025027 : Nat := 118140960795 + 6025027 * 2 ^ 59
def prefixEnd_6025027 : Nat := 4983230072969 + 3 ^ 40 * 6025027 * 2
def baseEnd_6025027 : Nat := 3093734807316703787853911

theorem tailTrace_6025027 : CollatzResearch.WordTrace tailWord_6025027 prefixEnd_6025027 3093734807316703787853911 := by
  unfold tailWord_6025027
  simp only [CollatzResearch.WordTrace]
  refine ⟨219750787943363646534417335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146500525295575764356278223 219750787943363646534417335)
  ·
    refine ⟨329626181915045469801626003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219750787943363646534417335 329626181915045469801626003)
    ·
      refine ⟨494439272872568204702439005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329626181915045469801626003 494439272872568204702439005)
      ·
        refine ⟨185414727327213076763414627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494439272872568204702439005 185414727327213076763414627)
        ·
          refine ⟨278122090990819615145121941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185414727327213076763414627 278122090990819615145121941)
          ·
            refine ⟨13036973015194669459927591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 278122090990819615145121941 13036973015194669459927591)
            ·
              refine ⟨19555459522792004189891387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13036973015194669459927591 19555459522792004189891387)
              ·
                refine ⟨29333189284188006284837081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19555459522792004189891387 29333189284188006284837081)
                ·
                  refine ⟨21999891963141004713627811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29333189284188006284837081 21999891963141004713627811)
                  ·
                    refine ⟨32999837944711507070441717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21999891963141004713627811 32999837944711507070441717)
                    ·
                      refine ⟨3093734807316703787853911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32999837944711507070441717 3093734807316703787853911)
                      ·
                        rfl

theorem cell23_6025027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_6025027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025027 prefixEnd_6025027 := by exact prefixLift 6025027
  have htrace : WordTrace (prefixWord ++ tailWord_6025027) baseStart_6025027 baseEnd_6025027 := by
    simpa [prefixWord, tailWord_6025027, baseEnd_6025027] using wordTrace_append hprefix tailTrace_6025027
  have hstable : (prefixWord ++ tailWord_6025027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025027).length < 2 ^ (prefixWord ++ tailWord_6025027).sum := by decide
  have hdescent : baseEnd_6025027 < baseStart_6025027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025040 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_6025040 : Nat := 118140960795 + 6025040 * 2 ^ 59
def prefixEnd_6025040 : Nat := 4983230072969 + 3 ^ 40 * 6025040 * 2
def baseEnd_6025040 : Nat := 3093741482565212236991351

theorem tailTrace_6025040 : CollatzResearch.WordTrace tailWord_6025040 prefixEnd_6025040 3093741482565212236991351 := by
  unfold tailWord_6025040
  simp only [CollatzResearch.WordTrace]
  refine ⟨109875631046158274877320287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146500841394877699836427049 109875631046158274877320287)
  ·
    refine ⟨164813446569237412315980431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109875631046158274877320287 164813446569237412315980431)
    ·
      refine ⟨247220169853856118473970647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164813446569237412315980431 247220169853856118473970647)
      ·
        refine ⟨370830254780784177710955971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247220169853856118473970647 370830254780784177710955971)
        ·
          refine ⟨556245382171176266566433957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370830254780784177710955971 556245382171176266566433957)
          ·
            refine ⟨104296009157095549981206367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 556245382171176266566433957 104296009157095549981206367)
            ·
              refine ⟨156444013735643324971809551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104296009157095549981206367 156444013735643324971809551)
              ·
                refine ⟨234666020603464987457714327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156444013735643324971809551 234666020603464987457714327)
                ·
                  refine ⟨351999030905197481186571491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234666020603464987457714327 351999030905197481186571491)
                  ·
                    refine ⟨527998546357796221779857237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 351999030905197481186571491 527998546357796221779857237)
                    ·
                      refine ⟨3093741482565212236991351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 527998546357796221779857237 3093741482565212236991351)
                      ·
                        rfl

theorem cell23_6025040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_6025040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025040 prefixEnd_6025040 := by exact prefixLift 6025040
  have htrace : WordTrace (prefixWord ++ tailWord_6025040) baseStart_6025040 baseEnd_6025040 := by
    simpa [prefixWord, tailWord_6025040, baseEnd_6025040] using wordTrace_append hprefix tailTrace_6025040
  have hstable : (prefixWord ++ tailWord_6025040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025040).length < 2 ^ (prefixWord ++ tailWord_6025040).sum := by decide
  have hdescent : baseEnd_6025040 < baseStart_6025040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025041 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 4, 2, 2]
def baseStart_6025041 : Nat := 118140960795 + 6025041 * 2 ^ 59
def prefixEnd_6025041 : Nat := 4983230072969 + 3 ^ 40 * 6025041 * 2
def baseEnd_6025041 : Nat := 3093741996045866733078847

theorem tailTrace_6025041 : CollatzResearch.WordTrace tailWord_6025041 prefixEnd_6025041 3093741996045866733078847 := by
  unfold tailWord_6025041
  simp only [CollatzResearch.WordTrace]
  refine ⟨219751298565312926925426977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146500865710208617950284651 219751298565312926925426977)
  ·
    refine ⟨164813473923984695194070233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219751298565312926925426977 164813473923984695194070233)
    ·
      refine ⟨123610105442988521395552675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164813473923984695194070233 123610105442988521395552675)
      ·
        refine ⟨185415158164482782093329013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123610105442988521395552675 185415158164482782093329013)
        ·
          refine ⟨17382671077920260821249595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185415158164482782093329013 17382671077920260821249595)
          ·
            refine ⟨26074006616880391231874393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17382671077920260821249595 26074006616880391231874393)
            ·
              refine ⟨19555504962660293423905795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26074006616880391231874393 19555504962660293423905795)
              ·
                refine ⟨29333257443990440135858693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19555504962660293423905795 29333257443990440135858693)
                ·
                  refine ⟨5499985770748207525473505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29333257443990440135858693 5499985770748207525473505)
                  ·
                    refine ⟨4124989328061155644105129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5499985770748207525473505 4124989328061155644105129)
                    ·
                      refine ⟨3093741996045866733078847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4124989328061155644105129 3093741996045866733078847)
                      ·
                        rfl

theorem cell23_6025041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_6025041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025041 prefixEnd_6025041 := by exact prefixLift 6025041
  have htrace : WordTrace (prefixWord ++ tailWord_6025041) baseStart_6025041 baseEnd_6025041 := by
    simpa [prefixWord, tailWord_6025041, baseEnd_6025041] using wordTrace_append hprefix tailTrace_6025041
  have hstable : (prefixWord ++ tailWord_6025041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025041).length < 2 ^ (prefixWord ++ tailWord_6025041).sum := by decide
  have hdescent : baseEnd_6025041 < baseStart_6025041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025052 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_6025052 : Nat := 118140960795 + 6025052 * 2 ^ 59
def prefixEnd_6025052 : Nat := 4983230072969 + 3 ^ 40 * 6025052 * 2
def baseEnd_6025052 : Nat := 3093747644333066190041297

theorem tailTrace_6025052 : CollatzResearch.WordTrace tailWord_6025052 prefixEnd_6025052 3093747644333066190041297 := by
  unfold tailWord_6025052
  simp only [CollatzResearch.WordTrace]
  refine ⟨109875849884136537902038705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146501133178848717202718273 109875849884136537902038705)
  ·
    refine ⟨82406887413102403426529029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109875849884136537902038705 82406887413102403426529029)
    ·
      refine ⟨15451291389956700642474193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82406887413102403426529029 15451291389956700642474193)
      ·
        refine ⟨11588468542467525481855645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15451291389956700642474193 11588468542467525481855645)
        ·
          refine ⟨4345675703425322055695867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11588468542467525481855645 4345675703425322055695867)
          ·
            refine ⟨6518513555137983083543801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345675703425322055695867 6518513555137983083543801)
            ·
              refine ⟨4888885166353487312657851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6518513555137983083543801 4888885166353487312657851)
              ·
                refine ⟨7333327749530230968986777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888885166353487312657851 7333327749530230968986777)
                ·
                  refine ⟨5499995812147673226740083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7333327749530230968986777 5499995812147673226740083)
                  ·
                    refine ⟨8249993718221509840110125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5499995812147673226740083 8249993718221509840110125)
                    ·
                      refine ⟨3093747644333066190041297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8249993718221509840110125 3093747644333066190041297)
                      ·
                        rfl

theorem cell23_6025052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_6025052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025052 prefixEnd_6025052 := by exact prefixLift 6025052
  have htrace : WordTrace (prefixWord ++ tailWord_6025052) baseStart_6025052 baseEnd_6025052 := by
    simpa [prefixWord, tailWord_6025052, baseEnd_6025052] using wordTrace_append hprefix tailTrace_6025052
  have hstable : (prefixWord ++ tailWord_6025052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025052).length < 2 ^ (prefixWord ++ tailWord_6025052).sum := by decide
  have hdescent : baseEnd_6025052 < baseStart_6025052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025057 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_6025057 : Nat := 118140960795 + 6025057 * 2 ^ 59
def prefixEnd_6025057 : Nat := 4983230072969 + 3 ^ 40 * 6025057 * 2
def baseEnd_6025057 : Nat := 3093750211736338670478773

theorem tailTrace_6025057 : CollatzResearch.WordTrace tailWord_6025057 prefixEnd_6025057 3093750211736338670478773 := by
  unfold tailWord_6025057
  simp only [CollatzResearch.WordTrace]
  refine ⟨219751882133254961658009425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146501254755503307772006283 219751882133254961658009425)
  ·
    refine ⟨164813911599941221243507069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219751882133254961658009425 164813911599941221243507069)
    ·
      refine ⟨61805216849977957966315151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164813911599941221243507069 61805216849977957966315151)
      ·
        refine ⟨92707825274966936949472727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61805216849977957966315151 92707825274966936949472727)
        ·
          refine ⟨139061737912450405424209091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92707825274966936949472727 139061737912450405424209091)
          ·
            refine ⟨208592606868675608136313637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139061737912450405424209091 208592606868675608136313637)
            ·
              refine ⟨39111113787876676525558807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208592606868675608136313637 39111113787876676525558807)
              ·
                refine ⟨58666670681815014788338211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39111113787876676525558807 58666670681815014788338211)
                ·
                  refine ⟨88000006022722522182507317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58666670681815014788338211 88000006022722522182507317)
                  ·
                    refine ⟨8250000564630236454610061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88000006022722522182507317 8250000564630236454610061)
                    ·
                      refine ⟨3093750211736338670478773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8250000564630236454610061 3093750211736338670478773)
                      ·
                        rfl

theorem cell23_6025057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_6025057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025057 prefixEnd_6025057 := by exact prefixLift 6025057
  have htrace : WordTrace (prefixWord ++ tailWord_6025057) baseStart_6025057 baseEnd_6025057 := by
    simpa [prefixWord, tailWord_6025057, baseEnd_6025057] using wordTrace_append hprefix tailTrace_6025057
  have hstable : (prefixWord ++ tailWord_6025057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025057).length < 2 ^ (prefixWord ++ tailWord_6025057).sum := by decide
  have hdescent : baseEnd_6025057 < baseStart_6025057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025124 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_6025124 : Nat := 118140960795 + 6025124 * 2 ^ 59
def prefixEnd_6025124 : Nat := 4983230072969 + 3 ^ 40 * 6025124 * 2
def baseEnd_6025124 : Nat := 1031261538313396636113655

theorem tailTrace_6025124 : CollatzResearch.WordTrace tailWord_6025124 prefixEnd_6025124 1031261538313396636113655 := by
  unfold tailWord_6025124
  simp only [CollatzResearch.WordTrace]
  refine ⟨109877162912006116050349213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146502883882674821400465617 109877162912006116050349213)
  ·
    refine ⟨41203936092002293518880955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109877162912006116050349213 41203936092002293518880955)
    ·
      refine ⟨61805904138003440278321433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41203936092002293518880955 61805904138003440278321433)
      ·
        refine ⟨46354428103502580208741075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61805904138003440278321433 46354428103502580208741075)
        ·
          refine ⟨69531642155253870313111613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46354428103502580208741075 69531642155253870313111613)
          ·
            refine ⟨26074365808220201367416855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69531642155253870313111613 26074365808220201367416855)
            ·
              refine ⟨39111548712330302051125283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26074365808220201367416855 39111548712330302051125283)
              ·
                refine ⟨58667323068495453076687925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39111548712330302051125283 58667323068495453076687925)
                ·
                  refine ⟨5500061537671448725939493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58667323068495453076687925 5500061537671448725939493)
                  ·
                    refine ⟨1031261538313396636113655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5500061537671448725939493 1031261538313396636113655)
                    ·
                      rfl

theorem cell23_6025124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_6025124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025124 prefixEnd_6025124 := by exact prefixLift 6025124
  have htrace : WordTrace (prefixWord ++ tailWord_6025124) baseStart_6025124 baseEnd_6025124 := by
    simpa [prefixWord, tailWord_6025124, baseEnd_6025124] using wordTrace_append hprefix tailTrace_6025124
  have hstable : (prefixWord ++ tailWord_6025124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025124).length < 2 ^ (prefixWord ++ tailWord_6025124).sum := by decide
  have hdescent : baseEnd_6025124 < baseStart_6025124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025222 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_6025222 : Nat := 118140960795 + 6025222 * 2 ^ 59
def prefixEnd_6025222 : Nat := 4983230072969 + 3 ^ 40 * 6025222 * 2
def baseEnd_6025222 : Nat := 343759437338258947212835

theorem tailTrace_6025222 : CollatzResearch.WordTrace tailWord_6025222 prefixEnd_6025222 343759437338258947212835 := by
  unfold tailWord_6025222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6867434380551787338680185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146505266785104796558510613 6867434380551787338680185)
  ·
    refine ⟨5150575785413840504010139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6867434380551787338680185 5150575785413840504010139)
    ·
      refine ⟨7725863678120760756015209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5150575785413840504010139 7725863678120760756015209)
      ·
        refine ⟨5794397758590570567011407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7725863678120760756015209 5794397758590570567011407)
        ·
          refine ⟨8691596637885855850517111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5794397758590570567011407 8691596637885855850517111)
          ·
            refine ⟨13037394956828783775775667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8691596637885855850517111 13037394956828783775775667)
            ·
              refine ⟨19556092435243175663663501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13037394956828783775775667 19556092435243175663663501)
              ·
                refine ⟨7333534663216190873873813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19556092435243175663663501 7333534663216190873873813)
                ·
                  refine ⟨343759437338258947212835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7333534663216190873873813 343759437338258947212835)
                  ·
                    rfl

theorem cell23_6025222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_6025222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025222 prefixEnd_6025222 := by exact prefixLift 6025222
  have htrace : WordTrace (prefixWord ++ tailWord_6025222) baseStart_6025222 baseEnd_6025222 := by
    simpa [prefixWord, tailWord_6025222, baseEnd_6025222] using wordTrace_append hprefix tailTrace_6025222
  have hstable : (prefixWord ++ tailWord_6025222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025222).length < 2 ^ (prefixWord ++ tailWord_6025222).sum := by decide
  have hdescent : baseEnd_6025222 < baseStart_6025222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025224 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_6025224 : Nat := 118140960795 + 6025224 * 2 ^ 59
def prefixEnd_6025224 : Nat := 4983230072969 + 3 ^ 40 * 6025224 * 2
def baseEnd_6025224 : Nat := 3093835963005639517090505

theorem tailTrace_6025224 : CollatzResearch.WordTrace tailWord_6025224 prefixEnd_6025224 3093835963005639517090505 := by
  unfold tailWord_6025224
  simp only [CollatzResearch.WordTrace]
  refine ⟨109878986561824974589669363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146505315415766632786225817 109878986561824974589669363)
  ·
    refine ⟨164818479842737461884504045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109878986561824974589669363 164818479842737461884504045)
    ·
      refine ⟨61806929941026548206689017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164818479842737461884504045 61806929941026548206689017)
      ·
        refine ⟨46355197455769911155016763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61806929941026548206689017 46355197455769911155016763)
        ·
          refine ⟨69532796183654866732525145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46355197455769911155016763 69532796183654866732525145)
          ·
            refine ⟨52149597137741150049393859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69532796183654866732525145 52149597137741150049393859)
            ·
              refine ⟨78224395706611725074090789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52149597137741150049393859 78224395706611725074090789)
              ·
                refine ⟨14667074194989698451392023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78224395706611725074090789 14667074194989698451392023)
                ·
                  refine ⟨22000611292484547677088035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14667074194989698451392023 22000611292484547677088035)
                  ·
                    refine ⟨33000916938726821515632053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22000611292484547677088035 33000916938726821515632053)
                    ·
                      refine ⟨3093835963005639517090505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33000916938726821515632053 3093835963005639517090505)
                      ·
                        rfl

theorem cell23_6025224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_6025224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025224 prefixEnd_6025224 := by exact prefixLift 6025224
  have htrace : WordTrace (prefixWord ++ tailWord_6025224) baseStart_6025224 baseEnd_6025224 := by
    simpa [prefixWord, tailWord_6025224, baseEnd_6025224] using wordTrace_append hprefix tailTrace_6025224
  have hstable : (prefixWord ++ tailWord_6025224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025224).length < 2 ^ (prefixWord ++ tailWord_6025224).sum := by decide
  have hdescent : baseEnd_6025224 < baseStart_6025224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025244 : List Nat := [2, 2, 3, 1, 3, 1, 2, 9]
def baseStart_6025244 : Nat := 118140960795 + 6025244 * 2 ^ 59
def prefixEnd_6025244 : Nat := 4983230072969 + 3 ^ 40 * 6025244 * 2
def baseEnd_6025244 : Nat := 114586897504397386623719

theorem tailTrace_6025244 : CollatzResearch.WordTrace tailWord_6025244 prefixEnd_6025244 114586897504397386623719 := by
  unfold tailWord_6025244
  simp only [CollatzResearch.WordTrace]
  refine ⟨109879351291788746297533393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146505801722384995063377857 109879351291788746297533393)
  ·
    refine ⟨82409513468841559723150045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109879351291788746297533393 82409513468841559723150045)
    ·
      refine ⟨30903567550815584896181267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82409513468841559723150045 30903567550815584896181267)
      ·
        refine ⟨46355351326223377344271901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30903567550815584896181267 46355351326223377344271901)
        ·
          refine ⟨17383256747333766504101963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46355351326223377344271901 17383256747333766504101963)
          ·
            refine ⟨26074885121000649756152945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17383256747333766504101963 26074885121000649756152945)
            ·
              refine ⟨19556163840750487317114709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26074885121000649756152945 19556163840750487317114709)
              ·
                refine ⟨114586897504397386623719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19556163840750487317114709 114586897504397386623719)
                ·
                  rfl

theorem cell23_6025244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 9].length) (baseStart_6025244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025244 prefixEnd_6025244 := by exact prefixLift 6025244
  have htrace : WordTrace (prefixWord ++ tailWord_6025244) baseStart_6025244 baseEnd_6025244 := by
    simpa [prefixWord, tailWord_6025244, baseEnd_6025244] using wordTrace_append hprefix tailTrace_6025244
  have hstable : (prefixWord ++ tailWord_6025244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025244).length < 2 ^ (prefixWord ++ tailWord_6025244).sum := by decide
  have hdescent : baseEnd_6025244 < baseStart_6025244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025258 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_6025258 : Nat := 118140960795 + 6025258 * 2 ^ 59
def prefixEnd_6025258 : Nat := 4983230072969 + 3 ^ 40 * 6025258 * 2
def baseEnd_6025258 : Nat := 3093853421347892384065349

theorem tailTrace_6025258 : CollatzResearch.WordTrace tailWord_6025258 prefixEnd_6025258 3093853421347892384065349 := by
  unfold tailWord_6025258
  simp only [CollatzResearch.WordTrace]
  refine ⟨54939803301381693246519107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146506142137017848657384285 54939803301381693246519107)
  ·
    refine ⟨82409704952072539869778661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54939803301381693246519107 82409704952072539869778661)
    ·
      refine ⟨15451819678513601225583499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82409704952072539869778661 15451819678513601225583499)
      ·
        refine ⟨23177729517770401838375249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15451819678513601225583499 23177729517770401838375249)
        ·
          refine ⟨17383297138327801378781437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23177729517770401838375249 17383297138327801378781437)
          ·
            refine ⟨6518736426872925517043039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17383297138327801378781437 6518736426872925517043039)
            ·
              refine ⟨9778104640309388275564559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6518736426872925517043039 9778104640309388275564559)
              ·
                refine ⟨14667156960464082413346839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9778104640309388275564559 14667156960464082413346839)
                ·
                  refine ⟨22000735440696123620020259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14667156960464082413346839 22000735440696123620020259)
                  ·
                    refine ⟨33001103161044185430030389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22000735440696123620020259 33001103161044185430030389)
                    ·
                      refine ⟨3093853421347892384065349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33001103161044185430030389 3093853421347892384065349)
                      ·
                        rfl

theorem cell23_6025258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_6025258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025258 prefixEnd_6025258 := by exact prefixLift 6025258
  have htrace : WordTrace (prefixWord ++ tailWord_6025258) baseStart_6025258 baseEnd_6025258 := by
    simpa [prefixWord, tailWord_6025258, baseEnd_6025258] using wordTrace_append hprefix tailTrace_6025258
  have hstable : (prefixWord ++ tailWord_6025258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025258).length < 2 ^ (prefixWord ++ tailWord_6025258).sum := by decide
  have hdescent : baseEnd_6025258 < baseStart_6025258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025271 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 4, 1, 3]
def baseStart_6025271 : Nat := 118140960795 + 6025271 * 2 ^ 59
def prefixEnd_6025271 : Nat := 4983230072969 + 3 ^ 40 * 6025271 * 2
def baseEnd_6025271 : Nat := 3093860096596400833202789

theorem tailTrace_6025271 : CollatzResearch.WordTrace tailWord_6025271 prefixEnd_6025271 3093860096596400833202789 := by
  unfold tailWord_6025271
  simp only [CollatzResearch.WordTrace]
  refine ⟨219759687354479676206299667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146506458236319784137533111 219759687354479676206299667)
  ·
    refine ⟨329639531031719514309449501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219759687354479676206299667 329639531031719514309449501)
    ·
      refine ⟨123614824136894817866043563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329639531031719514309449501 123614824136894817866043563)
      ·
        refine ⟨185422236205342226799065345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123614824136894817866043563 185422236205342226799065345)
        ·
          refine ⟨139066677154006670099299009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185422236205342226799065345 139066677154006670099299009)
          ·
            refine ⟨104300007865505002574474257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139066677154006670099299009 104300007865505002574474257)
            ·
              refine ⟨78225005899128751930855693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104300007865505002574474257 78225005899128751930855693)
              ·
                refine ⟨29334377212173281974070885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78225005899128751930855693 29334377212173281974070885)
                ·
                  refine ⟨5500195727282490370138291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29334377212173281974070885 5500195727282490370138291)
                  ·
                    refine ⟨8250293590923735555207437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5500195727282490370138291 8250293590923735555207437)
                    ·
                      refine ⟨3093860096596400833202789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8250293590923735555207437 3093860096596400833202789)
                      ·
                        rfl

theorem cell23_6025271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_6025271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025271 prefixEnd_6025271 := by exact prefixLift 6025271
  have htrace : WordTrace (prefixWord ++ tailWord_6025271) baseStart_6025271 baseEnd_6025271 := by
    simpa [prefixWord, tailWord_6025271, baseEnd_6025271] using wordTrace_append hprefix tailTrace_6025271
  have hstable : (prefixWord ++ tailWord_6025271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025271).length < 2 ^ (prefixWord ++ tailWord_6025271).sum := by decide
  have hdescent : baseEnd_6025271 < baseStart_6025271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025272 : List Nat := [2, 1, 2, 1, 6, 1, 1, 4, 1, 2, 2]
def baseStart_6025272 : Nat := 118140960795 + 6025272 * 2 ^ 59
def prefixEnd_6025272 : Nat := 4983230072969 + 3 ^ 40 * 6025272 * 2
def baseEnd_6025272 : Nat := 3093860610077055329290285

theorem tailTrace_6025272 : CollatzResearch.WordTrace tailWord_6025272 prefixEnd_6025272 3093860610077055329290285 := by
  unfold tailWord_6025272
  simp only [CollatzResearch.WordTrace]
  refine ⟨109879861913738026688543035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146506482551650702251390713 109879861913738026688543035)
  ·
    refine ⟨164819792870607040032814553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109879861913738026688543035 164819792870607040032814553)
    ·
      refine ⟨123614844652955280024610915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164819792870607040032814553 123614844652955280024610915)
      ·
        refine ⟨185422266979432920036916373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123614844652955280024610915 185422266979432920036916373)
        ·
          refine ⟨8691668764660918126730455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185422266979432920036916373 8691668764660918126730455)
          ·
            refine ⟨13037503146991377190095683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8691668764660918126730455 13037503146991377190095683)
            ·
              refine ⟨19556254720487065785143525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13037503146991377190095683 19556254720487065785143525)
              ·
                refine ⟨3666797760091324834714411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19556254720487065785143525 3666797760091324834714411)
                ·
                  refine ⟨5500196640136987252071617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666797760091324834714411 5500196640136987252071617)
                  ·
                    refine ⟨4125147480102740439053713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5500196640136987252071617 4125147480102740439053713)
                    ·
                      refine ⟨3093860610077055329290285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125147480102740439053713 3093860610077055329290285)
                      ·
                        rfl

theorem cell23_6025272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 1, 2, 2].length) (baseStart_6025272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025272 prefixEnd_6025272 := by exact prefixLift 6025272
  have htrace : WordTrace (prefixWord ++ tailWord_6025272) baseStart_6025272 baseEnd_6025272 := by
    simpa [prefixWord, tailWord_6025272, baseEnd_6025272] using wordTrace_append hprefix tailTrace_6025272
  have hstable : (prefixWord ++ tailWord_6025272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025272).length < 2 ^ (prefixWord ++ tailWord_6025272).sum := by decide
  have hdescent : baseEnd_6025272 < baseStart_6025272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025278 : List Nat := [4, 2, 1, 3, 2, 2, 1, 8]
def baseStart_6025278 : Nat := 118140960795 + 6025278 * 2 ^ 59
def prefixEnd_6025278 : Nat := 4983230072969 + 3 ^ 40 * 6025278 * 2
def baseEnd_6025278 : Nat := 114587544109666011326491

theorem tailTrace_6025278 : CollatzResearch.WordTrace tailWord_6025278 prefixEnd_6025278 114587544109666011326491 := by
  unfold tailWord_6025278
  simp only [CollatzResearch.WordTrace]
  refine ⟨27469992833181789550225561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146506628443636210934536325 27469992833181789550225561)
  ·
    refine ⟨20602494624886342162669171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27469992833181789550225561 20602494624886342162669171)
    ·
      refine ⟨30903741937329513244003757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20602494624886342162669171 30903741937329513244003757)
      ·
        refine ⟨11588903226498567466501409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30903741937329513244003757 11588903226498567466501409)
        ·
          refine ⟨8691677419873925599876057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11588903226498567466501409 8691677419873925599876057)
          ·
            refine ⟨6518758064905444199907043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8691677419873925599876057 6518758064905444199907043)
            ·
              refine ⟨9778137097358166299860565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6518758064905444199907043 9778137097358166299860565)
              ·
                refine ⟨114587544109666011326491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9778137097358166299860565 114587544109666011326491)
                ·
                  rfl

theorem cell23_6025278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_6025278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025278 prefixEnd_6025278 := by exact prefixLift 6025278
  have htrace : WordTrace (prefixWord ++ tailWord_6025278) baseStart_6025278 baseEnd_6025278 := by
    simpa [prefixWord, tailWord_6025278, baseEnd_6025278] using wordTrace_append hprefix tailTrace_6025278
  have hstable : (prefixWord ++ tailWord_6025278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025278).length < 2 ^ (prefixWord ++ tailWord_6025278).sum := by decide
  have hdescent : baseEnd_6025278 < baseStart_6025278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025311 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 3, 4, 2]
def baseStart_6025311 : Nat := 118140960795 + 6025311 * 2 ^ 59
def prefixEnd_6025311 : Nat := 4983230072969 + 3 ^ 40 * 6025311 * 2
def baseEnd_6025311 : Nat := 3093880635822580676702605

theorem tailTrace_6025311 : CollatzResearch.WordTrace tailWord_6025311 prefixEnd_6025311 3093880635822580676702605 := by
  unfold tailWord_6025311
  simp only [CollatzResearch.WordTrace]
  refine ⟨219761146274334763037755787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146507430849556508691837191 219761146274334763037755787)
  ·
    refine ⟨329641719411502144556633681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219761146274334763037755787 329641719411502144556633681)
    ·
      refine ⟨247231289558626608417475261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329641719411502144556633681 247231289558626608417475261)
      ·
        refine ⟨92711733584484978156553223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247231289558626608417475261 92711733584484978156553223)
        ·
          refine ⟨139067600376727467234829835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92711733584484978156553223 139067600376727467234829835)
          ·
            refine ⟨208601400565091200852244753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139067600376727467234829835 208601400565091200852244753)
            ·
              refine ⟨156451050423818400639183565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208601400565091200852244753 156451050423818400639183565)
              ·
                refine ⟨58669143908931900239693837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156451050423818400639183565 58669143908931900239693837)
                ·
                  refine ⟨22000928965849462589885189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58669143908931900239693837 22000928965849462589885189)
                  ·
                    refine ⟨4125174181096774235603473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22000928965849462589885189 4125174181096774235603473)
                    ·
                      refine ⟨3093880635822580676702605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125174181096774235603473 3093880635822580676702605)
                      ·
                        rfl

theorem cell23_6025311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_6025311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025311 prefixEnd_6025311 := by exact prefixLift 6025311
  have htrace : WordTrace (prefixWord ++ tailWord_6025311) baseStart_6025311 baseEnd_6025311 := by
    simpa [prefixWord, tailWord_6025311, baseEnd_6025311] using wordTrace_append hprefix tailTrace_6025311
  have hstable : (prefixWord ++ tailWord_6025311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025311).length < 2 ^ (prefixWord ++ tailWord_6025311).sum := by decide
  have hdescent : baseEnd_6025311 < baseStart_6025311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025315 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 1, 3, 2]
def baseStart_6025315 : Nat := 118140960795 + 6025315 * 2 ^ 59
def prefixEnd_6025315 : Nat := 4983230072969 + 3 ^ 40 * 6025315 * 2
def baseEnd_6025315 : Nat := 3093882689745198661052587

theorem tailTrace_6025315 : CollatzResearch.WordTrace tailWord_6025315 prefixEnd_6025315 3093882689745198661052587 := by
  unfold tailWord_6025315
  simp only [CollatzResearch.WordTrace]
  refine ⟨219761292166320271720901399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146507528110880181147267599 219761292166320271720901399)
  ·
    refine ⟨329641938249480407581352099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219761292166320271720901399 329641938249480407581352099)
    ·
      refine ⟨494462907374220611372028149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329641938249480407581352099 494462907374220611372028149)
      ·
        refine ⟨46355897566333182316127639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 494462907374220611372028149 46355897566333182316127639)
        ·
          refine ⟨69533846349499773474191459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46355897566333182316127639 69533846349499773474191459)
          ·
            refine ⟨104300769524249660211287189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69533846349499773474191459 104300769524249660211287189)
            ·
              refine ⟨4889098571449202822404087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104300769524249660211287189 4889098571449202822404087)
              ·
                refine ⟨7333647857173804233606131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4889098571449202822404087 7333647857173804233606131)
                ·
                  refine ⟨11000471785760706350409197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7333647857173804233606131 11000471785760706350409197)
                  ·
                    refine ⟨4125176919660264881403449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11000471785760706350409197 4125176919660264881403449)
                    ·
                      refine ⟨3093882689745198661052587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125176919660264881403449 3093882689745198661052587)
                      ·
                        rfl

theorem cell23_6025315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_6025315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025315 prefixEnd_6025315 := by exact prefixLift 6025315
  have htrace : WordTrace (prefixWord ++ tailWord_6025315) baseStart_6025315 baseEnd_6025315 := by
    simpa [prefixWord, tailWord_6025315, baseEnd_6025315] using wordTrace_append hprefix tailTrace_6025315
  have hstable : (prefixWord ++ tailWord_6025315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025315).length < 2 ^ (prefixWord ++ tailWord_6025315).sum := by decide
  have hdescent : baseEnd_6025315 < baseStart_6025315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025322 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_6025322 : Nat := 118140960795 + 6025322 * 2 ^ 59
def prefixEnd_6025322 : Nat := 4983230072969 + 3 ^ 40 * 6025322 * 2
def baseEnd_6025322 : Nat := 3093886284109780133665055

theorem tailTrace_6025322 : CollatzResearch.WordTrace tailWord_6025322 prefixEnd_6025322 3093886284109780133665055 := by
  unfold tailWord_6025322
  simp only [CollatzResearch.WordTrace]
  refine ⟨54940386869323727979101555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146507698318196607944270813 54940386869323727979101555)
  ·
    refine ⟨82410580303985591968652333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54940386869323727979101555 82410580303985591968652333)
    ·
      refine ⟨30903967613994596988244625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82410580303985591968652333 30903967613994596988244625)
      ·
        refine ⟨23177975710495947741183469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30903967613994596988244625 23177975710495947741183469)
        ·
          refine ⟨8691740891435980402943801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23177975710495947741183469 8691740891435980402943801)
          ·
            refine ⟨6518805668576985302207851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8691740891435980402943801 6518805668576985302207851)
            ·
              refine ⟨9778208502865477953311777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6518805668576985302207851 9778208502865477953311777)
              ·
                refine ⟨7333656377149108464983833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9778208502865477953311777 7333656377149108464983833)
                ·
                  refine ⟨5500242282861831348737875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7333656377149108464983833 5500242282861831348737875)
                  ·
                    refine ⟨8250363424292747023106813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5500242282861831348737875 8250363424292747023106813)
                    ·
                      refine ⟨3093886284109780133665055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8250363424292747023106813 3093886284109780133665055)
                      ·
                        rfl

theorem cell23_6025322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_6025322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025322 prefixEnd_6025322 := by exact prefixLift 6025322
  have htrace : WordTrace (prefixWord ++ tailWord_6025322) baseStart_6025322 baseEnd_6025322 := by
    simpa [prefixWord, tailWord_6025322, baseEnd_6025322] using wordTrace_append hprefix tailTrace_6025322
  have hstable : (prefixWord ++ tailWord_6025322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025322).length < 2 ^ (prefixWord ++ tailWord_6025322).sum := by decide
  have hdescent : baseEnd_6025322 < baseStart_6025322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025341 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_6025341 : Nat := 118140960795 + 6025341 * 2 ^ 59
def prefixEnd_6025341 : Nat := 4983230072969 + 3 ^ 40 * 6025341 * 2
def baseEnd_6025341 : Nat := 3093896040242215559327467

theorem tailTrace_6025341 : CollatzResearch.WordTrace tailWord_6025341 prefixEnd_6025341 3093896040242215559327467 := by
  unfold tailWord_6025341
  simp only [CollatzResearch.WordTrace]
  refine ⟨219762240464226078161347877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146508160309484052107565251 219762240464226078161347877)
  ·
    refine ⟨41205420087042389655252727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219762240464226078161347877 41205420087042389655252727)
    ·
      refine ⟨61808130130563584482879091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41205420087042389655252727 61808130130563584482879091)
      ·
        refine ⟨92712195195845376724318637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61808130130563584482879091 92712195195845376724318637)
        ·
          refine ⟨34767073198442016271619489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92712195195845376724318637 34767073198442016271619489)
          ·
            refine ⟨26075304898831512203714617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34767073198442016271619489 26075304898831512203714617)
            ·
              refine ⟨19556478674123634152785963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26075304898831512203714617 19556478674123634152785963)
              ·
                refine ⟨29334718011185451229178945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19556478674123634152785963 29334718011185451229178945)
                ·
                  refine ⟨22001038508389088421884209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29334718011185451229178945 22001038508389088421884209)
                  ·
                    refine ⟨16500778881291816316413157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22001038508389088421884209 16500778881291816316413157)
                    ·
                      refine ⟨3093896040242215559327467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16500778881291816316413157 3093896040242215559327467)
                      ·
                        rfl

theorem cell23_6025341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_6025341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025341 prefixEnd_6025341 := by exact prefixLift 6025341
  have htrace : WordTrace (prefixWord ++ tailWord_6025341) baseStart_6025341 baseEnd_6025341 := by
    simpa [prefixWord, tailWord_6025341, baseEnd_6025341] using wordTrace_append hprefix tailTrace_6025341
  have hstable : (prefixWord ++ tailWord_6025341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025341).length < 2 ^ (prefixWord ++ tailWord_6025341).sum := by decide
  have hdescent : baseEnd_6025341 < baseStart_6025341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025371 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 4, 5, 2]
def baseStart_6025371 : Nat := 118140960795 + 6025371 * 2 ^ 59
def prefixEnd_6025371 : Nat := 4983230072969 + 3 ^ 40 * 6025371 * 2
def baseEnd_6025371 : Nat := 3093911444661850441952329

theorem tailTrace_6025371 : CollatzResearch.WordTrace tailWord_6025371 prefixEnd_6025371 3093911444661850441952329 := by
  unfold tailWord_6025371
  simp only [CollatzResearch.WordTrace]
  refine ⟨219763334654117393284939967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146508889769411595523293311 219763334654117393284939967)
  ·
    refine ⟨329645001981176089927409951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219763334654117393284939967 329645001981176089927409951)
    ·
      refine ⟨494467502971764134891114927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329645001981176089927409951 494467502971764134891114927)
      ·
        refine ⟨741701254457646202336672391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494467502971764134891114927 741701254457646202336672391)
        ·
          refine ⟨1112551881686469303505008587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741701254457646202336672391 1112551881686469303505008587)
          ·
            refine ⟨1668827822529703955257512881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112551881686469303505008587 1668827822529703955257512881)
            ·
              refine ⟨1251620866897277966443134661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668827822529703955257512881 1251620866897277966443134661)
              ·
                refine ⟨234678912543239618708087749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1251620866897277966443134661 234678912543239618708087749)
                ·
                  refine ⟨44002296101857428507766453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234678912543239618708087749 44002296101857428507766453)
                  ·
                    refine ⟨4125215259549133922603105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44002296101857428507766453 4125215259549133922603105)
                    ·
                      refine ⟨3093911444661850441952329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125215259549133922603105 3093911444661850441952329)
                      ·
                        rfl

theorem cell23_6025371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 5, 2].length) (baseStart_6025371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025371 prefixEnd_6025371 := by exact prefixLift 6025371
  have htrace : WordTrace (prefixWord ++ tailWord_6025371) baseStart_6025371 baseEnd_6025371 := by
    simpa [prefixWord, tailWord_6025371, baseEnd_6025371] using wordTrace_append hprefix tailTrace_6025371
  have hstable : (prefixWord ++ tailWord_6025371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025371).length < 2 ^ (prefixWord ++ tailWord_6025371).sum := by decide
  have hdescent : baseEnd_6025371 < baseStart_6025371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025381 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_6025381 : Nat := 118140960795 + 6025381 * 2 ^ 59
def prefixEnd_6025381 : Nat := 4983230072969 + 3 ^ 40 * 6025381 * 2
def baseEnd_6025381 : Nat := 1031305526489465134275761

theorem tailTrace_6025381 : CollatzResearch.WordTrace tailWord_6025381 prefixEnd_6025381 1031305526489465134275761 := by
  unfold tailWord_6025381
  simp only [CollatzResearch.WordTrace]
  refine ⟨219763699384081164992803997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146509132922720776661869331 219763699384081164992803997)
  ·
    refine ⟨82411387269030436872301499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219763699384081164992803997 82411387269030436872301499)
    ·
      refine ⟨123617080903545655308452249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82411387269030436872301499 123617080903545655308452249)
      ·
        refine ⟨92712810677659241481339187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123617080903545655308452249 92712810677659241481339187)
        ·
          refine ⟨139069216016488862222008781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92712810677659241481339187 139069216016488862222008781)
          ·
            refine ⟨52150956006183323333253293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139069216016488862222008781 52150956006183323333253293)
            ·
              refine ⟨19556608502318746249969985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52150956006183323333253293 19556608502318746249969985)
              ·
                refine ⟨14667456376739059687477489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19556608502318746249969985 14667456376739059687477489)
                ·
                  refine ⟨11000592282554294765608117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14667456376739059687477489 11000592282554294765608117)
                  ·
                    refine ⟨1031305526489465134275761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11000592282554294765608117 1031305526489465134275761)
                    ·
                      rfl

theorem cell23_6025381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_6025381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025381 prefixEnd_6025381 := by exact prefixLift 6025381
  have htrace : WordTrace (prefixWord ++ tailWord_6025381) baseStart_6025381 baseEnd_6025381 := by
    simpa [prefixWord, tailWord_6025381, baseEnd_6025381] using wordTrace_append hprefix tailTrace_6025381
  have hstable : (prefixWord ++ tailWord_6025381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025381).length < 2 ^ (prefixWord ++ tailWord_6025381).sum := by decide
  have hdescent : baseEnd_6025381 < baseStart_6025381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025401 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 4]
def baseStart_6025401 : Nat := 118140960795 + 6025401 * 2 ^ 59
def prefixEnd_6025401 : Nat := 4983230072969 + 3 ^ 40 * 6025401 * 2
def baseEnd_6025401 : Nat := 3093926849081485324577191

theorem tailTrace_6025401 : CollatzResearch.WordTrace tailWord_6025401 prefixEnd_6025401 3093926849081485324577191 := by
  unfold tailWord_6025401
  simp only [CollatzResearch.WordTrace]
  refine ⟨219764428844008708408532057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146509619229339138939021371 219764428844008708408532057)
  ·
    refine ⟨164823321633006531306399043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219764428844008708408532057 164823321633006531306399043)
    ·
      refine ⟨247234982449509796959598565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164823321633006531306399043 247234982449509796959598565)
      ·
        refine ⟨46356559209283086929924731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247234982449509796959598565 46356559209283086929924731)
        ·
          refine ⟨69534838813924630394887097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46356559209283086929924731 69534838813924630394887097)
          ·
            refine ⟨52151129110443472796165323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69534838813924630394887097 52151129110443472796165323)
            ·
              refine ⟨78226693665665209194247985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52151129110443472796165323 78226693665665209194247985)
              ·
                refine ⟨58670020249248906895685989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78226693665665209194247985 58670020249248906895685989)
                ·
                  refine ⟨11000628796734170042941123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58670020249248906895685989 11000628796734170042941123)
                  ·
                    refine ⟨16500943195101255064411685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11000628796734170042941123 16500943195101255064411685)
                    ·
                      refine ⟨3093926849081485324577191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16500943195101255064411685 3093926849081485324577191)
                      ·
                        rfl

theorem cell23_6025401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_6025401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025401 prefixEnd_6025401 := by exact prefixLift 6025401
  have htrace : WordTrace (prefixWord ++ tailWord_6025401) baseStart_6025401 baseEnd_6025401 := by
    simpa [prefixWord, tailWord_6025401, baseEnd_6025401] using wordTrace_append hprefix tailTrace_6025401
  have hstable : (prefixWord ++ tailWord_6025401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025401).length < 2 ^ (prefixWord ++ tailWord_6025401).sum := by decide
  have hdescent : baseEnd_6025401 < baseStart_6025401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025418 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_6025418 : Nat := 118140960795 + 6025418 * 2 ^ 59
def prefixEnd_6025418 : Nat := 4983230072969 + 3 ^ 40 * 6025418 * 2
def baseEnd_6025418 : Nat := 3093935578252611758064613

theorem tailTrace_6025418 : CollatzResearch.WordTrace tailWord_6025418 prefixEnd_6025418 3093935578252611758064613 := by
  unfold tailWord_6025418
  simp only [CollatzResearch.WordTrace]
  refine ⟨54941262221236780077975227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146510032589964746874600605 54941262221236780077975227)
  ·
    refine ⟨82411893331855170116962841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54941262221236780077975227 82411893331855170116962841)
    ·
      refine ⟨61808919998891377587722131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82411893331855170116962841 61808919998891377587722131)
      ·
        refine ⟨92713379998337066381583197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61808919998891377587722131 92713379998337066381583197)
        ·
          refine ⟨34767517499376399893093699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92713379998337066381583197 34767517499376399893093699)
          ·
            refine ⟨52151276249064599839640549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34767517499376399893093699 52151276249064599839640549)
            ·
              refine ⟨9778364296699612469932603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52151276249064599839640549 9778364296699612469932603)
              ·
                refine ⟨14667546445049418704898905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9778364296699612469932603 14667546445049418704898905)
                ·
                  refine ⟨11000659833787064028674179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14667546445049418704898905 11000659833787064028674179)
                  ·
                    refine ⟨16500989750680596043011269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11000659833787064028674179 16500989750680596043011269)
                    ·
                      refine ⟨3093935578252611758064613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16500989750680596043011269 3093935578252611758064613)
                      ·
                        rfl

theorem cell23_6025418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_6025418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025418 prefixEnd_6025418 := by exact prefixLift 6025418
  have htrace : WordTrace (prefixWord ++ tailWord_6025418) baseStart_6025418 baseEnd_6025418 := by
    simpa [prefixWord, tailWord_6025418, baseEnd_6025418] using wordTrace_append hprefix tailTrace_6025418
  have hstable : (prefixWord ++ tailWord_6025418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025418).length < 2 ^ (prefixWord ++ tailWord_6025418).sum := by decide
  have hdescent : baseEnd_6025418 < baseStart_6025418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025436 : List Nat := [2, 2, 5, 2, 2, 1, 2, 2, 5]
def baseStart_6025436 : Nat := 118140960795 + 6025436 * 2 ^ 59
def prefixEnd_6025436 : Nat := 4983230072969 + 3 ^ 40 * 6025436 * 2
def baseEnd_6025436 : Nat := 343771646767154743071059

theorem tailTrace_6025436 : CollatzResearch.WordTrace tailWord_6025436 prefixEnd_6025436 343771646767154743071059 := by
  unfold tailWord_6025436
  simp only [CollatzResearch.WordTrace]
  refine ⟨109882852699440954693028081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146510470265921272924037441 109882852699440954693028081)
  ·
    refine ⟨82412139524580716019771061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109882852699440954693028081 82412139524580716019771061)
    ·
      refine ⟨7726138080429442126853537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82412139524580716019771061 7726138080429442126853537)
      ·
        refine ⟨5794603560322081595140153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7726138080429442126853537 5794603560322081595140153)
        ·
          refine ⟨4345952670241561196355115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5794603560322081595140153 4345952670241561196355115)
          ·
            refine ⟨6518929005362341794532673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345952670241561196355115 6518929005362341794532673)
            ·
              refine ⟨4889196754021756345899505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6518929005362341794532673 4889196754021756345899505)
              ·
                refine ⟨3666897565516317259424629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4889196754021756345899505 3666897565516317259424629)
                ·
                  refine ⟨343771646767154743071059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3666897565516317259424629 343771646767154743071059)
                  ·
                    rfl

theorem cell23_6025436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_6025436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025436 prefixEnd_6025436 := by exact prefixLift 6025436
  have htrace : WordTrace (prefixWord ++ tailWord_6025436) baseStart_6025436 baseEnd_6025436 := by
    simpa [prefixWord, tailWord_6025436, baseEnd_6025436] using wordTrace_append hprefix tailTrace_6025436
  have hstable : (prefixWord ++ tailWord_6025436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025436).length < 2 ^ (prefixWord ++ tailWord_6025436).sum := by decide
  have hdescent : baseEnd_6025436 < baseStart_6025436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025458 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 6]
def baseStart_6025458 : Nat := 118140960795 + 6025458 * 2 ^ 59
def prefixEnd_6025458 : Nat := 4983230072969 + 3 ^ 40 * 6025458 * 2
def baseEnd_6025458 : Nat := 343772901942087955729381

theorem tailTrace_6025458 : CollatzResearch.WordTrace tailWord_6025458 prefixEnd_6025458 343772901942087955729381 := by
  unfold tailWord_6025458
  simp only [CollatzResearch.WordTrace]
  refine ⟨54941626951200551785839257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146511005203201471428904685 54941626951200551785839257)
  ·
    refine ⟨41206220213400413839379443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54941626951200551785839257 41206220213400413839379443)
    ·
      refine ⟨61809330320100620759069165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41206220213400413839379443 61809330320100620759069165)
      ·
        refine ⟨23178498870037732784650937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61809330320100620759069165 23178498870037732784650937)
        ·
          refine ⟨17383874152528299588488203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23178498870037732784650937 17383874152528299588488203)
          ·
            refine ⟨26075811228792449382732305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17383874152528299588488203 26075811228792449382732305)
            ·
              refine ⟨19556858421594337037049229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26075811228792449382732305 19556858421594337037049229)
              ·
                refine ⟨7333821908097876388893461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19556858421594337037049229 7333821908097876388893461)
                ·
                  refine ⟨343772901942087955729381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7333821908097876388893461 343772901942087955729381)
                  ·
                    rfl

theorem cell23_6025458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_6025458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025458 prefixEnd_6025458 := by exact prefixLift 6025458
  have htrace : WordTrace (prefixWord ++ tailWord_6025458) baseStart_6025458 baseEnd_6025458 := by
    simpa [prefixWord, tailWord_6025458, baseEnd_6025458] using wordTrace_append hprefix tailTrace_6025458
  have hstable : (prefixWord ++ tailWord_6025458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025458).length < 2 ^ (prefixWord ++ tailWord_6025458).sum := by decide
  have hdescent : baseEnd_6025458 < baseStart_6025458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025471 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 3, 5]
def baseStart_6025471 : Nat := 118140960795 + 6025471 * 2 ^ 59
def prefixEnd_6025471 : Nat := 4983230072969 + 3 ^ 40 * 6025471 * 2
def baseEnd_6025471 : Nat := 1031320930909100016900623

theorem tailTrace_6025471 : CollatzResearch.WordTrace tailWord_6025471 prefixEnd_6025471 1031320930909100016900623 := by
  unfold tailWord_6025471
  simp only [CollatzResearch.WordTrace]
  refine ⟨219766981953755110363580267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146511321302503406909053511 219766981953755110363580267)
  ·
    refine ⟨329650472930632665545370401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219766981953755110363580267 329650472930632665545370401)
    ·
      refine ⟨247237854697974499159027801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329650472930632665545370401 247237854697974499159027801)
      ·
        refine ⟨185428391023480874369270851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247237854697974499159027801 185428391023480874369270851)
        ·
          refine ⟨278142586535221311553906277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185428391023480874369270851 278142586535221311553906277)
          ·
            refine ⟨52151734975353995916357427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278142586535221311553906277 52151734975353995916357427)
            ·
              refine ⟨78227602463030993874536141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52151734975353995916357427 78227602463030993874536141)
              ·
                refine ⟨29335350923636622702951053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78227602463030993874536141 29335350923636622702951053)
                ·
                  refine ⟨11000756596363733513606645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29335350923636622702951053 11000756596363733513606645)
                  ·
                    refine ⟨1031320930909100016900623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11000756596363733513606645 1031320930909100016900623)
                    ·
                      rfl

theorem cell23_6025471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_6025471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025471 prefixEnd_6025471 := by exact prefixLift 6025471
  have htrace : WordTrace (prefixWord ++ tailWord_6025471) baseStart_6025471 baseEnd_6025471 := by
    simpa [prefixWord, tailWord_6025471, baseEnd_6025471] using wordTrace_append hprefix tailTrace_6025471
  have hstable : (prefixWord ++ tailWord_6025471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025471).length < 2 ^ (prefixWord ++ tailWord_6025471).sum := by decide
  have hdescent : baseEnd_6025471 < baseStart_6025471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025479 : List Nat := [1, 1, 4, 5, 1, 1, 2, 3, 1, 4]
def baseStart_6025479 : Nat := 118140960795 + 6025479 * 2 ^ 59
def prefixEnd_6025479 : Nat := 4983230072969 + 3 ^ 40 * 6025479 * 2
def baseEnd_6025479 : Nat := 1031322300190845339800611

theorem tailTrace_6025479 : CollatzResearch.WordTrace tailWord_6025479 prefixEnd_6025479 1031322300190845339800611 := by
  unfold tailWord_6025479
  simp only [CollatzResearch.WordTrace]
  refine ⟨219767273737726127729871491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146511515825150751819914327 219767273737726127729871491)
  ·
    refine ⟨329650910606589191594807237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219767273737726127729871491 329650910606589191594807237)
    ·
      refine ⟨61809545738735473424026357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329650910606589191594807237 61809545738735473424026357)
      ·
        refine ⟨5794644913006450633502471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61809545738735473424026357 5794644913006450633502471)
        ·
          refine ⟨8691967369509675950253707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5794644913006450633502471 8691967369509675950253707)
          ·
            refine ⟨13037951054264513925380561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8691967369509675950253707 13037951054264513925380561)
            ·
              refine ⟨9778463290698385444035421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13037951054264513925380561 9778463290698385444035421)
              ·
                refine ⟨3666923734011894541513283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9778463290698385444035421 3666923734011894541513283)
                ·
                  refine ⟨5500385601017841812269925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666923734011894541513283 5500385601017841812269925)
                  ·
                    refine ⟨1031322300190845339800611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5500385601017841812269925 1031322300190845339800611)
                    ·
                      rfl

theorem cell23_6025479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_6025479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025479 prefixEnd_6025479 := by exact prefixLift 6025479
  have htrace : WordTrace (prefixWord ++ tailWord_6025479) baseStart_6025479 baseEnd_6025479 := by
    simpa [prefixWord, tailWord_6025479, baseEnd_6025479] using wordTrace_append hprefix tailTrace_6025479
  have hstable : (prefixWord ++ tailWord_6025479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025479).length < 2 ^ (prefixWord ++ tailWord_6025479).sum := by decide
  have hdescent : baseEnd_6025479 < baseStart_6025479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025525 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_6025525 : Nat := 118140960795 + 6025525 * 2 ^ 59
def prefixEnd_6025525 : Nat := 4983230072969 + 3 ^ 40 * 6025525 * 2
def baseEnd_6025525 : Nat := 3093990520682642839426621

theorem tailTrace_6025525 : CollatzResearch.WordTrace tailWord_6025525 prefixEnd_6025525 3093990520682642839426621 := by
  unfold tailWord_6025525
  simp only [CollatzResearch.WordTrace]
  refine ⟨219768951495559477586046029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146512634330372985057364019 219768951495559477586046029)
  ·
    refine ⟨82413356810834804094767261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219768951495559477586046029 82413356810834804094767261)
    ·
      refine ⟨30905008804063051535537723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82413356810834804094767261 30905008804063051535537723)
      ·
        refine ⟨46357513206094577303306585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30905008804063051535537723 46357513206094577303306585)
        ·
          refine ⟨34768134904570932977479939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46357513206094577303306585 34768134904570932977479939)
          ·
            refine ⟨52152202356856399466219909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34768134904570932977479939 52152202356856399466219909)
            ·
              refine ⟨9778537941910574899916233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52152202356856399466219909 9778537941910574899916233)
              ·
                refine ⟨7333903456432931174937175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9778537941910574899916233 7333903456432931174937175)
                ·
                  refine ⟨11000855184649396762405763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7333903456432931174937175 11000855184649396762405763)
                  ·
                    refine ⟨16501282776974095143608645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11000855184649396762405763 16501282776974095143608645)
                    ·
                      refine ⟨3093990520682642839426621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16501282776974095143608645 3093990520682642839426621)
                      ·
                        rfl

theorem cell23_6025525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_6025525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025525 prefixEnd_6025525 := by exact prefixLift 6025525
  have htrace : WordTrace (prefixWord ++ tailWord_6025525) baseStart_6025525 baseEnd_6025525 := by
    simpa [prefixWord, tailWord_6025525, baseEnd_6025525] using wordTrace_append hprefix tailTrace_6025525
  have hstable : (prefixWord ++ tailWord_6025525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025525).length < 2 ^ (prefixWord ++ tailWord_6025525).sum := by decide
  have hdescent : baseEnd_6025525 < baseStart_6025525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025528 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 3, 2, 3]
def baseStart_6025528 : Nat := 118140960795 + 6025528 * 2 ^ 59
def prefixEnd_6025528 : Nat := 4983230072969 + 3 ^ 40 * 6025528 * 2
def baseEnd_6025528 : Nat := 3093992061124606327689107

theorem tailTrace_6025528 : CollatzResearch.WordTrace tailWord_6025528 prefixEnd_6025528 3093992061124606327689107 := by
  unfold tailWord_6025528
  simp only [CollatzResearch.WordTrace]
  refine ⟨109884530457274304549202619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146512707276365739398936825 109884530457274304549202619)
  ·
    refine ⟨164826795685911456823803929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109884530457274304549202619 164826795685911456823803929)
    ·
      refine ⟨123620096764433592617852947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164826795685911456823803929 123620096764433592617852947)
      ·
        refine ⟨185430145146650388926779421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123620096764433592617852947 185430145146650388926779421)
        ·
          refine ⟨69536304429993895847542283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185430145146650388926779421 69536304429993895847542283)
          ·
            refine ⟨104304456644990843771313425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69536304429993895847542283 104304456644990843771313425)
            ·
              refine ⟨78228342483743132828485069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104304456644990843771313425 78228342483743132828485069)
              ·
                refine ⟨29335628431403674810681901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78228342483743132828485069 29335628431403674810681901)
                ·
                  refine ⟨11000860661776378054005713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29335628431403674810681901 11000860661776378054005713)
                  ·
                    refine ⟨8250645496332283540504285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11000860661776378054005713 8250645496332283540504285)
                    ·
                      refine ⟨3093992061124606327689107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8250645496332283540504285 3093992061124606327689107)
                      ·
                        rfl

theorem cell23_6025528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_6025528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025528 prefixEnd_6025528 := by exact prefixLift 6025528
  have htrace : WordTrace (prefixWord ++ tailWord_6025528) baseStart_6025528 baseEnd_6025528 := by
    simpa [prefixWord, tailWord_6025528, baseEnd_6025528] using wordTrace_append hprefix tailTrace_6025528
  have hstable : (prefixWord ++ tailWord_6025528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025528).length < 2 ^ (prefixWord ++ tailWord_6025528).sum := by decide
  have hdescent : baseEnd_6025528 < baseStart_6025528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025561 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 2, 7]
def baseStart_6025561 : Nat := 118140960795 + 6025561 * 2 ^ 59
def prefixEnd_6025561 : Nat := 4983230072969 + 3 ^ 40 * 6025561 * 2
def baseEnd_6025561 : Nat := 1031336335328734899525485

theorem tailTrace_6025561 : CollatzResearch.WordTrace tailWord_6025561 prefixEnd_6025561 1031336335328734899525485 := by
  unfold tailWord_6025561
  simp only [CollatzResearch.WordTrace]
  refine ⟨219770264523429055734356537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146513509682286037156237691 219770264523429055734356537)
  ·
    refine ⟨164827698392571791800767403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219770264523429055734356537 164827698392571791800767403)
    ·
      refine ⟨247241547588857687701151105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164827698392571791800767403 247241547588857687701151105)
      ·
        refine ⟨185431160691643265775863329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247241547588857687701151105 185431160691643265775863329)
        ·
          refine ⟨139073370518732449331897497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185431160691643265775863329 139073370518732449331897497)
          ·
            refine ⟨104305027889049336998923123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139073370518732449331897497 104305027889049336998923123)
            ·
              refine ⟨156457541833574005498384685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104305027889049336998923123 156457541833574005498384685)
              ·
                refine ⟨58671578187590252061894257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156457541833574005498384685 58671578187590252061894257)
                ·
                  refine ⟨44003683640692689046420693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58671578187590252061894257 44003683640692689046420693)
                  ·
                    refine ⟨1031336335328734899525485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44003683640692689046420693 1031336335328734899525485)
                    ·
                      rfl

theorem cell23_6025561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_6025561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025561 prefixEnd_6025561 := by exact prefixLift 6025561
  have htrace : WordTrace (prefixWord ++ tailWord_6025561) baseStart_6025561 baseEnd_6025561 := by
    simpa [prefixWord, tailWord_6025561, baseEnd_6025561] using wordTrace_append hprefix tailTrace_6025561
  have hstable : (prefixWord ++ tailWord_6025561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025561).length < 2 ^ (prefixWord ++ tailWord_6025561).sum := by decide
  have hdescent : baseEnd_6025561 < baseStart_6025561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025591 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 3, 8]
def baseStart_6025591 : Nat := 118140960795 + 6025591 * 2 ^ 59
def prefixEnd_6025591 : Nat := 4983230072969 + 3 ^ 40 * 6025591 * 2
def baseEnd_6025591 : Nat := 1031341470135279860400439

theorem tailTrace_6025591 : CollatzResearch.WordTrace tailWord_6025591 prefixEnd_6025591 1031341470135279860400439 := by
  unfold tailWord_6025591
  simp only [CollatzResearch.WordTrace]
  refine ⟨219771358713320370857948627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146514239142213580571965751 219771358713320370857948627)
  ·
    refine ⟨329657038069980556286922941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219771358713320370857948627 329657038069980556286922941)
    ·
      refine ⟨123621389276242708607596103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329657038069980556286922941 123621389276242708607596103)
      ·
        refine ⟨185432083914364062911394155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123621389276242708607596103 185432083914364062911394155)
        ·
          refine ⟨278148125871546094367091233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185432083914364062911394155 278148125871546094367091233)
          ·
            refine ⟨208611094403659570775318425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278148125871546094367091233 208611094403659570775318425)
            ·
              refine ⟨156458320802744678081488819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208611094403659570775318425 156458320802744678081488819)
              ·
                refine ⟨234687481204117017122233229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156458320802744678081488819 234687481204117017122233229)
                ·
                  refine ⟨88007805451543881420837461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234687481204117017122233229 88007805451543881420837461)
                  ·
                    refine ⟨1031341470135279860400439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88007805451543881420837461 1031341470135279860400439)
                    ·
                      rfl

theorem cell23_6025591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_6025591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025591 prefixEnd_6025591 := by exact prefixLift 6025591
  have htrace : WordTrace (prefixWord ++ tailWord_6025591) baseStart_6025591 baseEnd_6025591 := by
    simpa [prefixWord, tailWord_6025591, baseEnd_6025591] using wordTrace_append hprefix tailTrace_6025591
  have hstable : (prefixWord ++ tailWord_6025591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025591).length < 2 ^ (prefixWord ++ tailWord_6025591).sum := by decide
  have hdescent : baseEnd_6025591 < baseStart_6025591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025608 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 2, 6]
def baseStart_6025608 : Nat := 118140960795 + 6025608 * 2 ^ 59
def prefixEnd_6025608 : Nat := 4983230072969 + 3 ^ 40 * 6025608 * 2
def baseEnd_6025608 : Nat := 1031344379858988671562913

theorem tailTrace_6025608 : CollatzResearch.WordTrace tailWord_6025608 prefixEnd_6025608 1031344379858988671562913 := by
  unfold tailWord_6025608
  simp only [CollatzResearch.WordTrace]
  refine ⟨109885989377129391380658739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146514652502839188507544985 109885989377129391380658739)
  ·
    refine ⟨164828984065694087070988109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109885989377129391380658739 164828984065694087070988109)
    ·
      refine ⟨61810869024635282651620541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164828984065694087070988109 61810869024635282651620541)
      ·
        refine ⟨23179075884238230994357703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61810869024635282651620541 23179075884238230994357703)
        ·
          refine ⟨34768613826357346491536555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23179075884238230994357703 34768613826357346491536555)
          ·
            refine ⟨52152920739536019737304833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34768613826357346491536555 52152920739536019737304833)
            ·
              refine ⟨39114690554652014802978625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52152920739536019737304833 39114690554652014802978625)
              ·
                refine ⟨29336017915989011102233969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39114690554652014802978625 29336017915989011102233969)
                ·
                  refine ⟨22002013436991758326675477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29336017915989011102233969 22002013436991758326675477)
                  ·
                    refine ⟨1031344379858988671562913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22002013436991758326675477 1031344379858988671562913)
                    ·
                      rfl

theorem cell23_6025608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_6025608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025608 prefixEnd_6025608 := by exact prefixLift 6025608
  have htrace : WordTrace (prefixWord ++ tailWord_6025608) baseStart_6025608 baseEnd_6025608 := by
    simpa [prefixWord, tailWord_6025608, baseEnd_6025608] using wordTrace_append hprefix tailTrace_6025608
  have hstable : (prefixWord ++ tailWord_6025608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025608).length < 2 ^ (prefixWord ++ tailWord_6025608).sum := by decide
  have hdescent : baseEnd_6025608 < baseStart_6025608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025610 : List Nat := [3, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6025610 : Nat := 118140960795 + 6025610 * 2 ^ 59
def prefixEnd_6025610 : Nat := 4983230072969 + 3 ^ 40 * 6025610 * 2
def baseEnd_6025610 : Nat := 3094034166538275006863731

theorem tailTrace_6025610 : CollatzResearch.WordTrace tailWord_6025610 prefixEnd_6025610 3094034166538275006863731 := by
  unfold tailWord_6025610
  simp only [CollatzResearch.WordTrace]
  refine ⟨54943012925062884275722571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146514701133501024735260189 54943012925062884275722571)
  ·
    refine ⟨82414519387594326413583857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54943012925062884275722571 82414519387594326413583857)
    ·
      refine ⟨61810889540695744810187893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82414519387594326413583857 61810889540695744810187893)
      ·
        refine ⟨5794770894440226075955115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61810889540695744810187893 5794770894440226075955115)
        ·
          refine ⟨8692156341660339113932673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5794770894440226075955115 8692156341660339113932673)
          ·
            refine ⟨6519117256245254335449505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8692156341660339113932673 6519117256245254335449505)
            ·
              refine ⟨4889337942183940751587129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6519117256245254335449505 4889337942183940751587129)
              ·
                refine ⟨3667003456637955563690347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4889337942183940751587129 3667003456637955563690347)
                ·
                  refine ⟨5500505184956933345535521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3667003456637955563690347 5500505184956933345535521)
                  ·
                    refine ⟨4125378888717700009151641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5500505184956933345535521 4125378888717700009151641)
                    ·
                      refine ⟨3094034166538275006863731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125378888717700009151641 3094034166538275006863731)
                      ·
                        rfl

theorem cell23_6025610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6025610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025610 prefixEnd_6025610 := by exact prefixLift 6025610
  have htrace : WordTrace (prefixWord ++ tailWord_6025610) baseStart_6025610 baseEnd_6025610 := by
    simpa [prefixWord, tailWord_6025610, baseEnd_6025610] using wordTrace_append hprefix tailTrace_6025610
  have hstable : (prefixWord ++ tailWord_6025610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025610).length < 2 ^ (prefixWord ++ tailWord_6025610).sum := by decide
  have hdescent : baseEnd_6025610 < baseStart_6025610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025632 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 1, 4, 2]
def baseStart_6025632 : Nat := 118140960795 + 6025632 * 2 ^ 59
def prefixEnd_6025632 : Nat := 4983230072969 + 3 ^ 40 * 6025632 * 2
def baseEnd_6025632 : Nat := 3094045463112673920788629

theorem tailTrace_6025632 : CollatzResearch.WordTrace tailWord_6025632 prefixEnd_6025632 3094045463112673920788629 := by
  unfold tailWord_6025632
  simp only [CollatzResearch.WordTrace]
  refine ⟨109886427053085917430095575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146515236070781223240127433 109886427053085917430095575)
  ·
    refine ⟨164829640579628876145143363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109886427053085917430095575 164829640579628876145143363)
    ·
      refine ⟨247244460869443314217715045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164829640579628876145143363 247244460869443314217715045)
      ·
        refine ⟨46358336413020621415821571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247244460869443314217715045 46358336413020621415821571)
        ·
          refine ⟨69537504619530932123732357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46358336413020621415821571 69537504619530932123732357)
          ·
            refine ⟨13038282116162049773199817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69537504619530932123732357 13038282116162049773199817)
            ·
              refine ⟨9778711587121537329899863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13038282116162049773199817 9778711587121537329899863)
              ·
                refine ⟨14668067380682305994849795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9778711587121537329899863 14668067380682305994849795)
                ·
                  refine ⟨22002101071023458992274693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14668067380682305994849795 22002101071023458992274693)
                  ·
                    refine ⟨4125393950816898561051505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22002101071023458992274693 4125393950816898561051505)
                    ·
                      refine ⟨3094045463112673920788629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125393950816898561051505 3094045463112673920788629)
                      ·
                        rfl

theorem cell23_6025632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_6025632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025632 prefixEnd_6025632 := by exact prefixLift 6025632
  have htrace : WordTrace (prefixWord ++ tailWord_6025632) baseStart_6025632 baseEnd_6025632 := by
    simpa [prefixWord, tailWord_6025632, baseEnd_6025632] using wordTrace_append hprefix tailTrace_6025632
  have hstable : (prefixWord ++ tailWord_6025632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025632).length < 2 ^ (prefixWord ++ tailWord_6025632).sum := by decide
  have hdescent : baseEnd_6025632 < baseStart_6025632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025653 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_6025653 : Nat := 118140960795 + 6025653 * 2 ^ 59
def prefixEnd_6025653 : Nat := 4983230072969 + 3 ^ 40 * 6025653 * 2
def baseEnd_6025653 : Nat := 3094056246206418338626033

theorem tailTrace_6025653 : CollatzResearch.WordTrace tailWord_6025653 prefixEnd_6025653 3094056246206418338626033 := by
  unfold tailWord_6025653
  simp only [CollatzResearch.WordTrace]
  refine ⟨219773620039095755446705613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146515746692730503631137075 219773620039095755446705613)
  ·
    refine ⟨82415107514660908292514605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219773620039095755446705613 82415107514660908292514605)
    ·
      refine ⟨30905665317997840609692977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82415107514660908292514605 30905665317997840609692977)
      ·
        refine ⟨23179248988498380457269733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30905665317997840609692977 23179248988498380457269733)
        ·
          refine ⟨4346109185343446335738075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23179248988498380457269733 4346109185343446335738075)
          ·
            refine ⟨6519163778015169503607113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346109185343446335738075 6519163778015169503607113)
            ·
              refine ⟨4889372833511377127705335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6519163778015169503607113 4889372833511377127705335)
              ·
                refine ⟨7334059250267065691558003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4889372833511377127705335 7334059250267065691558003)
                ·
                  refine ⟨11001088875400598537337005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7334059250267065691558003 11001088875400598537337005)
                  ·
                    refine ⟨4125408328275224451501377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11001088875400598537337005 4125408328275224451501377)
                    ·
                      refine ⟨3094056246206418338626033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125408328275224451501377 3094056246206418338626033)
                      ·
                        rfl

theorem cell23_6025653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_6025653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025653 prefixEnd_6025653 := by exact prefixLift 6025653
  have htrace : WordTrace (prefixWord ++ tailWord_6025653) baseStart_6025653 baseEnd_6025653 := by
    simpa [prefixWord, tailWord_6025653, baseEnd_6025653] using wordTrace_append hprefix tailTrace_6025653
  have hstable : (prefixWord ++ tailWord_6025653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025653).length < 2 ^ (prefixWord ++ tailWord_6025653).sum := by decide
  have hdescent : baseEnd_6025653 < baseStart_6025653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025655 : List Nat := [1, 1, 3, 1, 3, 3, 1, 5, 5]
def baseStart_6025655 : Nat := 118140960795 + 6025655 * 2 ^ 59
def prefixEnd_6025655 : Nat := 4983230072969 + 3 ^ 40 * 6025655 * 2
def baseEnd_6025655 : Nat := 343784141463080814533447

theorem tailTrace_6025655 : CollatzResearch.WordTrace tailWord_6025655 prefixEnd_6025655 343784141463080814533447 := by
  unfold tailWord_6025655
  simp only [CollatzResearch.WordTrace]
  refine ⟨219773692985088509788278419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146515795323392339858852279 219773692985088509788278419)
  ·
    refine ⟨329660539477632764682417629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219773692985088509788278419 329660539477632764682417629)
    ·
      refine ⟨123622702304112286755906611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329660539477632764682417629 123622702304112286755906611)
      ·
        refine ⟨185434053456168430133859917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123622702304112286755906611 185434053456168430133859917)
        ·
          refine ⟨69537770046063161300197469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185434053456168430133859917 69537770046063161300197469)
          ·
            refine ⟨26076663767273685487574051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69537770046063161300197469 26076663767273685487574051)
            ·
              refine ⟨39114995650910528231361077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26076663767273685487574051 39114995650910528231361077)
              ·
                refine ⟨3667030842272862021690101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39114995650910528231361077 3667030842272862021690101)
                ·
                  refine ⟨343784141463080814533447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3667030842272862021690101 343784141463080814533447)
                  ·
                    rfl

theorem cell23_6025655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 5].length) (baseStart_6025655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025655 prefixEnd_6025655 := by exact prefixLift 6025655
  have htrace : WordTrace (prefixWord ++ tailWord_6025655) baseStart_6025655 baseEnd_6025655 := by
    simpa [prefixWord, tailWord_6025655, baseEnd_6025655] using wordTrace_append hprefix tailTrace_6025655
  have hstable : (prefixWord ++ tailWord_6025655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025655).length < 2 ^ (prefixWord ++ tailWord_6025655).sum := by decide
  have hdescent : baseEnd_6025655 < baseStart_6025655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025678 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_6025678 : Nat := 118140960795 + 6025678 * 2 ^ 59
def prefixEnd_6025678 : Nat := 4983230072969 + 3 ^ 40 * 6025678 * 2
def baseEnd_6025678 : Nat := 3094069083222780740813417

theorem tailTrace_6025678 : CollatzResearch.WordTrace tailWord_6025678 prefixEnd_6025678 3094069083222780740813417 := by
  unfold tailWord_6025678
  simp only [CollatzResearch.WordTrace]
  refine ⟨27471816483000648089545711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146516354576003456477577125 27471816483000648089545711)
  ·
    refine ⟨41207724724500972134318567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27471816483000648089545711 41207724724500972134318567)
    ·
      refine ⟨61811587086751458201477851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41207724724500972134318567 61811587086751458201477851)
      ·
        refine ⟨92717380630127187302216777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61811587086751458201477851 92717380630127187302216777)
        ·
          refine ⟨69538035472595390476662583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92717380630127187302216777 69538035472595390476662583)
          ·
            refine ⟨104307053208893085714993875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69538035472595390476662583 104307053208893085714993875)
            ·
              refine ⟨156460579813339628572490813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104307053208893085714993875 156460579813339628572490813)
              ·
                refine ⟨58672717430002360714684055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156460579813339628572490813 58672717430002360714684055)
                ·
                  refine ⟨88009076145003541072026083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58672717430002360714684055 88009076145003541072026083)
                  ·
                    refine ⟨132013614217505311608039125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88009076145003541072026083 132013614217505311608039125)
                    ·
                      refine ⟨3094069083222780740813417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132013614217505311608039125 3094069083222780740813417)
                      ·
                        rfl

theorem cell23_6025678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_6025678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025678 prefixEnd_6025678 := by exact prefixLift 6025678
  have htrace : WordTrace (prefixWord ++ tailWord_6025678) baseStart_6025678 baseEnd_6025678 := by
    simpa [prefixWord, tailWord_6025678, baseEnd_6025678] using wordTrace_append hprefix tailTrace_6025678
  have hstable : (prefixWord ++ tailWord_6025678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025678).length < 2 ^ (prefixWord ++ tailWord_6025678).sum := by decide
  have hdescent : baseEnd_6025678 < baseStart_6025678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025705 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 4, 4, 2]
def baseStart_6025705 : Nat := 118140960795 + 6025705 * 2 ^ 59
def prefixEnd_6025705 : Nat := 4983230072969 + 3 ^ 40 * 6025705 * 2
def baseEnd_6025705 : Nat := 3094082947200452135175793

theorem tailTrace_6025705 : CollatzResearch.WordTrace tailWord_6025705 prefixEnd_6025705 3094082947200452135175793 := by
  unfold tailWord_6025705
  simp only [CollatzResearch.WordTrace]
  refine ⟨219775516634907368327598569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146517011089938245551732379 219775516634907368327598569)
  ·
    refine ⟨164831637476180526245698927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219775516634907368327598569 164831637476180526245698927)
    ·
      refine ⟨247247456214270789368548391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164831637476180526245698927 247247456214270789368548391)
      ·
        refine ⟨370871184321406184052822587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247247456214270789368548391 370871184321406184052822587)
        ·
          refine ⟨556306776482109276079233881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370871184321406184052822587 556306776482109276079233881)
          ·
            refine ⟨417230082361581957059425411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556306776482109276079233881 417230082361581957059425411)
            ·
              refine ⟨625845123542372935589138117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417230082361581957059425411 625845123542372935589138117)
              ·
                refine ⟨117345960664194925422963397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 625845123542372935589138117 117345960664194925422963397)
                ·
                  refine ⟨22002367624536548516805637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117345960664194925422963397 22002367624536548516805637)
                  ·
                    refine ⟨4125443929600602846901057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22002367624536548516805637 4125443929600602846901057)
                    ·
                      refine ⟨3094082947200452135175793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125443929600602846901057 3094082947200452135175793)
                      ·
                        rfl

theorem cell23_6025705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 4, 2].length) (baseStart_6025705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025705 prefixEnd_6025705 := by exact prefixLift 6025705
  have htrace : WordTrace (prefixWord ++ tailWord_6025705) baseStart_6025705 baseEnd_6025705 := by
    simpa [prefixWord, tailWord_6025705, baseEnd_6025705] using wordTrace_append hprefix tailTrace_6025705
  have hstable : (prefixWord ++ tailWord_6025705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025705).length < 2 ^ (prefixWord ++ tailWord_6025705).sum := by decide
  have hdescent : baseEnd_6025705 < baseStart_6025705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025812 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_6025812 : Nat := 118140960795 + 6025812 * 2 ^ 59
def prefixEnd_6025812 : Nat := 4983230072969 + 3 ^ 40 * 6025812 * 2
def baseEnd_6025812 : Nat := 3094137889630483216537801

theorem tailTrace_6025812 : CollatzResearch.WordTrace tailWord_6025812 prefixEnd_6025812 3094137889630483216537801 := by
  unfold tailWord_6025812
  simp only [CollatzResearch.WordTrace]
  refine ⟨109889709622759862800871845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146519612830346483734495793 109889709622759862800871845)
  ·
    refine ⟨20604320554267474275163471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109889709622759862800871845 20604320554267474275163471)
    ·
      refine ⟨30906480831401211412745207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20604320554267474275163471 30906480831401211412745207)
      ·
        refine ⟨46359721247101817119117811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30906480831401211412745207 46359721247101817119117811)
        ·
          refine ⟨69539581870652725678676717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46359721247101817119117811 69539581870652725678676717)
          ·
            refine ⟨26077343201494772129503769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69539581870652725678676717 26077343201494772129503769)
            ·
              refine ⟨19558007401121079097127827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26077343201494772129503769 19558007401121079097127827)
              ·
                refine ⟨29337011101681618645691741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19558007401121079097127827 29337011101681618645691741)
                ·
                  refine ⟨11001379163130606992134403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29337011101681618645691741 11001379163130606992134403)
                  ·
                    refine ⟨16502068744695910488201605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11001379163130606992134403 16502068744695910488201605)
                    ·
                      refine ⟨3094137889630483216537801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16502068744695910488201605 3094137889630483216537801)
                      ·
                        rfl

theorem cell23_6025812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_6025812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025812 prefixEnd_6025812 := by exact prefixLift 6025812
  have htrace : WordTrace (prefixWord ++ tailWord_6025812) baseStart_6025812 baseEnd_6025812 := by
    simpa [prefixWord, tailWord_6025812, baseEnd_6025812] using wordTrace_append hprefix tailTrace_6025812
  have hstable : (prefixWord ++ tailWord_6025812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025812).length < 2 ^ (prefixWord ++ tailWord_6025812).sum := by decide
  have hdescent : baseEnd_6025812 < baseStart_6025812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025826 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_6025826 : Nat := 118140960795 + 6025826 * 2 ^ 59
def prefixEnd_6025826 : Nat := 4983230072969 + 3 ^ 40 * 6025826 * 2
def baseEnd_6025826 : Nat := 1031381692786548720587579

theorem tailTrace_6025826 : CollatzResearch.WordTrace tailWord_6025826 prefixEnd_6025826 1031381692786548720587579 := by
  unfold tailWord_6025826
  simp only [CollatzResearch.WordTrace]
  refine ⟨54944982466867251498188333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146519953244979337328502221 54944982466867251498188333)
  ·
    refine ⟨20604368425075219311820625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54944982466867251498188333 20604368425075219311820625)
    ·
      refine ⟨15453276318806414483865469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20604368425075219311820625 15453276318806414483865469)
      ·
        refine ⟨5794978619552405431449551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15453276318806414483865469 5794978619552405431449551)
        ·
          refine ⟨8692467929328608147174327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5794978619552405431449551 8692467929328608147174327)
          ·
            refine ⟨13038701893992912220761491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692467929328608147174327 13038701893992912220761491)
            ·
              refine ⟨19558052840989368331142237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13038701893992912220761491 19558052840989368331142237)
              ·
                refine ⟨7334269815371013124178339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19558052840989368331142237 7334269815371013124178339)
                ·
                  refine ⟨11001404723056519686267509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7334269815371013124178339 11001404723056519686267509)
                  ·
                    refine ⟨1031381692786548720587579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11001404723056519686267509 1031381692786548720587579)
                    ·
                      rfl

theorem cell23_6025826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_6025826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025826 prefixEnd_6025826 := by exact prefixLift 6025826
  have htrace : WordTrace (prefixWord ++ tailWord_6025826) baseStart_6025826 baseEnd_6025826 := by
    simpa [prefixWord, tailWord_6025826, baseEnd_6025826] using wordTrace_append hprefix tailTrace_6025826
  have hstable : (prefixWord ++ tailWord_6025826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025826).length < 2 ^ (prefixWord ++ tailWord_6025826).sum := by decide
  have hdescent : baseEnd_6025826 < baseStart_6025826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025829 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 4]
def baseStart_6025829 : Nat := 118140960795 + 6025829 * 2 ^ 59
def prefixEnd_6025829 : Nat := 4983230072969 + 3 ^ 40 * 6025829 * 2
def baseEnd_6025829 : Nat := 3094146618801609650025223

theorem tailTrace_6025829 : CollatzResearch.WordTrace tailWord_6025829 prefixEnd_6025829 3094146618801609650025223 := by
  unfold tailWord_6025829
  simp only [CollatzResearch.WordTrace]
  refine ⟨219780039286458137505112541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146520026190972091670075027 219780039286458137505112541)
  ·
    refine ⟨82417514732421801564417203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219780039286458137505112541 82417514732421801564417203)
    ·
      refine ⟨123626272098632702346625805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82417514732421801564417203 123626272098632702346625805)
      ·
        refine ⟨46359852036987263379984677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123626272098632702346625805 46359852036987263379984677)
        ·
          refine ⟨8692472256935111883747127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46359852036987263379984677 8692472256935111883747127)
          ·
            refine ⟨13038708385402667825620691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692472256935111883747127 13038708385402667825620691)
            ·
              refine ⟨19558062578104001738431037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13038708385402667825620691 19558062578104001738431037)
              ·
                refine ⟨7334273466789000651911639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19558062578104001738431037 7334273466789000651911639)
                ·
                  refine ⟨11001410200183500977867459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7334273466789000651911639 11001410200183500977867459)
                  ·
                    refine ⟨16502115300275251466801189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11001410200183500977867459 16502115300275251466801189)
                    ·
                      refine ⟨3094146618801609650025223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16502115300275251466801189 3094146618801609650025223)
                      ·
                        rfl

theorem cell23_6025829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_6025829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025829 prefixEnd_6025829 := by exact prefixLift 6025829
  have htrace : WordTrace (prefixWord ++ tailWord_6025829) baseStart_6025829 baseEnd_6025829 := by
    simpa [prefixWord, tailWord_6025829, baseEnd_6025829] using wordTrace_append hprefix tailTrace_6025829
  have hstable : (prefixWord ++ tailWord_6025829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025829).length < 2 ^ (prefixWord ++ tailWord_6025829).sum := by decide
  have hdescent : baseEnd_6025829 < baseStart_6025829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025866 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_6025866 : Nat := 118140960795 + 6025866 * 2 ^ 59
def prefixEnd_6025866 : Nat := 4983230072969 + 3 ^ 40 * 6025866 * 2
def baseEnd_6025866 : Nat := 3094165617585826005262553

theorem tailTrace_6025866 : CollatzResearch.WordTrace tailWord_6025866 prefixEnd_6025866 3094165617585826005262553 := by
  unfold tailWord_6025866
  simp only [CollatzResearch.WordTrace]
  refine ⟨54945347196831023206052363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146520925858216061882806301 54945347196831023206052363)
  ·
    refine ⟨82418020795246534809078545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54945347196831023206052363 82418020795246534809078545)
    ·
      refine ⟨61813515596434901106808909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82418020795246534809078545 61813515596434901106808909)
      ·
        refine ⟨23180068348663087915053341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61813515596434901106808909 23180068348663087915053341)
        ·
          refine ⟨8692525630748657968145003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23180068348663087915053341 8692525630748657968145003)
          ·
            refine ⟨13038788446122986952217505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692525630748657968145003 13038788446122986952217505)
            ·
              refine ⟨9779091334592240214163129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13038788446122986952217505 9779091334592240214163129)
              ·
                refine ⟨7334318500944180160622347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9779091334592240214163129 7334318500944180160622347)
                ·
                  refine ⟨11001477751416270240933521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7334318500944180160622347 11001477751416270240933521)
                  ·
                    refine ⟨8251108313562202680700141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11001477751416270240933521 8251108313562202680700141)
                    ·
                      refine ⟨3094165617585826005262553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8251108313562202680700141 3094165617585826005262553)
                      ·
                        rfl

theorem cell23_6025866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_6025866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025866 prefixEnd_6025866 := by exact prefixLift 6025866
  have htrace : WordTrace (prefixWord ++ tailWord_6025866) baseStart_6025866 baseEnd_6025866 := by
    simpa [prefixWord, tailWord_6025866, baseEnd_6025866] using wordTrace_append hprefix tailTrace_6025866
  have hstable : (prefixWord ++ tailWord_6025866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025866).length < 2 ^ (prefixWord ++ tailWord_6025866).sum := by decide
  have hdescent : baseEnd_6025866 < baseStart_6025866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025940 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6025940 : Nat := 118140960795 + 6025940 * 2 ^ 59
def prefixEnd_6025940 : Nat := 4983230072969 + 3 ^ 40 * 6025940 * 2
def baseEnd_6025940 : Nat := 3094203615154258715737213

theorem tailTrace_6025940 : CollatzResearch.WordTrace tailWord_6025940 prefixEnd_6025940 3094203615154258715737213 := by
  unfold tailWord_6025940
  simp only [CollatzResearch.WordTrace]
  refine ⟨109892043894528001731201637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146522725192704002308268849 109892043894528001731201637)
  ·
    refine ⟨20604758230224000324600307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109892043894528001731201637 20604758230224000324600307)
    ·
      refine ⟨30907137345336000486900461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20604758230224000324600307 30907137345336000486900461)
      ·
        refine ⟨11590176504501000182587673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30907137345336000486900461 11590176504501000182587673)
        ·
          refine ⟨8692632378375750136940755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11590176504501000182587673 8692632378375750136940755)
          ·
            refine ⟨13038948567563625205411133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692632378375750136940755 13038948567563625205411133)
            ·
              refine ⟨4889605712836359452029175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13038948567563625205411133 4889605712836359452029175)
              ·
                refine ⟨7334408569254539178043763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4889605712836359452029175 7334408569254539178043763)
                ·
                  refine ⟨11001612853881808767065645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7334408569254539178043763 11001612853881808767065645)
                  ·
                    refine ⟨4125604820205678287649617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11001612853881808767065645 4125604820205678287649617)
                    ·
                      refine ⟨3094203615154258715737213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125604820205678287649617 3094203615154258715737213)
                      ·
                        rfl

theorem cell23_6025940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6025940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025940 prefixEnd_6025940 := by exact prefixLift 6025940
  have htrace : WordTrace (prefixWord ++ tailWord_6025940) baseStart_6025940 baseEnd_6025940 := by
    simpa [prefixWord, tailWord_6025940, baseEnd_6025940] using wordTrace_append hprefix tailTrace_6025940
  have hstable : (prefixWord ++ tailWord_6025940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025940).length < 2 ^ (prefixWord ++ tailWord_6025940).sum := by decide
  have hdescent : baseEnd_6025940 < baseStart_6025940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025952 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 3]
def baseStart_6025952 : Nat := 118140960795 + 6025952 * 2 ^ 59
def prefixEnd_6025952 : Nat := 4983230072969 + 3 ^ 40 * 6025952 * 2
def baseEnd_6025952 : Nat := 3094209776922112668787157

theorem tailTrace_6025952 : CollatzResearch.WordTrace tailWord_6025952 prefixEnd_6025952 3094209776922112668787157 := by
  unfold tailWord_6025952
  simp only [CollatzResearch.WordTrace]
  refine ⟨109892262732506264755920055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146523016976675019674560073 109892262732506264755920055)
  ·
    refine ⟨164838394098759397133880083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109892262732506264755920055 164838394098759397133880083)
    ·
      refine ⟨247257591148139095700820125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164838394098759397133880083 247257591148139095700820125)
      ·
        refine ⟨92721596680552160887807547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247257591148139095700820125 92721596680552160887807547)
        ·
          refine ⟨139082395020828241331711321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92721596680552160887807547 139082395020828241331711321)
          ·
            refine ⟨104311796265621180998783491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139082395020828241331711321 104311796265621180998783491)
            ·
              refine ⟨156467694398431771498175237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104311796265621180998783491 156467694398431771498175237)
              ·
                refine ⟨29337692699705957155907857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156467694398431771498175237 29337692699705957155907857)
                ·
                  refine ⟨22003269524779467866930893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29337692699705957155907857 22003269524779467866930893)
                  ·
                    refine ⟨8251226071792300450099085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22003269524779467866930893 8251226071792300450099085)
                    ·
                      refine ⟨3094209776922112668787157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8251226071792300450099085 3094209776922112668787157)
                      ·
                        rfl

theorem cell23_6025952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_6025952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025952 prefixEnd_6025952 := by exact prefixLift 6025952
  have htrace : WordTrace (prefixWord ++ tailWord_6025952) baseStart_6025952 baseEnd_6025952 := by
    simpa [prefixWord, tailWord_6025952, baseEnd_6025952] using wordTrace_append hprefix tailTrace_6025952
  have hstable : (prefixWord ++ tailWord_6025952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025952).length < 2 ^ (prefixWord ++ tailWord_6025952).sum := by decide
  have hdescent : baseEnd_6025952 < baseStart_6025952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6025953 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 2, 2, 2]
def baseStart_6025953 : Nat := 118140960795 + 6025953 * 2 ^ 59
def prefixEnd_6025953 : Nat := 4983230072969 + 3 ^ 40 * 6025953 * 2
def baseEnd_6025953 : Nat := 3094210290402767164874653

theorem tailTrace_6025953 : CollatzResearch.WordTrace tailWord_6025953 prefixEnd_6025953 3094210290402767164874653 := by
  unfold tailWord_6025953
  simp only [CollatzResearch.WordTrace]
  refine ⟨219784561938008906682626513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146523041292005937788417675 219784561938008906682626513)
  ·
    refine ⟨164838421453506680011969885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219784561938008906682626513 164838421453506680011969885)
    ·
      refine ⟨61814408045065005004488707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164838421453506680011969885 61814408045065005004488707)
      ·
        refine ⟨92721612067597507506733061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61814408045065005004488707 92721612067597507506733061)
        ·
          refine ⟨17385302262674532657512449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92721612067597507506733061 17385302262674532657512449)
          ·
            refine ⟨13038976697005899493134337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17385302262674532657512449 13038976697005899493134337)
            ·
              refine ⟨9779232522754424619850753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13038976697005899493134337 9779232522754424619850753)
              ·
                refine ⟨7334424392065818464888065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9779232522754424619850753 7334424392065818464888065)
                ·
                  refine ⟨5500818294049363848666049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7334424392065818464888065 5500818294049363848666049)
                  ·
                    refine ⟨4125613720537022886499537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5500818294049363848666049 4125613720537022886499537)
                    ·
                      refine ⟨3094210290402767164874653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125613720537022886499537 3094210290402767164874653)
                      ·
                        rfl

theorem cell23_6025953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_6025953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6025953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6025953 prefixEnd_6025953 := by exact prefixLift 6025953
  have htrace : WordTrace (prefixWord ++ tailWord_6025953) baseStart_6025953 baseEnd_6025953 := by
    simpa [prefixWord, tailWord_6025953, baseEnd_6025953] using wordTrace_append hprefix tailTrace_6025953
  have hstable : (prefixWord ++ tailWord_6025953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6025953).length < 2 ^ (prefixWord ++ tailWord_6025953).sum := by decide
  have hdescent : baseEnd_6025953 < baseStart_6025953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6025953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026032 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 6]
def baseStart_6026032 : Nat := 118140960795 + 6026032 * 2 ^ 59
def prefixEnd_6026032 : Nat := 4983230072969 + 3 ^ 40 * 6026032 * 2
def baseEnd_6026032 : Nat := 343805650597163595087421

theorem tailTrace_6026032 : CollatzResearch.WordTrace tailWord_6026032 prefixEnd_6026032 343805650597163595087421 := by
  unfold tailWord_6026032
  simp only [CollatzResearch.WordTrace]
  refine ⟨109893721652361351587376175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146524962203148468783168233 109893721652361351587376175)
  ·
    refine ⟨164840582478542027381064263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109893721652361351587376175 164840582478542027381064263)
    ·
      refine ⟨247260873717813041071596395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164840582478542027381064263 247260873717813041071596395)
      ·
        refine ⟨370891310576719561607394593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247260873717813041071596395 370891310576719561607394593)
        ·
          refine ⟨278168482932539671205545945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370891310576719561607394593 278168482932539671205545945)
          ·
            refine ⟨208626362199404753404159459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278168482932539671205545945 208626362199404753404159459)
            ·
              refine ⟨312939543299107130106239189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208626362199404753404159459 312939543299107130106239189)
              ·
                refine ⟨7334520546072823361864981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 312939543299107130106239189 7334520546072823361864981)
                ·
                  refine ⟨343805650597163595087421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7334520546072823361864981 343805650597163595087421)
                  ·
                    rfl

theorem cell23_6026032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 6].length) (baseStart_6026032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026032 prefixEnd_6026032 := by exact prefixLift 6026032
  have htrace : WordTrace (prefixWord ++ tailWord_6026032) baseStart_6026032 baseEnd_6026032 := by
    simpa [prefixWord, tailWord_6026032, baseEnd_6026032] using wordTrace_append hprefix tailTrace_6026032
  have hstable : (prefixWord ++ tailWord_6026032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026032).length < 2 ^ (prefixWord ++ tailWord_6026032).sum := by decide
  have hdescent : baseEnd_6026032 < baseStart_6026032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026099 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 2, 6, 2]
def baseStart_6026099 : Nat := 118140960795 + 6026099 * 2 ^ 59
def prefixEnd_6026099 : Nat := 4983230072969 + 3 ^ 40 * 6026099 * 2
def baseEnd_6026099 : Nat := 3094285258578323593648981

theorem tailTrace_6026099 : CollatzResearch.WordTrace tailWord_6026099 prefixEnd_6026099 3094285258578323593648981 := by
  unfold tailWord_6026099
  simp only [CollatzResearch.WordTrace]
  refine ⟨219789886995479973617441351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146526591330319982411627567 219789886995479973617441351)
  ·
    refine ⟨329684830493219960426162027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219789886995479973617441351 329684830493219960426162027)
    ·
      refine ⟨494527245739829940639243041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329684830493219960426162027 494527245739829940639243041)
      ·
        refine ⟨370895434304872455479432281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494527245739829940639243041 370895434304872455479432281)
        ·
          refine ⟨278171575728654341609574211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370895434304872455479432281 278171575728654341609574211)
          ·
            refine ⟨417257363592981512414361317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278171575728654341609574211 417257363592981512414361317)
            ·
              refine ⟨78235755673684033577692747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 417257363592981512414361317 78235755673684033577692747)
              ·
                refine ⟨117353633510526050366539121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78235755673684033577692747 117353633510526050366539121)
                ·
                  refine ⟨88015225132894537774904341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117353633510526050366539121 88015225132894537774904341)
                  ·
                    refine ⟨4125713678104431458198641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88015225132894537774904341 4125713678104431458198641)
                    ·
                      refine ⟨3094285258578323593648981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125713678104431458198641 3094285258578323593648981)
                      ·
                        rfl

theorem cell23_6026099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 6, 2].length) (baseStart_6026099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026099 prefixEnd_6026099 := by exact prefixLift 6026099
  have htrace : WordTrace (prefixWord ++ tailWord_6026099) baseStart_6026099 baseEnd_6026099 := by
    simpa [prefixWord, tailWord_6026099, baseEnd_6026099] using wordTrace_append hprefix tailTrace_6026099
  have hstable : (prefixWord ++ tailWord_6026099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026099).length < 2 ^ (prefixWord ++ tailWord_6026099).sum := by decide
  have hdescent : baseEnd_6026099 < baseStart_6026099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026109 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_6026109 : Nat := 118140960795 + 6026109 * 2 ^ 59
def prefixEnd_6026109 : Nat := 4983230072969 + 3 ^ 40 * 6026109 * 2
def baseEnd_6026109 : Nat := 1031430131128289518174645

theorem tailTrace_6026109 : CollatzResearch.WordTrace tailWord_6026109 prefixEnd_6026109 1031430131128289518174645 := by
  unfold tailWord_6026109
  simp only [CollatzResearch.WordTrace]
  refine ⟨219790251725443745325305381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146526834483629163550203587 219790251725443745325305381)
  ·
    refine ⟨41210672198520702248494759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219790251725443745325305381 41210672198520702248494759)
    ·
      refine ⟨61816008297781053372742139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41210672198520702248494759 61816008297781053372742139)
      ·
        refine ⟨92724012446671580059113209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61816008297781053372742139 92724012446671580059113209)
        ·
          refine ⟨69543009335003685044334907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92724012446671580059113209 69543009335003685044334907)
          ·
            refine ⟨104314514002505527566502361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69543009335003685044334907 104314514002505527566502361)
            ·
              refine ⟨78235885501879145674876771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104314514002505527566502361 78235885501879145674876771)
              ·
                refine ⟨117353828252818718512315157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78235885501879145674876771 117353828252818718512315157)
                ·
                  refine ⟨5500960699350877430264773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117353828252818718512315157 5500960699350877430264773)
                  ·
                    refine ⟨1031430131128289518174645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5500960699350877430264773 1031430131128289518174645)
                    ·
                      rfl

theorem cell23_6026109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_6026109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026109 prefixEnd_6026109 := by exact prefixLift 6026109
  have htrace : WordTrace (prefixWord ++ tailWord_6026109) baseStart_6026109 baseEnd_6026109 := by
    simpa [prefixWord, tailWord_6026109, baseEnd_6026109] using wordTrace_append hprefix tailTrace_6026109
  have hstable : (prefixWord ++ tailWord_6026109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026109).length < 2 ^ (prefixWord ++ tailWord_6026109).sum := by decide
  have hdescent : baseEnd_6026109 < baseStart_6026109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026112 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_6026112 : Nat := 118140960795 + 6026112 * 2 ^ 59
def prefixEnd_6026112 : Nat := 4983230072969 + 3 ^ 40 * 6026112 * 2
def baseEnd_6026112 : Nat := 3094291933826832042786421

theorem tailTrace_6026112 : CollatzResearch.WordTrace tailWord_6026112 prefixEnd_6026112 3094291933826832042786421 := by
  unfold tailWord_6026112
  simp only [CollatzResearch.WordTrace]
  refine ⟨109895180572216438418832295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146526907429621917891776393 109895180572216438418832295)
  ·
    refine ⟨164842770858324657628248443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109895180572216438418832295 164842770858324657628248443)
    ·
      refine ⟨247264156287486986442372665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164842770858324657628248443 247264156287486986442372665)
      ·
        refine ⟨185448117215615239831779499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247264156287486986442372665 185448117215615239831779499)
        ·
          refine ⟨278172175823422859747669249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185448117215615239831779499 278172175823422859747669249)
          ·
            refine ⟨208629131867567144810751937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278172175823422859747669249 208629131867567144810751937)
            ·
              refine ⟨156471848900675358608063953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208629131867567144810751937 156471848900675358608063953)
              ·
                refine ⟨117353886675506518956047965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156471848900675358608063953 117353886675506518956047965)
                ·
                  refine ⟨44007707503314944608517987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117353886675506518956047965 44007707503314944608517987)
                  ·
                    refine ⟨66011561254972416912776981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44007707503314944608517987 66011561254972416912776981)
                    ·
                      refine ⟨3094291933826832042786421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66011561254972416912776981 3094291933826832042786421)
                      ·
                        rfl

theorem cell23_6026112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_6026112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026112 prefixEnd_6026112 := by exact prefixLift 6026112
  have htrace : WordTrace (prefixWord ++ tailWord_6026112) baseStart_6026112 baseEnd_6026112 := by
    simpa [prefixWord, tailWord_6026112, baseEnd_6026112] using wordTrace_append hprefix tailTrace_6026112
  have hstable : (prefixWord ++ tailWord_6026112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026112).length < 2 ^ (prefixWord ++ tailWord_6026112).sum := by decide
  have hdescent : baseEnd_6026112 < baseStart_6026112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026146 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_6026146 : Nat := 118140960795 + 6026146 * 2 ^ 59
def prefixEnd_6026146 : Nat := 4983230072969 + 3 ^ 40 * 6026146 * 2
def baseEnd_6026146 : Nat := 3094309392169084909761265

theorem tailTrace_6026146 : CollatzResearch.WordTrace tailWord_6026146 prefixEnd_6026146 3094309392169084909761265 := by
  unfold tailWord_6026146
  simp only [CollatzResearch.WordTrace]
  refine ⟨54947900306577425161100573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146527734150873133762934861 54947900306577425161100573)
  ·
    refine ⟨20605462614966534435412715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54947900306577425161100573 20605462614966534435412715)
    ·
      refine ⟨30908193922449801653119073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20605462614966534435412715 30908193922449801653119073)
      ·
        refine ⟨23181145441837351239839305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30908193922449801653119073 23181145441837351239839305)
        ·
          refine ⟨17385859081378013429879479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23181145441837351239839305 17385859081378013429879479)
          ·
            refine ⟨26078788622067020144819219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17385859081378013429879479 26078788622067020144819219)
            ·
              refine ⟨39118182933100530217228829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26078788622067020144819219 39118182933100530217228829)
              ·
                refine ⟨14669318599912698831460811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39118182933100530217228829 14669318599912698831460811)
                ·
                  refine ⟨22003977899869048247191217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14669318599912698831460811 22003977899869048247191217)
                  ·
                    refine ⟨16502983424901786185393413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22003977899869048247191217 16502983424901786185393413)
                    ·
                      refine ⟨3094309392169084909761265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16502983424901786185393413 3094309392169084909761265)
                      ·
                        rfl

theorem cell23_6026146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_6026146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026146 prefixEnd_6026146 := by exact prefixLift 6026146
  have htrace : WordTrace (prefixWord ++ tailWord_6026146) baseStart_6026146 baseEnd_6026146 := by
    simpa [prefixWord, tailWord_6026146, baseEnd_6026146] using wordTrace_append hprefix tailTrace_6026146
  have hstable : (prefixWord ++ tailWord_6026146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026146).length < 2 ^ (prefixWord ++ tailWord_6026146).sum := by decide
  have hdescent : baseEnd_6026146 < baseStart_6026146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026183 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_6026183 : Nat := 118140960795 + 6026183 * 2 ^ 59
def prefixEnd_6026183 : Nat := 4983230072969 + 3 ^ 40 * 6026183 * 2
def baseEnd_6026183 : Nat := 3094328390953301264998595

theorem tailTrace_6026183 : CollatzResearch.WordTrace tailWord_6026183 prefixEnd_6026183 3094328390953301264998595 := by
  unfold tailWord_6026183
  simp only [CollatzResearch.WordTrace]
  refine ⟨219792950727175655963499203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146528633818117103975666135 219792950727175655963499203)
  ·
    refine ⟨329689426090763483945248805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219792950727175655963499203 329689426090763483945248805)
    ·
      refine ⟨61816767392018153239734151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329689426090763483945248805 61816767392018153239734151)
      ·
        refine ⟨92725151088027229859601227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61816767392018153239734151 92725151088027229859601227)
        ·
          refine ⟨139087726632040844789401841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92725151088027229859601227 139087726632040844789401841)
          ·
            refine ⟨104315794974030633592051381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139087726632040844789401841 104315794974030633592051381)
            ·
              refine ⟨9779605778815371899254817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104315794974030633592051381 9779605778815371899254817)
              ·
                refine ⟨7334704334111528924441113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9779605778815371899254817 7334704334111528924441113)
                ·
                  refine ⟨5501028250583646693330835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7334704334111528924441113 5501028250583646693330835)
                  ·
                    refine ⟨8251542375875470039996253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5501028250583646693330835 8251542375875470039996253)
                    ·
                      refine ⟨3094328390953301264998595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8251542375875470039996253 3094328390953301264998595)
                      ·
                        rfl

theorem cell23_6026183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_6026183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026183 prefixEnd_6026183 := by exact prefixLift 6026183
  have htrace : WordTrace (prefixWord ++ tailWord_6026183) baseStart_6026183 baseEnd_6026183 := by
    simpa [prefixWord, tailWord_6026183, baseEnd_6026183] using wordTrace_append hprefix tailTrace_6026183
  have hstable : (prefixWord ++ tailWord_6026183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026183).length < 2 ^ (prefixWord ++ tailWord_6026183).sum := by decide
  have hdescent : baseEnd_6026183 < baseStart_6026183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026200 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 2, 1, 3]
def baseStart_6026200 : Nat := 118140960795 + 6026200 * 2 ^ 59
def prefixEnd_6026200 : Nat := 4983230072969 + 3 ^ 40 * 6026200 * 2
def baseEnd_6026200 : Nat := 3094337120124427698486017

theorem tailTrace_6026200 : CollatzResearch.WordTrace tailWord_6026200 prefixEnd_6026200 3094337120124427698486017 := by
  unfold tailWord_6026200
  simp only [CollatzResearch.WordTrace]
  refine ⟨109896785384057033933434027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146529047178742711911245369 109896785384057033933434027)
  ·
    refine ⟨164845178076085550900151041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109896785384057033933434027 164845178076085550900151041)
    ·
      refine ⟨123633883557064163175113281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164845178076085550900151041 123633883557064163175113281)
      ·
        refine ⟨92725412667798122381334961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123633883557064163175113281 92725412667798122381334961)
        ·
          refine ⟨69544059500848591786001221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92725412667798122381334961 69544059500848591786001221)
          ·
            refine ⟨13039511156409110959875229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69544059500848591786001221 13039511156409110959875229)
            ·
              refine ⟨4889816683653416609953211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13039511156409110959875229 4889816683653416609953211)
              ·
                refine ⟨7334725025480124914929817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4889816683653416609953211 7334725025480124914929817)
                ·
                  refine ⟨5501043769110093686197363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7334725025480124914929817 5501043769110093686197363)
                  ·
                    refine ⟨8251565653665140529296045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5501043769110093686197363 8251565653665140529296045)
                    ·
                      refine ⟨3094337120124427698486017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8251565653665140529296045 3094337120124427698486017)
                      ·
                        rfl

theorem cell23_6026200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_6026200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026200 prefixEnd_6026200 := by exact prefixLift 6026200
  have htrace : WordTrace (prefixWord ++ tailWord_6026200) baseStart_6026200 baseEnd_6026200 := by
    simpa [prefixWord, tailWord_6026200, baseEnd_6026200] using wordTrace_append hprefix tailTrace_6026200
  have hstable : (prefixWord ++ tailWord_6026200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026200).length < 2 ^ (prefixWord ++ tailWord_6026200).sum := by decide
  have hdescent : baseEnd_6026200 < baseStart_6026200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026209 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_6026209 : Nat := 118140960795 + 6026209 * 2 ^ 59
def prefixEnd_6026209 : Nat := 4983230072969 + 3 ^ 40 * 6026209 * 2
def baseEnd_6026209 : Nat := 3094341741450318163273475

theorem tailTrace_6026209 : CollatzResearch.WordTrace tailWord_6026209 prefixEnd_6026209 3094341741450318163273475 := by
  unfold tailWord_6026209
  simp only [CollatzResearch.WordTrace]
  refine ⟨219793899025081462403945681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146529266016720974935963787 219793899025081462403945681)
  ·
    refine ⟨164845424268811096802959261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219793899025081462403945681 164845424268811096802959261)
    ·
      refine ⟨61817034100804161301109723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164845424268811096802959261 61817034100804161301109723)
      ·
        refine ⟨92725551151206241951664585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61817034100804161301109723 92725551151206241951664585)
        ·
          refine ⟨69544163363404681463748439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92725551151206241951664585 69544163363404681463748439)
          ·
            refine ⟨104316245045107022195622659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69544163363404681463748439 104316245045107022195622659)
            ·
              refine ⟨156474367567660533293433989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104316245045107022195622659 156474367567660533293433989)
              ·
                refine ⟨29338943918936349992518873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156474367567660533293433989 29338943918936349992518873)
                ·
                  refine ⟨22004207939202262494389155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29338943918936349992518873 22004207939202262494389155)
                  ·
                    refine ⟨33006311908803393741583733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22004207939202262494389155 33006311908803393741583733)
                    ·
                      refine ⟨3094341741450318163273475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33006311908803393741583733 3094341741450318163273475)
                      ·
                        rfl

theorem cell23_6026209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_6026209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026209 prefixEnd_6026209 := by exact prefixLift 6026209
  have htrace : WordTrace (prefixWord ++ tailWord_6026209) baseStart_6026209 baseEnd_6026209 := by
    simpa [prefixWord, tailWord_6026209, baseEnd_6026209] using wordTrace_append hprefix tailTrace_6026209
  have hstable : (prefixWord ++ tailWord_6026209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026209).length < 2 ^ (prefixWord ++ tailWord_6026209).sum := by decide
  have hdescent : baseEnd_6026209 < baseStart_6026209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026223 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 4, 2, 2]
def baseStart_6026223 : Nat := 118140960795 + 6026223 * 2 ^ 59
def prefixEnd_6026223 : Nat := 4983230072969 + 3 ^ 40 * 6026223 * 2
def baseEnd_6026223 : Nat := 3094348930179481108498411

theorem tailTrace_6026223 : CollatzResearch.WordTrace tailWord_6026223 prefixEnd_6026223 3094348930179481108498411 := by
  unfold tailWord_6026223
  simp only [CollatzResearch.WordTrace]
  refine ⟨219794409647030742794955323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146529606431353828529970215 219794409647030742794955323)
  ·
    refine ⟨329691614470546114192432985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219794409647030742794955323 329691614470546114192432985)
    ·
      refine ⟨247268710852909585644324739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329691614470546114192432985 247268710852909585644324739)
      ·
        refine ⟨370903066279364378466487109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247268710852909585644324739 370903066279364378466487109)
        ·
          refine ⟨69544324927380820962466333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370903066279364378466487109 69544324927380820962466333)
          ·
            refine ⟨26079121847767807860924875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69544324927380820962466333 26079121847767807860924875)
            ·
              refine ⟨39118682771651711791387313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26079121847767807860924875 39118682771651711791387313)
              ·
                refine ⟨29339012078738783843540485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39118682771651711791387313 29339012078738783843540485)
                ·
                  refine ⟨5501064764763521970663841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29339012078738783843540485 5501064764763521970663841)
                  ·
                    refine ⟨4125798573572641477997881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5501064764763521970663841 4125798573572641477997881)
                    ·
                      refine ⟨3094348930179481108498411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125798573572641477997881 3094348930179481108498411)
                      ·
                        rfl

theorem cell23_6026223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 2, 2].length) (baseStart_6026223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026223 prefixEnd_6026223 := by exact prefixLift 6026223
  have htrace : WordTrace (prefixWord ++ tailWord_6026223) baseStart_6026223 baseEnd_6026223 := by
    simpa [prefixWord, tailWord_6026223, baseEnd_6026223] using wordTrace_append hprefix tailTrace_6026223
  have hstable : (prefixWord ++ tailWord_6026223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026223).length < 2 ^ (prefixWord ++ tailWord_6026223).sum := by decide
  have hdescent : baseEnd_6026223 < baseStart_6026223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026259 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 6, 5]
def baseStart_6026259 : Nat := 118140960795 + 6026259 * 2 ^ 59
def prefixEnd_6026259 : Nat := 4983230072969 + 3 ^ 40 * 6026259 * 2
def baseEnd_6026259 : Nat := 1031455805161014322549415

theorem tailTrace_6026259 : CollatzResearch.WordTrace tailWord_6026259 prefixEnd_6026259 1031455805161014322549415 := by
  unfold tailWord_6026259
  simp only [CollatzResearch.WordTrace]
  refine ⟨219795722674900320943265831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146530481783266880628843887 219795722674900320943265831)
  ·
    refine ⟨329693584012350481414898747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219795722674900320943265831 329693584012350481414898747)
    ·
      refine ⟨494540376018525722122348121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329693584012350481414898747 494540376018525722122348121)
      ·
        refine ⟨370905282013894291591761091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494540376018525722122348121 370905282013894291591761091)
        ·
          refine ⟨556357923020841437387641637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370905282013894291591761091 556357923020841437387641637)
          ·
            refine ⟨104317110566407769510182807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 556357923020841437387641637 104317110566407769510182807)
            ·
              refine ⟨156475665849611654265274211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104317110566407769510182807 156475665849611654265274211)
              ·
                refine ⟨234713498774417481397911317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156475665849611654265274211 234713498774417481397911317)
                ·
                  refine ⟨11002195255050819440527093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 234713498774417481397911317 11002195255050819440527093)
                  ·
                    refine ⟨1031455805161014322549415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11002195255050819440527093 1031455805161014322549415)
                    ·
                      rfl

theorem cell23_6026259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 5].length) (baseStart_6026259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026259 prefixEnd_6026259 := by exact prefixLift 6026259
  have htrace : WordTrace (prefixWord ++ tailWord_6026259) baseStart_6026259 baseEnd_6026259 := by
    simpa [prefixWord, tailWord_6026259, baseEnd_6026259] using wordTrace_append hprefix tailTrace_6026259
  have hstable : (prefixWord ++ tailWord_6026259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026259).length < 2 ^ (prefixWord ++ tailWord_6026259).sum := by decide
  have hdescent : baseEnd_6026259 < baseStart_6026259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026286 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6026286 : Nat := 118140960795 + 6026286 * 2 ^ 59
def prefixEnd_6026286 : Nat := 4983230072969 + 3 ^ 40 * 6026286 * 2
def baseEnd_6026286 : Nat := 3094381279460714362010621

theorem tailTrace_6026286 : CollatzResearch.WordTrace tailWord_6026286 prefixEnd_6026286 3094381279460714362010621 := by
  unfold tailWord_6026286
  simp only [CollatzResearch.WordTrace]
  refine ⟨27474588430725313069312339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146531138297201669702999141 27474588430725313069312339)
  ·
    refine ⟨41211882646087969603968509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27474588430725313069312339 41211882646087969603968509)
    ·
      refine ⟨15454455992282988601488191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41211882646087969603968509 15454455992282988601488191)
      ·
        refine ⟨23181683988424482902232287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15454455992282988601488191 23181683988424482902232287)
        ·
          refine ⟨34772525982636724353348431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23181683988424482902232287 34772525982636724353348431)
          ·
            refine ⟨52158788973955086530022647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34772525982636724353348431 52158788973955086530022647)
            ·
              refine ⟨78238183460932629795033971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52158788973955086530022647 78238183460932629795033971)
              ·
                refine ⟨117357275191398944692550957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78238183460932629795033971 117357275191398944692550957)
                ·
                  refine ⟨44008978196774604259706609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117357275191398944692550957 44008978196774604259706609)
                  ·
                    refine ⟨33006733647580953194779957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44008978196774604259706609 33006733647580953194779957)
                    ·
                      refine ⟨3094381279460714362010621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33006733647580953194779957 3094381279460714362010621)
                      ·
                        rfl

theorem cell23_6026286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6026286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026286 prefixEnd_6026286 := by exact prefixLift 6026286
  have htrace : WordTrace (prefixWord ++ tailWord_6026286) baseStart_6026286 baseEnd_6026286 := by
    simpa [prefixWord, tailWord_6026286, baseEnd_6026286] using wordTrace_append hprefix tailTrace_6026286
  have hstable : (prefixWord ++ tailWord_6026286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026286).length < 2 ^ (prefixWord ++ tailWord_6026286).sum := by decide
  have hdescent : baseEnd_6026286 < baseStart_6026286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026316 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 1, 4, 3]
def baseStart_6026316 : Nat := 118140960795 + 6026316 * 2 ^ 59
def prefixEnd_6026316 : Nat := 4983230072969 + 3 ^ 40 * 6026316 * 2
def baseEnd_6026316 : Nat := 3094396683880349244635483

theorem tailTrace_6026316 : CollatzResearch.WordTrace tailWord_6026316 prefixEnd_6026316 3094396683880349244635483 := by
  unfold tailWord_6026316
  simp only [CollatzResearch.WordTrace]
  refine ⟨109898900817846909839045401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146531867757129213118727201 109898900817846909839045401)
  ·
    refine ⟨82424175613385182379284051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109898900817846909839045401 82424175613385182379284051)
    ·
      refine ⟨123636263420077773568926077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82424175613385182379284051 123636263420077773568926077)
      ·
        refine ⟨46363598782529165088347279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123636263420077773568926077 46363598782529165088347279)
        ·
          refine ⟨69545398173793747632520919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46363598782529165088347279 69545398173793747632520919)
          ·
            refine ⟨104318097260690621448781379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69545398173793747632520919 104318097260690621448781379)
            ·
              refine ⟨156477145891035932173172069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104318097260690621448781379 156477145891035932173172069)
              ·
                refine ⟨29339464854569237282469763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156477145891035932173172069 29339464854569237282469763)
                ·
                  refine ⟨44009197281853855923704645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29339464854569237282469763 44009197281853855923704645)
                  ·
                    refine ⟨8251724490347597985694621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44009197281853855923704645 8251724490347597985694621)
                    ·
                      refine ⟨3094396683880349244635483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8251724490347597985694621 3094396683880349244635483)
                      ·
                        rfl

theorem cell23_6026316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_6026316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026316 prefixEnd_6026316 := by exact prefixLift 6026316
  have htrace : WordTrace (prefixWord ++ tailWord_6026316) baseStart_6026316 baseEnd_6026316 := by
    simpa [prefixWord, tailWord_6026316, baseEnd_6026316] using wordTrace_append hprefix tailTrace_6026316
  have hstable : (prefixWord ++ tailWord_6026316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026316).length < 2 ^ (prefixWord ++ tailWord_6026316).sum := by decide
  have hdescent : baseEnd_6026316 < baseStart_6026316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026357 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_6026357 : Nat := 118140960795 + 6026357 * 2 ^ 59
def prefixEnd_6026357 : Nat := 4983230072969 + 3 ^ 40 * 6026357 * 2
def baseEnd_6026357 : Nat := 1031472578862394528074265

theorem tailTrace_6026357 : CollatzResearch.WordTrace tailWord_6026357 prefixEnd_6026357 1031472578862394528074265 := by
  unfold tailWord_6026357
  simp only [CollatzResearch.WordTrace]
  refine ⟨219799297028545283680333325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146532864685696855786888883 219799297028545283680333325)
  ·
    refine ⟨82424736385704481380124997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219799297028545283680333325 82424736385704481380124997)
    ·
      refine ⟨15454638072319590258773437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82424736385704481380124997 15454638072319590258773437)
      ·
        refine ⟨5795489277119846347040039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15454638072319590258773437 5795489277119846347040039)
        ·
          refine ⟨8693233915679769520560059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5795489277119846347040039 8693233915679769520560059)
          ·
            refine ⟨13039850873519654280840089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8693233915679769520560059 13039850873519654280840089)
            ·
              refine ⟨9779888155139740710630067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13039850873519654280840089 9779888155139740710630067)
              ·
                refine ⟨14669832232709611065945101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9779888155139740710630067 14669832232709611065945101)
                ·
                  refine ⟨5501187087266104149729413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14669832232709611065945101 5501187087266104149729413)
                  ·
                    refine ⟨1031472578862394528074265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5501187087266104149729413 1031472578862394528074265)
                    ·
                      rfl

theorem cell23_6026357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_6026357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026357 prefixEnd_6026357 := by exact prefixLift 6026357
  have htrace : WordTrace (prefixWord ++ tailWord_6026357) baseStart_6026357 baseEnd_6026357 := by
    simpa [prefixWord, tailWord_6026357, baseEnd_6026357] using wordTrace_append hprefix tailTrace_6026357
  have hstable : (prefixWord ++ tailWord_6026357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026357).length < 2 ^ (prefixWord ++ tailWord_6026357).sum := by decide
  have hdescent : baseEnd_6026357 < baseStart_6026357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026407 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_6026407 : Nat := 118140960795 + 6026407 * 2 ^ 59
def prefixEnd_6026407 : Nat := 4983230072969 + 3 ^ 40 * 6026407 * 2
def baseEnd_6026407 : Nat := 3094443410619908388597565

theorem tailTrace_6026407 : CollatzResearch.WordTrace tailWord_6026407 prefixEnd_6026407 3094443410619908388597565 := by
  unfold tailWord_6026407
  simp only [CollatzResearch.WordTrace]
  refine ⟨219801120678364142219653475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146534080452242761479768983 219801120678364142219653475)
  ·
    refine ⟨329701681017546213329480213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219801120678364142219653475 329701681017546213329480213)
    ·
      refine ⟨15454766297697478749819385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 329701681017546213329480213 15454766297697478749819385)
      ·
        refine ⟨11591074723273109062364539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15454766297697478749819385 11591074723273109062364539)
        ·
          refine ⟨17386612084909663593546809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11591074723273109062364539 17386612084909663593546809)
          ·
            refine ⟨13039959063682247695160107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17386612084909663593546809 13039959063682247695160107)
            ·
              refine ⟨19559938595523371542740161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13039959063682247695160107 19559938595523371542740161)
              ·
                refine ⟨14669953946642528657055121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19559938595523371542740161 14669953946642528657055121)
                ·
                  refine ⟨11002465459981896492791341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14669953946642528657055121 11002465459981896492791341)
                  ·
                    refine ⟨4125924547493211184796753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11002465459981896492791341 4125924547493211184796753)
                    ·
                      refine ⟨3094443410619908388597565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125924547493211184796753 3094443410619908388597565)
                      ·
                        rfl

theorem cell23_6026407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_6026407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026407 prefixEnd_6026407 := by exact prefixLift 6026407
  have htrace : WordTrace (prefixWord ++ tailWord_6026407) baseStart_6026407 baseEnd_6026407 := by
    simpa [prefixWord, tailWord_6026407, baseEnd_6026407] using wordTrace_append hprefix tailTrace_6026407
  have hstable : (prefixWord ++ tailWord_6026407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026407).length < 2 ^ (prefixWord ++ tailWord_6026407).sum := by decide
  have hdescent : baseEnd_6026407 < baseStart_6026407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026416 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_6026416 : Nat := 118140960795 + 6026416 * 2 ^ 59
def prefixEnd_6026416 : Nat := 4983230072969 + 3 ^ 40 * 6026416 * 2
def baseEnd_6026416 : Nat := 3094448031945798853385023

theorem tailTrace_6026416 : CollatzResearch.WordTrace tailWord_6026416 prefixEnd_6026416 3094448031945798853385023 := by
  unfold tailWord_6026416
  simp only [CollatzResearch.WordTrace]
  refine ⟨109900724467665768378365551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146534299290221024504487401 109900724467665768378365551)
  ·
    refine ⟨164851086701498652567548327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109900724467665768378365551 164851086701498652567548327)
    ·
      refine ⟨247276630052247978851322491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164851086701498652567548327 247276630052247978851322491)
      ·
        refine ⟨370914945078371968276983737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247276630052247978851322491 370914945078371968276983737)
        ·
          refine ⟨278186208808778976207737803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370914945078371968276983737 278186208808778976207737803)
          ·
            refine ⟨417279313213168464311606705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278186208808778976207737803 417279313213168464311606705)
            ·
              refine ⟨312959484909876348233705029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417279313213168464311606705 312959484909876348233705029)
              ·
                refine ⟨58679903420601815293819693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312959484909876348233705029 58679903420601815293819693)
                ·
                  refine ⟨22004963782725680735182385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58679903420601815293819693 22004963782725680735182385)
                  ·
                    refine ⟨16503722837044260551386789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22004963782725680735182385 16503722837044260551386789)
                    ·
                      refine ⟨3094448031945798853385023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16503722837044260551386789 3094448031945798853385023)
                      ·
                        rfl

theorem cell23_6026416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_6026416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026416 prefixEnd_6026416 := by exact prefixLift 6026416
  have htrace : WordTrace (prefixWord ++ tailWord_6026416) baseStart_6026416 baseEnd_6026416 := by
    simpa [prefixWord, tailWord_6026416, baseEnd_6026416] using wordTrace_append hprefix tailTrace_6026416
  have hstable : (prefixWord ++ tailWord_6026416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026416).length < 2 ^ (prefixWord ++ tailWord_6026416).sum := by decide
  have hdescent : baseEnd_6026416 < baseStart_6026416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026423 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 3]
def baseStart_6026423 : Nat := 118140960795 + 6026423 * 2 ^ 59
def prefixEnd_6026423 : Nat := 4983230072969 + 3 ^ 40 * 6026423 * 2
def baseEnd_6026423 : Nat := 3094451626310380325997491

theorem tailTrace_6026423 : CollatzResearch.WordTrace tailWord_6026423 prefixEnd_6026423 3094451626310380325997491 := by
  unfold tailWord_6026423
  simp only [CollatzResearch.WordTrace]
  refine ⟨219801704246306176952235923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146534469497537451301490615 219801704246306176952235923)
  ·
    refine ⟨329702556369459265428353885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219801704246306176952235923 329702556369459265428353885)
    ·
      refine ⟨123638458638547224535632707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329702556369459265428353885 123638458638547224535632707)
      ·
        refine ⟨185457687957820836803449061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123638458638547224535632707 185457687957820836803449061)
        ·
          refine ⟨34773316492091406900646699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185457687957820836803449061 34773316492091406900646699)
          ·
            refine ⟨52159974738137110350970049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34773316492091406900646699 52159974738137110350970049)
            ·
              refine ⟨39119981053602832763227537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52159974738137110350970049 39119981053602832763227537)
              ·
                refine ⟨29339985790202124572420653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39119981053602832763227537 29339985790202124572420653)
                ·
                  refine ⟨11002494671325796714657745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29339985790202124572420653 11002494671325796714657745)
                  ·
                    refine ⟨8251871003494347535993309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11002494671325796714657745 8251871003494347535993309)
                    ·
                      refine ⟨3094451626310380325997491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8251871003494347535993309 3094451626310380325997491)
                      ·
                        rfl

theorem cell23_6026423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_6026423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026423 prefixEnd_6026423 := by exact prefixLift 6026423
  have htrace : WordTrace (prefixWord ++ tailWord_6026423) baseStart_6026423 baseEnd_6026423 := by
    simpa [prefixWord, tailWord_6026423, baseEnd_6026423] using wordTrace_append hprefix tailTrace_6026423
  have hstable : (prefixWord ++ tailWord_6026423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026423).length < 2 ^ (prefixWord ++ tailWord_6026423).sum := by decide
  have hdescent : baseEnd_6026423 < baseStart_6026423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026440 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_6026440 : Nat := 118140960795 + 6026440 * 2 ^ 59
def prefixEnd_6026440 : Nat := 4983230072969 + 3 ^ 40 * 6026440 * 2
def baseEnd_6026440 : Nat := 3094460355481506759484913

theorem tailTrace_6026440 : CollatzResearch.WordTrace tailWord_6026440 prefixEnd_6026440 3094460355481506759484913 := by
  unfold tailWord_6026440
  simp only [CollatzResearch.WordTrace]
  refine ⟨109901162143622294427802387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146534882858163059237069849 109901162143622294427802387)
  ·
    refine ⟨164851743215433441641703581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109901162143622294427802387 164851743215433441641703581)
    ·
      refine ⟨61819403705787540615638843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164851743215433441641703581 61819403705787540615638843)
      ·
        refine ⟨92729105558681310923458265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61819403705787540615638843 92729105558681310923458265)
        ·
          refine ⟨69546829169010983192593699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92729105558681310923458265 69546829169010983192593699)
          ·
            refine ⟨104320243753516474788890549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69546829169010983192593699 104320243753516474788890549)
            ·
              refine ⟨9780022851892169511458489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104320243753516474788890549 9780022851892169511458489)
              ·
                refine ⟨7335017138919127133593867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9780022851892169511458489 7335017138919127133593867)
                ·
                  refine ⟨11002525708378690700390801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7335017138919127133593867 11002525708378690700390801)
                  ·
                    refine ⟨8251894281284018025293101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11002525708378690700390801 8251894281284018025293101)
                    ·
                      refine ⟨3094460355481506759484913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8251894281284018025293101 3094460355481506759484913)
                      ·
                        rfl

theorem cell23_6026440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_6026440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026440 prefixEnd_6026440 := by exact prefixLift 6026440
  have htrace : WordTrace (prefixWord ++ tailWord_6026440) baseStart_6026440 baseEnd_6026440 := by
    simpa [prefixWord, tailWord_6026440, baseEnd_6026440] using wordTrace_append hprefix tailTrace_6026440
  have hstable : (prefixWord ++ tailWord_6026440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026440).length < 2 ^ (prefixWord ++ tailWord_6026440).sum := by decide
  have hdescent : baseEnd_6026440 < baseStart_6026440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026471 : List Nat := [1, 1, 5, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_6026471 : Nat := 118140960795 + 6026471 * 2 ^ 59
def prefixEnd_6026471 : Nat := 4983230072969 + 3 ^ 40 * 6026471 * 2
def baseEnd_6026471 : Nat := 3094476273381796138197271

theorem tailTrace_6026471 : CollatzResearch.WordTrace tailWord_6026471 prefixEnd_6026471 3094476273381796138197271 := by
  unfold tailWord_6026471
  simp only [CollatzResearch.WordTrace]
  refine ⟨219803454950132281149983267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146535636633421520766655511 219803454950132281149983267)
  ·
    refine ⟨329705182425198421724974901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219803454950132281149983267 329705182425198421724974901)
    ·
      refine ⟨30909860852362352036716397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 329705182425198421724974901 30909860852362352036716397)
      ·
        refine ⟨11591197819635882013768649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30909860852362352036716397 11591197819635882013768649)
        ·
          refine ⟨8693398364726911510326487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11591197819635882013768649 8693398364726911510326487)
          ·
            refine ⟨13040097547090367265489731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8693398364726911510326487 13040097547090367265489731)
            ·
              refine ⟨19560146320635550898234597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13040097547090367265489731 19560146320635550898234597)
              ·
                refine ⟨3667527435119165793418987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19560146320635550898234597 3667527435119165793418987)
                ·
                  refine ⟨5501291152678748690128481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3667527435119165793418987 5501291152678748690128481)
                  ·
                    refine ⟨4125968364509061517596361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5501291152678748690128481 4125968364509061517596361)
                    ·
                      refine ⟨3094476273381796138197271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4125968364509061517596361 3094476273381796138197271)
                      ·
                        rfl

theorem cell23_6026471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_6026471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026471 prefixEnd_6026471 := by exact prefixLift 6026471
  have htrace : WordTrace (prefixWord ++ tailWord_6026471) baseStart_6026471 baseEnd_6026471 := by
    simpa [prefixWord, tailWord_6026471, baseEnd_6026471] using wordTrace_append hprefix tailTrace_6026471
  have hstable : (prefixWord ++ tailWord_6026471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026471).length < 2 ^ (prefixWord ++ tailWord_6026471).sum := by decide
  have hdescent : baseEnd_6026471 < baseStart_6026471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026533 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 7]
def baseStart_6026533 : Nat := 118140960795 + 6026533 * 2 ^ 59
def prefixEnd_6026533 : Nat := 4983230072969 + 3 ^ 40 * 6026533 * 2
def baseEnd_6026533 : Nat := 343834234353597210624665

theorem tailTrace_6026533 : CollatzResearch.WordTrace tailWord_6026533 prefixEnd_6026533 343834234353597210624665 := by
  unfold tailWord_6026533
  simp only [CollatzResearch.WordTrace]
  refine ⟨219805716275907665738740253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146537144183938443825826835 219805716275907665738740253)
  ·
    refine ⟨82427143603465374652027595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219805716275907665738740253 82427143603465374652027595)
    ·
      refine ⟨123640715405198061978041393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82427143603465374652027595 123640715405198061978041393)
      ·
        refine ⟨92730536553898546483531045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123640715405198061978041393 92730536553898546483531045)
        ·
          refine ⟨17386975603855977465662071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92730536553898546483531045 17386975603855977465662071)
          ·
            refine ⟨26080463405783966198493107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17386975603855977465662071 26080463405783966198493107)
            ·
              refine ⟨39120695108675949297739661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26080463405783966198493107 39120695108675949297739661)
              ·
                refine ⟨14670260665753480986652373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39120695108675949297739661 14670260665753480986652373)
                ·
                  refine ⟨343834234353597210624665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14670260665753480986652373 343834234353597210624665)
                  ·
                    rfl

theorem cell23_6026533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_6026533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026533 prefixEnd_6026533 := by exact prefixLift 6026533
  have htrace : WordTrace (prefixWord ++ tailWord_6026533) baseStart_6026533 baseEnd_6026533 := by
    simpa [prefixWord, tailWord_6026533, baseEnd_6026533] using wordTrace_append hprefix tailTrace_6026533
  have hstable : (prefixWord ++ tailWord_6026533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026533).length < 2 ^ (prefixWord ++ tailWord_6026533).sum := by decide
  have hdescent : baseEnd_6026533 < baseStart_6026533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026544 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 2, 2, 2]
def baseStart_6026544 : Nat := 118140960795 + 6026544 * 2 ^ 59
def prefixEnd_6026544 : Nat := 4983230072969 + 3 ^ 40 * 6026544 * 2
def baseEnd_6026544 : Nat := 3094513757469574352584435

theorem tailTrace_6026544 : CollatzResearch.WordTrace tailWord_6026544 prefixEnd_6026544 3094513757469574352584435 := by
  unfold tailWord_6026544
  simp only [CollatzResearch.WordTrace]
  refine ⟨109903058739433907308695343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146537411652578543078260457 109903058739433907308695343)
  ·
    refine ⟨164854588109150860963043015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109903058739433907308695343 164854588109150860963043015)
    ·
      refine ⟨247281882163726291444564523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164854588109150860963043015 247281882163726291444564523)
      ·
        refine ⟨370922823245589437166846785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247281882163726291444564523 370922823245589437166846785)
        ·
          refine ⟨278192117434192077875135089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370922823245589437166846785 278192117434192077875135089)
          ·
            refine ⟨208644088075644058406351317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278192117434192077875135089 208644088075644058406351317)
            ·
              refine ⟨4890095814272907618898859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 208644088075644058406351317 4890095814272907618898859)
              ·
                refine ⟨7335143721409361428348289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4890095814272907618898859 7335143721409361428348289)
                ·
                  refine ⟨5501357791057021071261217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7335143721409361428348289 5501357791057021071261217)
                  ·
                    refine ⟨4126018343292765803445913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5501357791057021071261217 4126018343292765803445913)
                    ·
                      refine ⟨3094513757469574352584435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126018343292765803445913 3094513757469574352584435)
                      ·
                        rfl

theorem cell23_6026544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 2, 2, 2].length) (baseStart_6026544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026544 prefixEnd_6026544 := by exact prefixLift 6026544
  have htrace : WordTrace (prefixWord ++ tailWord_6026544) baseStart_6026544 baseEnd_6026544 := by
    simpa [prefixWord, tailWord_6026544, baseEnd_6026544] using wordTrace_append hprefix tailTrace_6026544
  have hstable : (prefixWord ++ tailWord_6026544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026544).length < 2 ^ (prefixWord ++ tailWord_6026544).sum := by decide
  have hdescent : baseEnd_6026544 < baseStart_6026544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026563 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 2, 5]
def baseStart_6026563 : Nat := 118140960795 + 6026563 * 2 ^ 59
def prefixEnd_6026563 : Nat := 4983230072969 + 3 ^ 40 * 6026563 * 2
def baseEnd_6026563 : Nat := 1031507837867336592748949

theorem tailTrace_6026563 : CollatzResearch.WordTrace tailWord_6026563 prefixEnd_6026563 1031507837867336592748949 := by
  unfold tailWord_6026563
  simp only [CollatzResearch.WordTrace]
  refine ⟨219806810465798980862332343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146537873643865987241554895 219806810465798980862332343)
  ·
    refine ⟨329710215698698471293498515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219806810465798980862332343 329710215698698471293498515)
    ·
      refine ⟨494565323548047706940247773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329710215698698471293498515 494565323548047706940247773)
      ·
        refine ⟨185461996330517890102592915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494565323548047706940247773 185461996330517890102592915)
        ·
          refine ⟨278192994495776835153889373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185461996330517890102592915 278192994495776835153889373)
          ·
            refine ⟨104322372935916313182708515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278192994495776835153889373 104322372935916313182708515)
            ·
              refine ⟨156483559403874469774062773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104322372935916313182708515 156483559403874469774062773)
              ·
                refine ⟨14670333694113231541318385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156483559403874469774062773 14670333694113231541318385)
                ·
                  refine ⟨11002750270584923655988789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14670333694113231541318385 11002750270584923655988789)
                  ·
                    refine ⟨1031507837867336592748949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11002750270584923655988789 1031507837867336592748949)
                    ·
                      rfl

theorem cell23_6026563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 5].length) (baseStart_6026563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026563 prefixEnd_6026563 := by exact prefixLift 6026563
  have htrace : WordTrace (prefixWord ++ tailWord_6026563) baseStart_6026563 baseEnd_6026563 := by
    simpa [prefixWord, tailWord_6026563, baseEnd_6026563] using wordTrace_append hprefix tailTrace_6026563
  have hstable : (prefixWord ++ tailWord_6026563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026563).length < 2 ^ (prefixWord ++ tailWord_6026563).sum := by decide
  have hdescent : baseEnd_6026563 < baseStart_6026563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026567 : List Nat := [1, 1, 4, 1, 2, 5, 1, 3, 5]
def baseStart_6026567 : Nat := 118140960795 + 6026567 * 2 ^ 59
def prefixEnd_6026567 : Nat := 4983230072969 + 3 ^ 40 * 6026567 * 2
def baseEnd_6026567 : Nat := 343836174169403084732981

theorem tailTrace_6026567 : CollatzResearch.WordTrace tailWord_6026567 prefixEnd_6026567 343836174169403084732981 := by
  unfold tailWord_6026567
  simp only [CollatzResearch.WordTrace]
  refine ⟨219806956357784489545477955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146537970905189659696985303 219806956357784489545477955)
  ·
    refine ⟨329710434536676734318216933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219806956357784489545477955 329710434536676734318216933)
    ·
      refine ⟨61820706475626887684665675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329710434536676734318216933 61820706475626887684665675)
      ·
        refine ⟨92731059713440331526998513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61820706475626887684665675 92731059713440331526998513)
        ·
          refine ⟨69548294785080248645248885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92731059713440331526998513 69548294785080248645248885)
          ·
            refine ⟨6520152636101273310492083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69548294785080248645248885 6520152636101273310492083)
            ·
              refine ⟨9780228954151909965738125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6520152636101273310492083 9780228954151909965738125)
              ·
                refine ⟨3667585857806966237151797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9780228954151909965738125 3667585857806966237151797)
                ·
                  refine ⟨343836174169403084732981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3667585857806966237151797 343836174169403084732981)
                  ·
                    rfl

theorem cell23_6026567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 5].length) (baseStart_6026567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026567 prefixEnd_6026567 := by exact prefixLift 6026567
  have htrace : WordTrace (prefixWord ++ tailWord_6026567) baseStart_6026567 baseEnd_6026567 := by
    simpa [prefixWord, tailWord_6026567, baseEnd_6026567] using wordTrace_append hprefix tailTrace_6026567
  have hstable : (prefixWord ++ tailWord_6026567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026567).length < 2 ^ (prefixWord ++ tailWord_6026567).sum := by decide
  have hdescent : baseEnd_6026567 < baseStart_6026567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026580 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_6026580 : Nat := 118140960795 + 6026580 * 2 ^ 59
def prefixEnd_6026580 : Nat := 4983230072969 + 3 ^ 40 * 6026580 * 2
def baseEnd_6026580 : Nat := 1031510747591045403911423

theorem tailTrace_6026580 : CollatzResearch.WordTrace tailWord_6026580 prefixEnd_6026580 1031510747591045403911423 := by
  unfold tailWord_6026580
  simp only [CollatzResearch.WordTrace]
  refine ⟨109903715253368696382850597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146538287004491595177134129 109903715253368696382850597)
  ·
    refine ⟨20606946610006630571784487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109903715253368696382850597 20606946610006630571784487)
    ·
      refine ⟨30910419915009945857676731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20606946610006630571784487 30910419915009945857676731)
      ·
        refine ⟨46365629872514918786515097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30910419915009945857676731 46365629872514918786515097)
        ·
          refine ⟨34774222404386189089886323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46365629872514918786515097 34774222404386189089886323)
          ·
            refine ⟨52161333606579283634829485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34774222404386189089886323 52161333606579283634829485)
            ·
              refine ⟨19560500102467231363061057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52161333606579283634829485 19560500102467231363061057)
              ·
                refine ⟨14670375076850423522295793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19560500102467231363061057 14670375076850423522295793)
                ·
                  refine ⟨11002781307637817641721845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14670375076850423522295793 11002781307637817641721845)
                  ·
                    refine ⟨1031510747591045403911423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11002781307637817641721845 1031510747591045403911423)
                    ·
                      rfl

theorem cell23_6026580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_6026580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026580 prefixEnd_6026580 := by exact prefixLift 6026580
  have htrace : WordTrace (prefixWord ++ tailWord_6026580) baseStart_6026580 baseEnd_6026580 := by
    simpa [prefixWord, tailWord_6026580, baseEnd_6026580] using wordTrace_append hprefix tailTrace_6026580
  have hstable : (prefixWord ++ tailWord_6026580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026580).length < 2 ^ (prefixWord ++ tailWord_6026580).sum := by decide
  have hdescent : baseEnd_6026580 < baseStart_6026580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026610 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_6026610 : Nat := 118140960795 + 6026610 * 2 ^ 59
def prefixEnd_6026610 : Nat := 4983230072969 + 3 ^ 40 * 6026610 * 2
def baseEnd_6026610 : Nat := 1031515882397590364786377

theorem tailTrace_6026610 : CollatzResearch.WordTrace tailWord_6026610 prefixEnd_6026610 1031515882397590364786377 := by
  unfold tailWord_6026610
  simp only [CollatzResearch.WordTrace]
  refine ⟨54952131174157176972323321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146539016464419138592862189 54952131174157176972323321)
  ·
    refine ⟨41214098380617882729242491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54952131174157176972323321 41214098380617882729242491)
    ·
      refine ⟨61821147570926824093863737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41214098380617882729242491 61821147570926824093863737)
      ·
        refine ⟨46365860678195118070397803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61821147570926824093863737 46365860678195118070397803)
        ·
          refine ⟨69548791017292677105596705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46365860678195118070397803 69548791017292677105596705)
          ·
            refine ⟨52161593262969507829197529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69548791017292677105596705 52161593262969507829197529)
            ·
              refine ⟨39121194947227130871898147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52161593262969507829197529 39121194947227130871898147)
              ·
                refine ⟨58681792420840696307847221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39121194947227130871898147 58681792420840696307847221)
                ·
                  refine ⟨5501418039453815278860677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58681792420840696307847221 5501418039453815278860677)
                  ·
                    refine ⟨1031515882397590364786377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5501418039453815278860677 1031515882397590364786377)
                    ·
                      rfl

theorem cell23_6026610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_6026610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026610 prefixEnd_6026610 := by exact prefixLift 6026610
  have htrace : WordTrace (prefixWord ++ tailWord_6026610) baseStart_6026610 baseEnd_6026610 := by
    simpa [prefixWord, tailWord_6026610, baseEnd_6026610] using wordTrace_append hprefix tailTrace_6026610
  have hstable : (prefixWord ++ tailWord_6026610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026610).length < 2 ^ (prefixWord ++ tailWord_6026610).sum := by decide
  have hdescent : baseEnd_6026610 < baseStart_6026610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026717 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_6026717 : Nat := 118140960795 + 6026717 * 2 ^ 59
def prefixEnd_6026717 : Nat := 4983230072969 + 3 ^ 40 * 6026717 * 2
def baseEnd_6026717 : Nat := 1031534196540934058573713

theorem tailTrace_6026717 : CollatzResearch.WordTrace tailWord_6026717 prefixEnd_6026717 1031534196540934058573713 := by
  unfold tailWord_6026717
  simp only [CollatzResearch.WordTrace]
  refine ⟨219812427307241065163438405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146541618204827376775625603 219812427307241065163438405)
  ·
    refine ⟨41214830120107699718144701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219812427307241065163438405 41214830120107699718144701)
    ·
      refine ⟨15455561295040387394304263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41214830120107699718144701 15455561295040387394304263)
      ·
        refine ⟨23183341942560581091456395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15455561295040387394304263 23183341942560581091456395)
        ·
          refine ⟨34775012913840871637184593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23183341942560581091456395 34775012913840871637184593)
          ·
            refine ⟨26081259685380653727888445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34775012913840871637184593 26081259685380653727888445)
            ·
              refine ⟨9780472382017745147958167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26081259685380653727888445 9780472382017745147958167)
              ·
                refine ⟨14670708573026617721937251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9780472382017745147958167 14670708573026617721937251)
                ·
                  refine ⟨22006062859539926582905877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14670708573026617721937251 22006062859539926582905877)
                  ·
                    refine ⟨1031534196540934058573713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22006062859539926582905877 1031534196540934058573713)
                    ·
                      rfl

theorem cell23_6026717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_6026717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026717 prefixEnd_6026717 := by exact prefixLift 6026717
  have htrace : WordTrace (prefixWord ++ tailWord_6026717) baseStart_6026717 baseEnd_6026717 := by
    simpa [prefixWord, tailWord_6026717, baseEnd_6026717] using wordTrace_append hprefix tailTrace_6026717
  have hstable : (prefixWord ++ tailWord_6026717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026717).length < 2 ^ (prefixWord ++ tailWord_6026717).sum := by decide
  have hdescent : baseEnd_6026717 < baseStart_6026717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026720 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 4]
def baseStart_6026720 : Nat := 118140960795 + 6026720 * 2 ^ 59
def prefixEnd_6026720 : Nat := 4983230072969 + 3 ^ 40 * 6026720 * 2
def baseEnd_6026720 : Nat := 3094604130064765663983625

theorem tailTrace_6026720 : CollatzResearch.WordTrace tailWord_6026720 prefixEnd_6026720 3094604130064765663983625 := by
  unfold tailWord_6026720
  simp only [CollatzResearch.WordTrace]
  refine ⟨109906268363115098337898807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146541691150820131117198409 109906268363115098337898807)
  ·
    refine ⟨164859402544672647506848211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109906268363115098337898807 164859402544672647506848211)
    ·
      refine ⟨247289103817008971260272317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164859402544672647506848211 247289103817008971260272317)
      ·
        refine ⟨92733413931378364222602119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247289103817008971260272317 92733413931378364222602119)
        ·
          refine ⟨139100120897067546333903179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92733413931378364222602119 139100120897067546333903179)
          ·
            refine ⟨208650181345601319500854769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139100120897067546333903179 208650181345601319500854769)
            ·
              refine ⟨156487636009200989625641077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208650181345601319500854769 156487636009200989625641077)
              ·
                refine ⟨14670715875862592777403851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156487636009200989625641077 14670715875862592777403851)
                ·
                  refine ⟨22006073813793889166105777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14670715875862592777403851 22006073813793889166105777)
                  ·
                    refine ⟨16504555360345416874579333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22006073813793889166105777 16504555360345416874579333)
                    ·
                      refine ⟨3094604130064765663983625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16504555360345416874579333 3094604130064765663983625)
                      ·
                        rfl

theorem cell23_6026720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_6026720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026720 prefixEnd_6026720 := by exact prefixLift 6026720
  have htrace : WordTrace (prefixWord ++ tailWord_6026720) baseStart_6026720 baseEnd_6026720 := by
    simpa [prefixWord, tailWord_6026720, baseEnd_6026720] using wordTrace_append hprefix tailTrace_6026720
  have hstable : (prefixWord ++ tailWord_6026720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026720).length < 2 ^ (prefixWord ++ tailWord_6026720).sum := by decide
  have hdescent : baseEnd_6026720 < baseStart_6026720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026817 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_6026817 : Nat := 118140960795 + 6026817 * 2 ^ 59
def prefixEnd_6026817 : Nat := 4983230072969 + 3 ^ 40 * 6026817 * 2
def baseEnd_6026817 : Nat := 3094653937688251784470679

theorem tailTrace_6026817 : CollatzResearch.WordTrace tailWord_6026817 prefixEnd_6026817 3094653937688251784470679 := by
  unfold tailWord_6026817
  simp only [CollatzResearch.WordTrace]
  refine ⟨219816074606878782242078705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146544049737919188161385803 219816074606878782242078705)
  ·
    refine ⟨164862055955159086681559029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219816074606878782242078705 164862055955159086681559029)
    ·
      refine ⟨15455817745796164376396159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164862055955159086681559029 15455817745796164376396159)
      ·
        refine ⟨23183726618694246564594239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15455817745796164376396159 23183726618694246564594239)
        ·
          refine ⟨34775589928041369846891359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23183726618694246564594239 34775589928041369846891359)
          ·
            refine ⟨52163384892062054770337039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34775589928041369846891359 52163384892062054770337039)
            ·
              refine ⟨78245077338093082155505559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52163384892062054770337039 78245077338093082155505559)
              ·
                refine ⟨117367616007139623233258339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78245077338093082155505559 117367616007139623233258339)
                ·
                  refine ⟨176051424010709434849887509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117367616007139623233258339 176051424010709434849887509)
                  ·
                    refine ⟨8252410500502004758588477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 176051424010709434849887509 8252410500502004758588477)
                    ·
                      refine ⟨3094653937688251784470679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8252410500502004758588477 3094653937688251784470679)
                      ·
                        rfl

theorem cell23_6026817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_6026817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026817 prefixEnd_6026817 := by exact prefixLift 6026817
  have htrace : WordTrace (prefixWord ++ tailWord_6026817) baseStart_6026817 baseEnd_6026817 := by
    simpa [prefixWord, tailWord_6026817, baseEnd_6026817] using wordTrace_append hprefix tailTrace_6026817
  have hstable : (prefixWord ++ tailWord_6026817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026817).length < 2 ^ (prefixWord ++ tailWord_6026817).sum := by decide
  have hdescent : baseEnd_6026817 < baseStart_6026817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026887 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_6026887 : Nat := 118140960795 + 6026887 * 2 ^ 59
def prefixEnd_6026887 : Nat := 4983230072969 + 3 ^ 40 * 6026887 * 2
def baseEnd_6026887 : Nat := 3094689881334066510595357

theorem tailTrace_6026887 : CollatzResearch.WordTrace tailWord_6026887 prefixEnd_6026887 3094689881334066510595357 := by
  unfold tailWord_6026887
  simp only [CollatzResearch.WordTrace]
  refine ⟨219818627716625184197126915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146545751811083456131417943 219818627716625184197126915)
  ·
    refine ⟨329727941574937776295690373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219818627716625184197126915 329727941574937776295690373)
    ·
      refine ⟨61823989045300833055441945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329727941574937776295690373 61823989045300833055441945)
      ·
        refine ⟨46367991783975624791581459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61823989045300833055441945 46367991783975624791581459)
        ·
          refine ⟨69551987675963437187372189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46367991783975624791581459 69551987675963437187372189)
          ·
            refine ⟨26081995378486288945264571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69551987675963437187372189 26081995378486288945264571)
            ·
              refine ⟨39122993067729433417896857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26081995378486288945264571 39122993067729433417896857)
              ·
                refine ⟨29342244800797075063422643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39122993067729433417896857 29342244800797075063422643)
                ·
                  refine ⟨44013367201195612595133965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29342244800797075063422643 44013367201195612595133965)
                  ·
                    refine ⟨16505012700448354723175237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44013367201195612595133965 16505012700448354723175237)
                    ·
                      refine ⟨3094689881334066510595357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16505012700448354723175237 3094689881334066510595357)
                      ·
                        rfl

theorem cell23_6026887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_6026887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026887 prefixEnd_6026887 := by exact prefixLift 6026887
  have htrace : WordTrace (prefixWord ++ tailWord_6026887) baseStart_6026887 baseEnd_6026887 := by
    simpa [prefixWord, tailWord_6026887, baseEnd_6026887] using wordTrace_append hprefix tailTrace_6026887
  have hstable : (prefixWord ++ tailWord_6026887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026887).length < 2 ^ (prefixWord ++ tailWord_6026887).sum := by decide
  have hdescent : baseEnd_6026887 < baseStart_6026887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026897 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 5, 4]
def baseStart_6026897 : Nat := 118140960795 + 6026897 * 2 ^ 59
def prefixEnd_6026897 : Nat := 4983230072969 + 3 ^ 40 * 6026897 * 2
def baseEnd_6026897 : Nat := 1031565005380203823823437

theorem tailTrace_6026897 : CollatzResearch.WordTrace tailWord_6026897 prefixEnd_6026897 1031565005380203823823437 := by
  unfold tailWord_6026897
  simp only [CollatzResearch.WordTrace]
  refine ⟨219818992446588955904990945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146545994964392637269993963 219818992446588955904990945)
  ·
    refine ⟨164864244334941716928743209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219818992446588955904990945 164864244334941716928743209)
    ·
      refine ⟨123648183251206287696557407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164864244334941716928743209 123648183251206287696557407)
      ·
        refine ⟨185472274876809431544836111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123648183251206287696557407 185472274876809431544836111)
        ·
          refine ⟨278208412315214147317254167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185472274876809431544836111 278208412315214147317254167)
          ·
            refine ⟨417312618472821220975881251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278208412315214147317254167 417312618472821220975881251)
            ·
              refine ⟨625968927709231831463821877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417312618472821220975881251 625968927709231831463821877)
              ·
                refine ⟨58684586972740484199733301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 625968927709231831463821877 58684586972740484199733301)
                ·
                  refine ⟨5501680028694420393724997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58684586972740484199733301 5501680028694420393724997)
                  ·
                    refine ⟨1031565005380203823823437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5501680028694420393724997 1031565005380203823823437)
                    ·
                      rfl

theorem cell23_6026897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_6026897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026897 prefixEnd_6026897 := by exact prefixLift 6026897
  have htrace : WordTrace (prefixWord ++ tailWord_6026897) baseStart_6026897 baseEnd_6026897 := by
    simpa [prefixWord, tailWord_6026897, baseEnd_6026897] using wordTrace_append hprefix tailTrace_6026897
  have hstable : (prefixWord ++ tailWord_6026897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026897).length < 2 ^ (prefixWord ++ tailWord_6026897).sum := by decide
  have hdescent : baseEnd_6026897 < baseStart_6026897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026927 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 6]
def baseStart_6026927 : Nat := 118140960795 + 6026927 * 2 ^ 59
def prefixEnd_6026927 : Nat := 4983230072969 + 3 ^ 40 * 6026927 * 2
def baseEnd_6026927 : Nat := 343856713395582928232797

theorem tailTrace_6026927 : CollatzResearch.WordTrace tailWord_6026927 prefixEnd_6026927 343856713395582928232797 := by
  unfold tailWord_6026927
  simp only [CollatzResearch.WordTrace]
  refine ⟨219820086636480271028583035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146546724424320180685722023 219820086636480271028583035)
  ·
    refine ⟨329730129954720406542874553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219820086636480271028583035 329730129954720406542874553)
    ·
      refine ⟨247297597466040304907155915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329730129954720406542874553 247297597466040304907155915)
      ·
        refine ⟨370946396199060457360733873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247297597466040304907155915 370946396199060457360733873)
        ·
          refine ⟨278209797149295343020550405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370946396199060457360733873 278209797149295343020550405)
          ·
            refine ⟨52164336965492876816353201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278209797149295343020550405 52164336965492876816353201)
            ·
              refine ⟨39123252724119657612264901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52164336965492876816353201 39123252724119657612264901)
              ·
                refine ⟨7335609885772435802299669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39123252724119657612264901 7335609885772435802299669)
                ·
                  refine ⟨343856713395582928232797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7335609885772435802299669 343856713395582928232797)
                  ·
                    rfl

theorem cell23_6026927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 6].length) (baseStart_6026927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026927 prefixEnd_6026927 := by exact prefixLift 6026927
  have htrace : WordTrace (prefixWord ++ tailWord_6026927) baseStart_6026927 baseEnd_6026927 := by
    simpa [prefixWord, tailWord_6026927, baseEnd_6026927] using wordTrace_append hprefix tailTrace_6026927
  have hstable : (prefixWord ++ tailWord_6026927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026927).length < 2 ^ (prefixWord ++ tailWord_6026927).sum := by decide
  have hdescent : baseEnd_6026927 < baseStart_6026927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026981 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 2, 3, 2]
def baseStart_6026981 : Nat := 118140960795 + 6026981 * 2 ^ 59
def prefixEnd_6026981 : Nat := 4983230072969 + 3 ^ 40 * 6026981 * 2
def baseEnd_6026981 : Nat := 3094738148515589142819925

theorem tailTrace_6026981 : CollatzResearch.WordTrace tailWord_6026981 prefixEnd_6026981 3094738148515589142819925 := by
  unfold tailWord_6026981
  simp only [CollatzResearch.WordTrace]
  refine ⟨219822056178284638251048797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146548037452189758834032531 219822056178284638251048797)
  ·
    refine ⟨82433271066856739344143299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219822056178284638251048797 82433271066856739344143299)
    ·
      refine ⟨123649906600285109016214949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82433271066856739344143299 123649906600285109016214949)
      ·
        refine ⟨23184357487553457940540303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123649906600285109016214949 23184357487553457940540303)
        ·
          refine ⟨34776536231330186910810455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23184357487553457940540303 34776536231330186910810455)
          ·
            refine ⟨52164804346995280366215683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34776536231330186910810455 52164804346995280366215683)
            ·
              refine ⟨78247206520492920549323525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52164804346995280366215683 78247206520492920549323525)
              ·
                refine ⟨14671351222592422602998161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78247206520492920549323525 14671351222592422602998161)
                ·
                  refine ⟨11003513416944316952248621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14671351222592422602998161 11003513416944316952248621)
                  ·
                    refine ⟨4126317531354118857093233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11003513416944316952248621 4126317531354118857093233)
                    ·
                      refine ⟨3094738148515589142819925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126317531354118857093233 3094738148515589142819925)
                      ·
                        rfl

theorem cell23_6026981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_6026981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026981 prefixEnd_6026981 := by exact prefixLift 6026981
  have htrace : WordTrace (prefixWord ++ tailWord_6026981) baseStart_6026981 baseEnd_6026981 := by
    simpa [prefixWord, tailWord_6026981, baseEnd_6026981] using wordTrace_append hprefix tailTrace_6026981
  have hstable : (prefixWord ++ tailWord_6026981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026981).length < 2 ^ (prefixWord ++ tailWord_6026981).sum := by decide
  have hdescent : baseEnd_6026981 < baseStart_6026981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026994 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6026994 : Nat := 118140960795 + 6026994 * 2 ^ 59
def prefixEnd_6026994 : Nat := 4983230072969 + 3 ^ 40 * 6026994 * 2
def baseEnd_6026994 : Nat := 3094744823764097591957365

theorem tailTrace_6026994 : CollatzResearch.WordTrace tailWord_6026994 prefixEnd_6026994 3094744823764097591957365 := by
  unfold tailWord_6026994
  simp only [CollatzResearch.WordTrace]
  refine ⟨54955632581809385367818009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146548353551491694314181357 54955632581809385367818009)
  ·
    refine ⟨41216724436357039025863507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54955632581809385367818009 41216724436357039025863507)
    ·
      refine ⟨61825086654535558538795261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41216724436357039025863507 61825086654535558538795261)
      ·
        refine ⟨23184407495450834452048223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61825086654535558538795261 23184407495450834452048223)
        ·
          refine ⟨34776611243176251678072335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23184407495450834452048223 34776611243176251678072335)
          ·
            refine ⟨52164916864764377517108503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34776611243176251678072335 52164916864764377517108503)
            ·
              refine ⟨78247375297146566275662755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52164916864764377517108503 78247375297146566275662755)
              ·
                refine ⟨117371062945719849413494133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78247375297146566275662755 117371062945719849413494133)
                ·
                  refine ⟨11003537151161235882515075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117371062945719849413494133 11003537151161235882515075)
                  ·
                    refine ⟨16505305726741853823772613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11003537151161235882515075 16505305726741853823772613)
                    ·
                      refine ⟨3094744823764097591957365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16505305726741853823772613 3094744823764097591957365)
                      ·
                        rfl

theorem cell23_6026994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6026994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6026994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6026994 prefixEnd_6026994 := by exact prefixLift 6026994
  have htrace : WordTrace (prefixWord ++ tailWord_6026994) baseStart_6026994 baseEnd_6026994 := by
    simpa [prefixWord, tailWord_6026994, baseEnd_6026994] using wordTrace_append hprefix tailTrace_6026994
  have hstable : (prefixWord ++ tailWord_6026994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026994).length < 2 ^ (prefixWord ++ tailWord_6026994).sum := by decide
  have hdescent : baseEnd_6026994 < baseStart_6026994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027004 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_6027004 : Nat := 118140960795 + 6027004 * 2 ^ 59
def prefixEnd_6027004 : Nat := 4983230072969 + 3 ^ 40 * 6027004 * 2
def baseEnd_6027004 : Nat := 1031583319523547517610773

theorem tailTrace_6027004 : CollatzResearch.WordTrace tailWord_6027004 prefixEnd_6027004 1031583319523547517610773 := by
  unfold tailWord_6027004
  simp only [CollatzResearch.WordTrace]
  refine ⟨109911447528600656589568033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146548596704800875452757377 109911447528600656589568033)
  ·
    refine ⟨82433585646450492442176025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109911447528600656589568033 82433585646450492442176025)
    ·
      refine ⟨61825189234837869331632019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82433585646450492442176025 61825189234837869331632019)
      ·
        refine ⟨92737783852256803997448029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61825189234837869331632019 92737783852256803997448029)
        ·
          refine ⟨34776668944596301499043011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92737783852256803997448029 34776668944596301499043011)
          ·
            refine ⟨52165003416894452248564517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34776668944596301499043011 52165003416894452248564517)
            ·
              refine ⟨9780938140667709796605847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52165003416894452248564517 9780938140667709796605847)
              ·
                refine ⟨14671407211001564694908771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9780938140667709796605847 14671407211001564694908771)
                ·
                  refine ⟨22007110816502347042363157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14671407211001564694908771 22007110816502347042363157)
                  ·
                    refine ⟨1031583319523547517610773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22007110816502347042363157 1031583319523547517610773)
                    ·
                      rfl

theorem cell23_6027004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_6027004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027004 prefixEnd_6027004 := by exact prefixLift 6027004
  have htrace : WordTrace (prefixWord ++ tailWord_6027004) baseStart_6027004 baseEnd_6027004 := by
    simpa [prefixWord, tailWord_6027004, baseEnd_6027004] using wordTrace_append hprefix tailTrace_6027004
  have hstable : (prefixWord ++ tailWord_6027004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027004).length < 2 ^ (prefixWord ++ tailWord_6027004).sum := by decide
  have hdescent : baseEnd_6027004 < baseStart_6027004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027007 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_6027007 : Nat := 118140960795 + 6027007 * 2 ^ 59
def prefixEnd_6027007 : Nat := 4983230072969 + 3 ^ 40 * 6027007 * 2
def baseEnd_6027007 : Nat := 3094751499012606041094805

theorem tailTrace_6027007 : CollatzResearch.WordTrace tailWord_6027007 prefixEnd_6027007 3094751499012606041094805 := by
  unfold tailWord_6027007
  simp only [CollatzResearch.WordTrace]
  refine ⟨219823004476190444691495275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146548669650793629794330183 219823004476190444691495275)
  ·
    refine ⟨329734506714285667037242913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219823004476190444691495275 329734506714285667037242913)
    ·
      refine ⟨247300880035714250277932185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329734506714285667037242913 247300880035714250277932185)
      ·
        refine ⟨185475660026785687708449139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247300880035714250277932185 185475660026785687708449139)
        ·
          refine ⟨278213490040178531562673709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185475660026785687708449139 278213490040178531562673709)
          ·
            refine ⟨104330058765066949336002641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278213490040178531562673709 104330058765066949336002641)
            ·
              refine ⟨78247544073800212002001981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104330058765066949336002641 78247544073800212002001981)
              ·
                refine ⟨29342829027675079500750743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78247544073800212002001981 29342829027675079500750743)
                ·
                  refine ⟨44014243541512619251126115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29342829027675079500750743 44014243541512619251126115)
                  ·
                    refine ⟨66021365312268928876689173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44014243541512619251126115 66021365312268928876689173)
                    ·
                      refine ⟨3094751499012606041094805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66021365312268928876689173 3094751499012606041094805)
                      ·
                        rfl

theorem cell23_6027007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_6027007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027007 prefixEnd_6027007 := by exact prefixLift 6027007
  have htrace : WordTrace (prefixWord ++ tailWord_6027007) baseStart_6027007 baseEnd_6027007 := by
    simpa [prefixWord, tailWord_6027007, baseEnd_6027007] using wordTrace_append hprefix tailTrace_6027007
  have hstable : (prefixWord ++ tailWord_6027007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027007).length < 2 ^ (prefixWord ++ tailWord_6027007).sum := by decide
  have hdescent : baseEnd_6027007 < baseStart_6027007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
