import V185TrunkScan22Chunk063

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_576061 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 7]
def baseStart_576061 : Nat := 118140960795 + 576061 * 2 ^ 59
def prefixEnd_576061 : Nat := 4983230072969 + 3 ^ 40 * 576061 * 2
def baseEnd_576061 : Nat := 65732484291061309419611

theorem tailTrace_576061 : CollatzResearch.WordTrace tailWord_576061 prefixEnd_576061 65732484291061309419611 := by
  unfold tailWord_576061
  simp only [CollatzResearch.WordTrace]
  refine ⟨21010670766036855231208037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14007113844024570154138691 21010670766036855231208037)
  ·
    refine ⟨3939500768631910355851507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21010670766036855231208037 3939500768631910355851507)
    ·
      refine ⟨5909251152947865533777261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3939500768631910355851507 5909251152947865533777261)
      ·
        refine ⟨2215969182355449575166473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5909251152947865533777261 2215969182355449575166473)
        ·
          refine ⟨1661976886766587181374855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2215969182355449575166473 1661976886766587181374855)
          ·
            refine ⟨2492965330149880772062283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661976886766587181374855 2492965330149880772062283)
            ·
              refine ⟨3739447995224821158093425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492965330149880772062283 3739447995224821158093425)
              ·
                refine ⟨2804585996418615868570069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3739447995224821158093425 2804585996418615868570069)
                ·
                  refine ⟨65732484291061309419611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2804585996418615868570069 65732484291061309419611)
                  ·
                    rfl

theorem cell22_576061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_576061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576061 prefixEnd_576061 := by exact prefixLift 576061
  have htrace : WordTrace (prefixWord ++ tailWord_576061) baseStart_576061 baseEnd_576061 := by
    simpa [prefixWord, tailWord_576061, baseEnd_576061] using wordTrace_append hprefix tailTrace_576061
  have hstable : (prefixWord ++ tailWord_576061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576061).length < 2 ^ (prefixWord ++ tailWord_576061).sum := by decide
  have hdescent : baseEnd_576061 < baseStart_576061 := by decide
  rcases family_descends (prefixWord ++ tailWord_576061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576082 : List Nat := [3, 2, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_576082 : Nat := 118140960795 + 576082 * 2 ^ 59
def prefixEnd_576082 : Nat := 4983230072969 + 3 ^ 40 * 576082 * 2
def baseEnd_576082 : Nat := 197204641602346873483769

theorem tailTrace_576082 : CollatzResearch.WordTrace tailWord_576082 prefixEnd_576082 197204641602346873483769 := by
  unfold tailWord_576082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5252859174740193954430625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14007624465973850545148333 5252859174740193954430625)
  ·
    refine ⟨3939644381055145465822969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5252859174740193954430625 3939644381055145465822969)
    ·
      refine ⟨2954733285791359099367227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3939644381055145465822969 2954733285791359099367227)
      ·
        refine ⟨4432099928687038649050841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954733285791359099367227 4432099928687038649050841)
        ·
          refine ⟨3324074946515278986788131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4432099928687038649050841 3324074946515278986788131)
          ·
            refine ⟨4986112419772918480182197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324074946515278986788131 4986112419772918480182197)
            ·
              refine ⟨467448039353711107517081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4986112419772918480182197 467448039353711107517081)
              ·
                refine ⟨350586029515283330637811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467448039353711107517081 350586029515283330637811)
                ·
                  refine ⟨525879044272924995956717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350586029515283330637811 525879044272924995956717)
                  ·
                    refine ⟨197204641602346873483769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525879044272924995956717 197204641602346873483769)
                    ·
                      rfl

theorem cell22_576082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_576082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576082 prefixEnd_576082 := by exact prefixLift 576082
  have htrace : WordTrace (prefixWord ++ tailWord_576082) baseStart_576082 baseEnd_576082 := by
    simpa [prefixWord, tailWord_576082, baseEnd_576082] using wordTrace_append hprefix tailTrace_576082
  have hstable : (prefixWord ++ tailWord_576082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576082).length < 2 ^ (prefixWord ++ tailWord_576082).sum := by decide
  have hdescent : baseEnd_576082 < baseStart_576082 := by decide
  rcases family_descends (prefixWord ++ tailWord_576082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576106 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_576106 : Nat := 118140960795 + 576106 * 2 ^ 59
def prefixEnd_576106 : Nat := 4983230072969 + 3 ^ 40 * 576106 * 2
def baseEnd_576106 : Nat := 65737619097606270294565

theorem tailTrace_576106 : CollatzResearch.WordTrace tailWord_576106 prefixEnd_576106 65737619097606270294565 := by
  unfold tailWord_576106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5253078012718456979149043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14008208033915885277730781 5253078012718456979149043)
  ·
    refine ⟨7879617019077685468723565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5253078012718456979149043 7879617019077685468723565)
    ·
      refine ⟨2954856382154132050771337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7879617019077685468723565 2954856382154132050771337)
      ·
        refine ⟨2216142286615599038078503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2954856382154132050771337 2216142286615599038078503)
        ·
          refine ⟨3324213429923398557117755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216142286615599038078503 3324213429923398557117755)
          ·
            refine ⟨4986320144885097835676633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324213429923398557117755 4986320144885097835676633)
            ·
              refine ⟨3739740108663823376757475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4986320144885097835676633 3739740108663823376757475)
              ·
                refine ⟨5609610162995735065136213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739740108663823376757475 5609610162995735065136213)
                ·
                  refine ⟨65737619097606270294565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5609610162995735065136213 65737619097606270294565)
                  ·
                    rfl

theorem cell22_576106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_576106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576106 prefixEnd_576106 := by exact prefixLift 576106
  have htrace : WordTrace (prefixWord ++ tailWord_576106) baseStart_576106 baseEnd_576106 := by
    simpa [prefixWord, tailWord_576106, baseEnd_576106] using wordTrace_append hprefix tailTrace_576106
  have hstable : (prefixWord ++ tailWord_576106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576106).length < 2 ^ (prefixWord ++ tailWord_576106).sum := by decide
  have hdescent : baseEnd_576106 < baseStart_576106 := by decide
  rcases family_descends (prefixWord ++ tailWord_576106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576108 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_576108 : Nat := 118140960795 + 576108 * 2 ^ 59
def prefixEnd_576108 : Nat := 4983230072969 + 3 ^ 40 * 576108 * 2
def baseEnd_576108 : Nat := 197213541933691472333689

theorem tailTrace_576108 : CollatzResearch.WordTrace tailWord_576108 prefixEnd_576108 197213541933691472333689 := by
  unfold tailWord_576108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10506192498433291129084489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14008256664577721505445985 10506192498433291129084489)
  ·
    refine ⟨7879644373824968346813367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10506192498433291129084489 7879644373824968346813367)
    ·
      refine ⟨11819466560737452520220051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7879644373824968346813367 11819466560737452520220051)
      ·
        refine ⟨17729199841106178780330077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11819466560737452520220051 17729199841106178780330077)
        ·
          refine ⟨6648449940414817042623779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17729199841106178780330077 6648449940414817042623779)
          ·
            refine ⟨9972674910622225563935669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6648449940414817042623779 9972674910622225563935669)
            ·
              refine ⟨934938272870833646618969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9972674910622225563935669 934938272870833646618969)
              ·
                refine ⟨701203704653125234964227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934938272870833646618969 701203704653125234964227)
                ·
                  refine ⟨1051805556979687852446341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701203704653125234964227 1051805556979687852446341)
                  ·
                    refine ⟨197213541933691472333689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1051805556979687852446341 197213541933691472333689)
                    ·
                      rfl

theorem cell22_576108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_576108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576108 prefixEnd_576108 := by exact prefixLift 576108
  have htrace : WordTrace (prefixWord ++ tailWord_576108) baseStart_576108 baseEnd_576108 := by
    simpa [prefixWord, tailWord_576108, baseEnd_576108] using wordTrace_append hprefix tailTrace_576108
  have hstable : (prefixWord ++ tailWord_576108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576108).length < 2 ^ (prefixWord ++ tailWord_576108).sum := by decide
  have hdescent : baseEnd_576108 < baseStart_576108 := by decide
  rcases family_descends (prefixWord ++ tailWord_576108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576121 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_576121 : Nat := 118140960795 + 576121 * 2 ^ 59
def prefixEnd_576121 : Nat := 4983230072969 + 3 ^ 40 * 576121 * 2
def baseEnd_576121 : Nat := 197217992099363771758649

theorem tailTrace_576121 : CollatzResearch.WordTrace tailWord_576121 prefixEnd_576121 197217992099363771758649 := by
  unfold tailWord_576121
  simp only [CollatzResearch.WordTrace]
  refine ⟨21012859145819485478392217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14008572763879656985594811 21012859145819485478392217)
  ·
    refine ⟨15759644359364614108794163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21012859145819485478392217 15759644359364614108794163)
    ·
      refine ⟨23639466539046921163191245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15759644359364614108794163 23639466539046921163191245)
      ·
        refine ⟨8864799952142595436196717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23639466539046921163191245 8864799952142595436196717)
        ·
          refine ⟨3324299982053473288573769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8864799952142595436196717 3324299982053473288573769)
          ·
            refine ⟨2493224986540104966430327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3324299982053473288573769 2493224986540104966430327)
            ·
              refine ⟨3739837479810157449645491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493224986540104966430327 3739837479810157449645491)
              ·
                refine ⟨5609756219715236174468237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739837479810157449645491 5609756219715236174468237)
                ·
                  refine ⟨2103658582393213565425589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5609756219715236174468237 2103658582393213565425589)
                  ·
                    refine ⟨197217992099363771758649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2103658582393213565425589 197217992099363771758649)
                    ·
                      rfl

theorem cell22_576121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_576121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576121 prefixEnd_576121 := by exact prefixLift 576121
  have htrace : WordTrace (prefixWord ++ tailWord_576121) baseStart_576121 baseEnd_576121 := by
    simpa [prefixWord, tailWord_576121, baseEnd_576121] using wordTrace_append hprefix tailTrace_576121
  have hstable : (prefixWord ++ tailWord_576121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576121).length < 2 ^ (prefixWord ++ tailWord_576121).sum := by decide
  have hdescent : baseEnd_576121 < baseStart_576121 := by decide
  rcases family_descends (prefixWord ++ tailWord_576121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576200 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 3, 3]
def baseStart_576200 : Nat := 118140960795 + 576200 * 2 ^ 59
def prefixEnd_576200 : Nat := 4983230072969 + 3 ^ 40 * 576200 * 2
def baseEnd_576200 : Nat := 197245035413833899033407

theorem tailTrace_576200 : CollatzResearch.WordTrace tailWord_576200 prefixEnd_576200 197245035413833899033407 := by
  unfold tailWord_576200
  simp only [CollatzResearch.WordTrace]
  refine ⟨10507870256266640985259027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14010493675022187980345369 10507870256266640985259027)
  ·
    refine ⟨15761805384399961477888541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10507870256266640985259027 15761805384399961477888541)
    ·
      refine ⟨5910677019149985554208203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15761805384399961477888541 5910677019149985554208203)
      ·
        refine ⟨8866015528724978331312305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5910677019149985554208203 8866015528724978331312305)
        ·
          refine ⟨6649511646543733748484229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8866015528724978331312305 6649511646543733748484229)
          ·
            refine ⟨1246783433726950077840793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6649511646543733748484229 1246783433726950077840793)
            ·
              refine ⟨935087575295212558380595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246783433726950077840793 935087575295212558380595)
              ·
                refine ⟨1402631362942818837570893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935087575295212558380595 1402631362942818837570893)
                ·
                  refine ⟨525986761103557064089085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1402631362942818837570893 525986761103557064089085)
                  ·
                    refine ⟨197245035413833899033407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525986761103557064089085 197245035413833899033407)
                    ·
                      rfl

theorem cell22_576200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_576200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576200 prefixEnd_576200 := by exact prefixLift 576200
  have htrace : WordTrace (prefixWord ++ tailWord_576200) baseStart_576200 baseEnd_576200 := by
    simpa [prefixWord, tailWord_576200, baseEnd_576200] using wordTrace_append hprefix tailTrace_576200
  have hstable : (prefixWord ++ tailWord_576200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576200).length < 2 ^ (prefixWord ++ tailWord_576200).sum := by decide
  have hdescent : baseEnd_576200 < baseStart_576200 := by decide
  rcases family_descends (prefixWord ++ tailWord_576200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576256 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_576256 : Nat := 118140960795 + 576256 * 2 ^ 59
def prefixEnd_576256 : Nat := 4983230072969 + 3 ^ 40 * 576256 * 2
def baseEnd_576256 : Nat := 197264205358268419633235

theorem tailTrace_576256 : CollatzResearch.WordTrace tailWord_576256 prefixEnd_576256 197264205358268419633235 := by
  unfold tailWord_576256
  simp only [CollatzResearch.WordTrace]
  refine ⟨10508891500165201767278311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14011855333553602356371081 10508891500165201767278311)
  ·
    refine ⟨15763337250247802650917467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10508891500165201767278311 15763337250247802650917467)
    ·
      refine ⟨23645005875371703976376201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15763337250247802650917467 23645005875371703976376201)
      ·
        refine ⟨17733754406528777982282151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23645005875371703976376201 17733754406528777982282151)
        ·
          refine ⟨26600631609793166973423227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17733754406528777982282151 26600631609793166973423227)
          ·
            refine ⟨39900947414689750460134841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26600631609793166973423227 39900947414689750460134841)
            ·
              refine ⟨29925710561017312845101131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39900947414689750460134841 29925710561017312845101131)
              ·
                refine ⟨44888565841525969267651697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29925710561017312845101131 44888565841525969267651697)
                ·
                  refine ⟨33666424381144476950738773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44888565841525969267651697 33666424381144476950738773)
                  ·
                    refine ⟨197264205358268419633235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 33666424381144476950738773 197264205358268419633235)
                    ·
                      rfl

theorem cell22_576256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_576256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576256 prefixEnd_576256 := by exact prefixLift 576256
  have htrace : WordTrace (prefixWord ++ tailWord_576256) baseStart_576256 baseEnd_576256 := by
    simpa [prefixWord, tailWord_576256, baseEnd_576256] using wordTrace_append hprefix tailTrace_576256
  have hstable : (prefixWord ++ tailWord_576256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576256).length < 2 ^ (prefixWord ++ tailWord_576256).sum := by decide
  have hdescent : baseEnd_576256 < baseStart_576256 := by decide
  rcases family_descends (prefixWord ++ tailWord_576256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576290 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_576290 : Nat := 118140960795 + 576290 * 2 ^ 59
def prefixEnd_576290 : Nat := 4983230072969 + 3 ^ 40 * 576290 * 2
def baseEnd_576290 : Nat := 197275844253103664283131

theorem tailTrace_576290 : CollatzResearch.WordTrace tailWord_576290 prefixEnd_576290 197275844253103664283131 := by
  unfold tailWord_576290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254755770551806835323581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14012682054804818227529549 5254755770551806835323581)
  ·
    refine ⟨1970533413956927563246343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5254755770551806835323581 1970533413956927563246343)
    ·
      refine ⟨2955800120935391344869515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1970533413956927563246343 2955800120935391344869515)
      ·
        refine ⟨4433700181403087017304273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2955800120935391344869515 4433700181403087017304273)
        ·
          refine ⟨3325275136052315262978205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4433700181403087017304273 3325275136052315262978205)
          ·
            refine ⟨1246978176019618223616827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3325275136052315262978205 1246978176019618223616827)
            ·
              refine ⟨1870467264029427335425241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246978176019618223616827 1870467264029427335425241)
              ·
                refine ⟨1402850448022070501568931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1870467264029427335425241 1402850448022070501568931)
                ·
                  refine ⟨2104275672033105752353397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402850448022070501568931 2104275672033105752353397)
                  ·
                    refine ⟨197275844253103664283131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2104275672033105752353397 197275844253103664283131)
                    ·
                      rfl

theorem cell22_576290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_576290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576290 prefixEnd_576290 := by exact prefixLift 576290
  have htrace : WordTrace (prefixWord ++ tailWord_576290) baseStart_576290 baseEnd_576290 := by
    simpa [prefixWord, tailWord_576290, baseEnd_576290] using wordTrace_append hprefix tailTrace_576290
  have hstable : (prefixWord ++ tailWord_576290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576290).length < 2 ^ (prefixWord ++ tailWord_576290).sum := by decide
  have hdescent : baseEnd_576290 < baseStart_576290 := by decide
  rcases family_descends (prefixWord ++ tailWord_576290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576307 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 2, 3]
def baseStart_576307 : Nat := 118140960795 + 576307 * 2 ^ 59
def prefixEnd_576307 : Nat := 4983230072969 + 3 ^ 40 * 576307 * 2
def baseEnd_576307 : Nat := 197281663700521286608079

theorem tailTrace_576307 : CollatzResearch.WordTrace tailWord_576307 prefixEnd_576307 197281663700521286608079 := by
  unfold tailWord_576307
  simp only [CollatzResearch.WordTrace]
  refine ⟨21019643123145639244663175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14013095415430426163108783 21019643123145639244663175)
  ·
    refine ⟨31529464684718458866994763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21019643123145639244663175 31529464684718458866994763)
    ·
      refine ⟨47294197027077688300492145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31529464684718458866994763 47294197027077688300492145)
      ·
        refine ⟨35470647770308266225369109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47294197027077688300492145 35470647770308266225369109)
        ·
          refine ⟨1662686614233199979314177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35470647770308266225369109 1662686614233199979314177)
          ·
            refine ⟨1247014960674899984485633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1662686614233199979314177 1247014960674899984485633)
            ·
              refine ⟨935261220506174988364225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247014960674899984485633 935261220506174988364225)
              ·
                refine ⟨701445915379631241273169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935261220506174988364225 701445915379631241273169)
                ·
                  refine ⟨526084436534723430954877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 701445915379631241273169 526084436534723430954877)
                  ·
                    refine ⟨197281663700521286608079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 526084436534723430954877 197281663700521286608079)
                    ·
                      rfl

theorem cell22_576307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 3].length) (baseStart_576307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576307 prefixEnd_576307 := by exact prefixLift 576307
  have htrace : WordTrace (prefixWord ++ tailWord_576307) baseStart_576307 baseEnd_576307 := by
    simpa [prefixWord, tailWord_576307, baseEnd_576307] using wordTrace_append hprefix tailTrace_576307
  have hstable : (prefixWord ++ tailWord_576307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576307).length < 2 ^ (prefixWord ++ tailWord_576307).sum := by decide
  have hdescent : baseEnd_576307 < baseStart_576307 := by decide
  rcases family_descends (prefixWord ++ tailWord_576307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576309 : List Nat := [1, 3, 3, 1, 3, 3, 2, 2, 4]
def baseStart_576309 : Nat := 118140960795 + 576309 * 2 ^ 59
def prefixEnd_576309 : Nat := 4983230072969 + 3 ^ 40 * 576309 * 2
def baseEnd_576309 : Nat := 65760782780464649352691

theorem tailTrace_576309 : CollatzResearch.WordTrace tailWord_576309 prefixEnd_576309 65760782780464649352691 := by
  unfold tailWord_576309
  simp only [CollatzResearch.WordTrace]
  refine ⟨21019716069138393586235981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14013144046092262390823987 21019716069138393586235981)
  ·
    refine ⟨7882393525926897594838493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21019716069138393586235981 7882393525926897594838493)
    ·
      refine ⟨2955897572222586598064435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7882393525926897594838493 2955897572222586598064435)
      ·
        refine ⟨4433846358333879897096653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2955897572222586598064435 4433846358333879897096653)
        ·
          refine ⟨1662692384375204961411245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4433846358333879897096653 1662692384375204961411245)
          ·
            refine ⟨623509644140701860529217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1662692384375204961411245 623509644140701860529217)
            ·
              refine ⟨467632233105526395396913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623509644140701860529217 467632233105526395396913)
              ·
                refine ⟨350724174829144796547685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467632233105526395396913 350724174829144796547685)
                ·
                  refine ⟨65760782780464649352691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 350724174829144796547685 65760782780464649352691)
                  ·
                    rfl

theorem cell22_576309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_576309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576309 prefixEnd_576309 := by exact prefixLift 576309
  have htrace : WordTrace (prefixWord ++ tailWord_576309) baseStart_576309 baseEnd_576309 := by
    simpa [prefixWord, tailWord_576309, baseEnd_576309] using wordTrace_append hprefix tailTrace_576309
  have hstable : (prefixWord ++ tailWord_576309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576309).length < 2 ^ (prefixWord ++ tailWord_576309).sum := by decide
  have hdescent : baseEnd_576309 < baseStart_576309 := by decide
  rcases family_descends (prefixWord ++ tailWord_576309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576324 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_576324 : Nat := 118140960795 + 576324 * 2 ^ 59
def prefixEnd_576324 : Nat := 4983230072969 + 3 ^ 40 * 576324 * 2
def baseEnd_576324 : Nat := 197287483147938908933027

theorem tailTrace_576324 : CollatzResearch.WordTrace tailWord_576324 prefixEnd_576324 197287483147938908933027 := by
  unfold tailWord_576324
  simp only [CollatzResearch.WordTrace]
  refine ⟨10510131582042025574016013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14013508776056034098688017 10510131582042025574016013)
  ·
    refine ⟨3941299343265759590256005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10510131582042025574016013 3941299343265759590256005)
    ·
      refine ⟨738993626862329923173001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3941299343265759590256005 738993626862329923173001)
      ·
        refine ⟨554245220146747442379751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 738993626862329923173001 554245220146747442379751)
        ·
          refine ⟨831367830220121163569627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554245220146747442379751 831367830220121163569627)
          ·
            refine ⟨1247051745330181745354441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831367830220121163569627 1247051745330181745354441)
            ·
              refine ⟨935288808997636309015831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247051745330181745354441 935288808997636309015831)
              ·
                refine ⟨1402933213496454463523747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935288808997636309015831 1402933213496454463523747)
                ·
                  refine ⟨2104399820244681695285621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402933213496454463523747 2104399820244681695285621)
                  ·
                    refine ⟨197287483147938908933027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2104399820244681695285621 197287483147938908933027)
                    ·
                      rfl

theorem cell22_576324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_576324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576324 prefixEnd_576324 := by exact prefixLift 576324
  have htrace : WordTrace (prefixWord ++ tailWord_576324) baseStart_576324 baseEnd_576324 := by
    simpa [prefixWord, tailWord_576324, baseEnd_576324] using wordTrace_append hprefix tailTrace_576324
  have hstable : (prefixWord ++ tailWord_576324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576324).length < 2 ^ (prefixWord ++ tailWord_576324).sum := by decide
  have hdescent : baseEnd_576324 < baseStart_576324 := by decide
  rcases family_descends (prefixWord ++ tailWord_576324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576363 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 2, 5]
def baseStart_576363 : Nat := 118140960795 + 576363 * 2 ^ 59
def prefixEnd_576363 : Nat := 4983230072969 + 3 ^ 40 * 576363 * 2
def baseEnd_576363 : Nat := 197300833644955807207907

theorem tailTrace_576363 : CollatzResearch.WordTrace tailWord_576363 prefixEnd_576363 197300833644955807207907 := by
  unfold tailWord_576363
  simp only [CollatzResearch.WordTrace]
  refine ⟨21021685610942760808701743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14014457073961840539134495 21021685610942760808701743)
  ·
    refine ⟨31532528416414141213052615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21021685610942760808701743 31532528416414141213052615)
    ·
      refine ⟨47298792624621211819578923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31532528416414141213052615 47298792624621211819578923)
      ·
        refine ⟨70948188936931817729368385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47298792624621211819578923 70948188936931817729368385)
        ·
          refine ⟨53211141702698863297026289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70948188936931817729368385 53211141702698863297026289)
          ·
            refine ⟨39908356277024147472769717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53211141702698863297026289 39908356277024147472769717)
            ·
              refine ⟨3741408400971013825572161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39908356277024147472769717 3741408400971013825572161)
              ·
                refine ⟨2806056300728260369179121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3741408400971013825572161 2806056300728260369179121)
                ·
                  refine ⟨2104542225546195276884341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2806056300728260369179121 2104542225546195276884341)
                  ·
                    refine ⟨197300833644955807207907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2104542225546195276884341 197300833644955807207907)
                    ·
                      rfl

theorem cell22_576363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_576363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576363 prefixEnd_576363 := by exact prefixLift 576363
  have htrace : WordTrace (prefixWord ++ tailWord_576363) baseStart_576363 baseEnd_576363 := by
    simpa [prefixWord, tailWord_576363, baseEnd_576363] using wordTrace_append hprefix tailTrace_576363
  have hstable : (prefixWord ++ tailWord_576363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576363).length < 2 ^ (prefixWord ++ tailWord_576363).sum := by decide
  have hdescent : baseEnd_576363 < baseStart_576363 := by decide
  rcases family_descends (prefixWord ++ tailWord_576363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576395 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 1, 4]
def baseStart_576395 : Nat := 118140960795 + 576395 * 2 ^ 59
def prefixEnd_576395 : Nat := 4983230072969 + 3 ^ 40 * 576395 * 2
def baseEnd_576395 : Nat := 197311787898918390407809

theorem tailTrace_576395 : CollatzResearch.WordTrace tailWord_576395 prefixEnd_576395 197311787898918390407809 := by
  unfold tailWord_576395
  simp only [CollatzResearch.WordTrace]
  refine ⟨21022852746826830273866639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14015235164551220182577759 21022852746826830273866639)
  ·
    refine ⟨31534279120240245410799959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21022852746826830273866639 31534279120240245410799959)
    ·
      refine ⟨47301418680360368116199939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31534279120240245410799959 47301418680360368116199939)
      ·
        refine ⟨70952128020540552174299909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47301418680360368116199939 70952128020540552174299909)
        ·
          refine ⟨13303524003851353532681233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70952128020540552174299909 13303524003851353532681233)
          ·
            refine ⟨9977643002888515149510925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13303524003851353532681233 9977643002888515149510925)
            ·
              refine ⟨3741616126083193181066597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9977643002888515149510925 3741616126083193181066597)
              ·
                refine ⟨701553023640598721449987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3741616126083193181066597 701553023640598721449987)
                ·
                  refine ⟨1052329535460898082174981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701553023640598721449987 1052329535460898082174981)
                  ·
                    refine ⟨197311787898918390407809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1052329535460898082174981 197311787898918390407809)
                    ·
                      rfl

theorem cell22_576395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 4].length) (baseStart_576395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576395 prefixEnd_576395 := by exact prefixLift 576395
  have htrace : WordTrace (prefixWord ++ tailWord_576395) baseStart_576395 baseEnd_576395 := by
    simpa [prefixWord, tailWord_576395, baseEnd_576395] using wordTrace_append hprefix tailTrace_576395
  have hstable : (prefixWord ++ tailWord_576395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576395).length < 2 ^ (prefixWord ++ tailWord_576395).sum := by decide
  have hdescent : baseEnd_576395 < baseStart_576395 := by decide
  rcases family_descends (prefixWord ++ tailWord_576395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576425 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 4, 3]
def baseStart_576425 : Nat := 118140960795 + 576425 * 2 ^ 59
def prefixEnd_576425 : Nat := 4983230072969 + 3 ^ 40 * 576425 * 2
def baseEnd_576425 : Nat := 197322057512008312157717

theorem tailTrace_576425 : CollatzResearch.WordTrace tailWord_576425 prefixEnd_576425 197322057512008312157717 := by
  unfold tailWord_576425
  simp only [CollatzResearch.WordTrace]
  refine ⟨21023946936718145397458729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14015964624478763598305819 21023946936718145397458729)
  ·
    refine ⟨15767960202538609048094047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21023946936718145397458729 15767960202538609048094047)
    ·
      refine ⟨23651940303807913572141071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15767960202538609048094047 23651940303807913572141071)
      ·
        refine ⟨35477910455711870358211607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23651940303807913572141071 35477910455711870358211607)
        ·
          refine ⟨53216865683567805537317411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35477910455711870358211607 53216865683567805537317411)
          ·
            refine ⟨79825298525351708305976117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53216865683567805537317411 79825298525351708305976117)
            ·
              refine ⟨7483621736751722653685261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79825298525351708305976117 7483621736751722653685261)
              ·
                refine ⟨2806358151281895995131973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7483621736751722653685261 2806358151281895995131973)
                ·
                  refine ⟨526192153365355499087245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2806358151281895995131973 526192153365355499087245)
                  ·
                    refine ⟨197322057512008312157717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 526192153365355499087245 197322057512008312157717)
                    ·
                      rfl

theorem cell22_576425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 3].length) (baseStart_576425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576425 prefixEnd_576425 := by exact prefixLift 576425
  have htrace : WordTrace (prefixWord ++ tailWord_576425) baseStart_576425 baseEnd_576425 := by
    simpa [prefixWord, tailWord_576425, baseEnd_576425] using wordTrace_append hprefix tailTrace_576425
  have hstable : (prefixWord ++ tailWord_576425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576425).length < 2 ^ (prefixWord ++ tailWord_576425).sum := by decide
  have hdescent : baseEnd_576425 < baseStart_576425 := by decide
  rcases family_descends (prefixWord ++ tailWord_576425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576442 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 2, 3]
def baseStart_576442 : Nat := 118140960795 + 576442 * 2 ^ 59
def prefixEnd_576442 : Nat := 4983230072969 + 3 ^ 40 * 576442 * 2
def baseEnd_576442 : Nat := 197327876959425934482665

theorem tailTrace_576442 : CollatzResearch.WordTrace tailWord_576442 prefixEnd_576442 197327876959425934482665 := by
  unfold tailWord_576442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5256141744414139325206895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14016377985104371533885053 5256141744414139325206895)
  ·
    refine ⟨7884212616621208987810343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5256141744414139325206895 7884212616621208987810343)
    ·
      refine ⟨11826318924931813481715515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7884212616621208987810343 11826318924931813481715515)
      ·
        refine ⟨17739478387397720222573273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11826318924931813481715515 17739478387397720222573273)
        ·
          refine ⟨13304608790548290166929955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17739478387397720222573273 13304608790548290166929955)
          ·
            refine ⟨19956913185822435250394933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13304608790548290166929955 19956913185822435250394933)
            ·
              refine ⟨1870960611170853304724525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19956913185822435250394933 1870960611170853304724525)
              ·
                refine ⟨701610229189069989271697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1870960611170853304724525 701610229189069989271697)
                ·
                  refine ⟨526207671891802491953773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 701610229189069989271697 526207671891802491953773)
                  ·
                    refine ⟨197327876959425934482665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 526207671891802491953773 197327876959425934482665)
                    ·
                      rfl

theorem cell22_576442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_576442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576442 prefixEnd_576442 := by exact prefixLift 576442
  have htrace : WordTrace (prefixWord ++ tailWord_576442) baseStart_576442 baseEnd_576442 := by
    simpa [prefixWord, tailWord_576442, baseEnd_576442] using wordTrace_append hprefix tailTrace_576442
  have hstable : (prefixWord ++ tailWord_576442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576442).length < 2 ^ (prefixWord ++ tailWord_576442).sum := by decide
  have hdescent : baseEnd_576442 < baseStart_576442 := by decide
  rcases family_descends (prefixWord ++ tailWord_576442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576551 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 5]
def baseStart_576551 : Nat := 118140960795 + 576551 * 2 ^ 59
def prefixEnd_576551 : Nat := 4983230072969 + 3 ^ 40 * 576551 * 2
def baseEnd_576551 : Nat := 65788396628995327835777

theorem tailTrace_576551 : CollatzResearch.WordTrace tailWord_576551 prefixEnd_576551 65788396628995327835777 := by
  unfold tailWord_576551
  simp only [CollatzResearch.WordTrace]
  refine ⟨21028542534261668916545507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14019028356174445944363671 21028542534261668916545507)
  ·
    refine ⟨31542813801392503374818261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21028542534261668916545507 31542813801392503374818261)
    ·
      refine ⟨739284698470136797847303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 31542813801392503374818261 739284698470136797847303)
      ·
        refine ⟨1108927047705205196770955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739284698470136797847303 1108927047705205196770955)
        ·
          refine ⟨1663390571557807795156433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108927047705205196770955 1663390571557807795156433)
          ·
            refine ⟨1247542928668355846367325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663390571557807795156433 1247542928668355846367325)
            ·
              refine ⟨467828598250633442387747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1247542928668355846367325 467828598250633442387747)
              ·
                refine ⟨701742897375950163581621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467828598250633442387747 701742897375950163581621)
                ·
                  refine ⟨65788396628995327835777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 701742897375950163581621 65788396628995327835777)
                  ·
                    rfl

theorem cell22_576551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 5].length) (baseStart_576551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576551 prefixEnd_576551 := by exact prefixLift 576551
  have htrace : WordTrace (prefixWord ++ tailWord_576551) baseStart_576551 baseEnd_576551 := by
    simpa [prefixWord, tailWord_576551, baseEnd_576551] using wordTrace_append hprefix tailTrace_576551
  have hstable : (prefixWord ++ tailWord_576551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576551).length < 2 ^ (prefixWord ++ tailWord_576551).sum := by decide
  have hdescent : baseEnd_576551 < baseStart_576551 := by decide
  rcases family_descends (prefixWord ++ tailWord_576551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576594 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_576594 : Nat := 118140960795 + 576594 * 2 ^ 59
def prefixEnd_576594 : Nat := 4983230072969 + 3 ^ 40 * 576594 * 2
def baseEnd_576594 : Nat := 197379909665748204682199

theorem tailTrace_576594 : CollatzResearch.WordTrace tailWord_576594 prefixEnd_576594 197379909665748204682199 := by
  unfold tailWord_576594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5257527718276471815090209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14020073915403924840240557 5257527718276471815090209)
  ·
    refine ⟨3943145788707353861317657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5257527718276471815090209 3943145788707353861317657)
    ·
      refine ⟨2957359341530515395988243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3943145788707353861317657 2957359341530515395988243)
      ·
        refine ⟨4436039012295773093982365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957359341530515395988243 4436039012295773093982365)
        ·
          refine ⟨1663514629610914910243387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4436039012295773093982365 1663514629610914910243387)
          ·
            refine ⟨2495271944416372365365081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663514629610914910243387 2495271944416372365365081)
            ·
              refine ⟨1871453958312279274023811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2495271944416372365365081 1871453958312279274023811)
              ·
                refine ⟨2807180937468418911035717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871453958312279274023811 2807180937468418911035717)
                ·
                  refine ⟨526346425775328545819197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2807180937468418911035717 526346425775328545819197)
                  ·
                    refine ⟨197379909665748204682199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 526346425775328545819197 197379909665748204682199)
                    ·
                      rfl

theorem cell22_576594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_576594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576594 prefixEnd_576594 := by exact prefixLift 576594
  have htrace : WordTrace (prefixWord ++ tailWord_576594) baseStart_576594 baseEnd_576594 := by
    simpa [prefixWord, tailWord_576594, baseEnd_576594] using wordTrace_append hprefix tailTrace_576594
  have hstable : (prefixWord ++ tailWord_576594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576594).length < 2 ^ (prefixWord ++ tailWord_576594).sum := by decide
  have hdescent : baseEnd_576594 < baseStart_576594 := by decide
  rcases family_descends (prefixWord ++ tailWord_576594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576635 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 9]
def baseStart_576635 : Nat := 118140960795 + 576635 * 2 ^ 59
def prefixEnd_576635 : Nat := 4983230072969 + 3 ^ 40 * 576635 * 2
def baseEnd_576635 : Nat := 65797981601212588135691

theorem tailTrace_576635 : CollatzResearch.WordTrace tailWord_576635 prefixEnd_576635 65797981601212588135691 := by
  unfold tailWord_576635
  simp only [CollatzResearch.WordTrace]
  refine ⟨21031606265957351262603359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14021070843971567508402239 21031606265957351262603359)
  ·
    refine ⟨31547409398936026893905039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21031606265957351262603359 31547409398936026893905039)
    ·
      refine ⟨47321114098404040340857559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31547409398936026893905039 47321114098404040340857559)
      ·
        refine ⟨70981671147606060511286339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47321114098404040340857559 70981671147606060511286339)
        ·
          refine ⟨106472506721409090766929509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70981671147606060511286339 106472506721409090766929509)
          ·
            refine ⟨19963595010264204518799283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106472506721409090766929509 19963595010264204518799283)
            ·
              refine ⟨29945392515396306778198925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19963595010264204518799283 29945392515396306778198925)
              ·
                refine ⟨11229522193273615041824597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29945392515396306778198925 11229522193273615041824597)
                ·
                  refine ⟨65797981601212588135691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11229522193273615041824597 65797981601212588135691)
                  ·
                    rfl

theorem cell22_576635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 9].length) (baseStart_576635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576635 prefixEnd_576635 := by exact prefixLift 576635
  have htrace : WordTrace (prefixWord ++ tailWord_576635) baseStart_576635 baseEnd_576635 := by
    simpa [prefixWord, tailWord_576635, baseEnd_576635] using wordTrace_append hprefix tailTrace_576635
  have hstable : (prefixWord ++ tailWord_576635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576635).length < 2 ^ (prefixWord ++ tailWord_576635).sum := by decide
  have hdescent : baseEnd_576635 < baseStart_576635 := by decide
  rcases family_descends (prefixWord ++ tailWord_576635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576712 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_576712 : Nat := 118140960795 + 576712 * 2 ^ 59
def prefixEnd_576712 : Nat := 4983230072969 + 3 ^ 40 * 576712 * 2
def baseEnd_576712 : Nat := 197420303477235230231837

theorem tailTrace_576712 : CollatzResearch.WordTrace tailWord_576712 prefixEnd_576712 197420303477235230231837 := by
  unfold tailWord_576712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517207343339196706578195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14022943124452262275437593 10517207343339196706578195)
  ·
    refine ⟨15775811015008795059867293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10517207343339196706578195 15775811015008795059867293)
    ·
      refine ⟨5915929130628298147450235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15775811015008795059867293 5915929130628298147450235)
      ·
        refine ⟨8873893695942447221175353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5915929130628298147450235 8873893695942447221175353)
        ·
          refine ⟨6655420271956835415881515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8873893695942447221175353 6655420271956835415881515)
          ·
            refine ⟨9983130407935253123822273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6655420271956835415881515 9983130407935253123822273)
            ·
              refine ⟨7487347805951439842866705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9983130407935253123822273 7487347805951439842866705)
              ·
                refine ⟨5615510854463579882150029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7487347805951439842866705 5615510854463579882150029)
                ·
                  refine ⟨2105816570423842455806261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5615510854463579882150029 2105816570423842455806261)
                  ·
                    refine ⟨197420303477235230231837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2105816570423842455806261 197420303477235230231837)
                    ·
                      rfl

theorem cell22_576712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_576712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576712 prefixEnd_576712 := by exact prefixLift 576712
  have htrace : WordTrace (prefixWord ++ tailWord_576712) baseStart_576712 baseEnd_576712 := by
    simpa [prefixWord, tailWord_576712, baseEnd_576712] using wordTrace_append hprefix tailTrace_576712
  have hstable : (prefixWord ++ tailWord_576712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576712).length < 2 ^ (prefixWord ++ tailWord_576712).sum := by decide
  have hdescent : baseEnd_576712 < baseStart_576712 := by decide
  rcases family_descends (prefixWord ++ tailWord_576712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576714 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_576714 : Nat := 118140960795 + 576714 * 2 ^ 59
def prefixEnd_576714 : Nat := 4983230072969 + 3 ^ 40 * 576714 * 2
def baseEnd_576714 : Nat := 65806996039369297227277

theorem tailTrace_576714 : CollatzResearch.WordTrace tailWord_576714 prefixEnd_576714 65806996039369297227277 := by
  unfold tailWord_576714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5258621908167786938682299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14022991755114098503152797 5258621908167786938682299)
  ·
    refine ⟨7887932862251680408023449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5258621908167786938682299 7887932862251680408023449)
    ·
      refine ⟨5915949646688760306017587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7887932862251680408023449 5915949646688760306017587)
      ·
        refine ⟨8873924470033140459026381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5915949646688760306017587 8873924470033140459026381)
        ·
          refine ⟨3327721676262427672134893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8873924470033140459026381 3327721676262427672134893)
          ·
            refine ⟨1247895628598410377050585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3327721676262427672134893 1247895628598410377050585)
            ·
              refine ⟨935921721448807782787939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247895628598410377050585 935921721448807782787939)
              ·
                refine ⟨1403882582173211674181909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935921721448807782787939 1403882582173211674181909)
                ·
                  refine ⟨65806996039369297227277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1403882582173211674181909 65806996039369297227277)
                  ·
                    rfl

theorem cell22_576714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_576714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576714 prefixEnd_576714 := by exact prefixLift 576714
  have htrace : WordTrace (prefixWord ++ tailWord_576714) baseStart_576714 baseEnd_576714 := by
    simpa [prefixWord, tailWord_576714, baseEnd_576714] using wordTrace_append hprefix tailTrace_576714
  have hstable : (prefixWord ++ tailWord_576714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576714).length < 2 ^ (prefixWord ++ tailWord_576714).sum := by decide
  have hdescent : baseEnd_576714 < baseStart_576714 := by decide
  rcases family_descends (prefixWord ++ tailWord_576714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576727 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 1, 6]
def baseStart_576727 : Nat := 118140960795 + 576727 * 2 ^ 59
def prefixEnd_576727 : Nat := 4983230072969 + 3 ^ 40 * 576727 * 2
def baseEnd_576727 : Nat := 197425438283780191106791

theorem tailTrace_576727 : CollatzResearch.WordTrace tailWord_576727 prefixEnd_576727 197425438283780191106791 := by
  unfold tailWord_576727
  simp only [CollatzResearch.WordTrace]
  refine ⟨21034961781624050974952435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14023307854416033983301623 21034961781624050974952435)
  ·
    refine ⟨31552442672436076462428653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21034961781624050974952435 31552442672436076462428653)
    ·
      refine ⟨11832166002163528673410745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31552442672436076462428653 11832166002163528673410745)
      ·
        refine ⟨8874124501622646505058059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11832166002163528673410745 8874124501622646505058059)
        ·
          refine ⟨13311186752433969757587089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8874124501622646505058059 13311186752433969757587089)
          ·
            refine ⟨9983390064325477318190317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13311186752433969757587089 9983390064325477318190317)
            ·
              refine ⟨3743771274122053994321369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9983390064325477318190317 3743771274122053994321369)
              ·
                refine ⟨2807828455591540495741027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3743771274122053994321369 2807828455591540495741027)
                ·
                  refine ⟨4211742683387310743611541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807828455591540495741027 4211742683387310743611541)
                  ·
                    refine ⟨197425438283780191106791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4211742683387310743611541 197425438283780191106791)
                    ·
                      rfl

theorem cell22_576727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_576727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576727 prefixEnd_576727 := by exact prefixLift 576727
  have htrace : WordTrace (prefixWord ++ tailWord_576727) baseStart_576727 baseEnd_576727 := by
    simpa [prefixWord, tailWord_576727, baseEnd_576727] using wordTrace_append hprefix tailTrace_576727
  have hstable : (prefixWord ++ tailWord_576727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576727).length < 2 ^ (prefixWord ++ tailWord_576727).sum := by decide
  have hdescent : baseEnd_576727 < baseStart_576727 := by decide
  rcases family_descends (prefixWord ++ tailWord_576727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576733 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_576733 : Nat := 118140960795 + 576733 * 2 ^ 59
def prefixEnd_576733 : Nat := 4983230072969 + 3 ^ 40 * 576733 * 2
def baseEnd_576733 : Nat := 197427492206398175456773

theorem tailTrace_576733 : CollatzResearch.WordTrace tailWord_576733 prefixEnd_576733 197427492206398175456773 := by
  unfold tailWord_576733
  simp only [CollatzResearch.WordTrace]
  refine ⟨21035180619602313999670853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14023453746401542666447235 21035180619602313999670853)
  ·
    refine ⟨3944096366175433874938285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21035180619602313999670853 3944096366175433874938285)
    ·
      refine ⟨1479036137315787703101857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3944096366175433874938285 1479036137315787703101857)
      ·
        refine ⟨1109277102986840777326393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479036137315787703101857 1109277102986840777326393)
        ·
          refine ⟨831957827240130582994795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1109277102986840777326393 831957827240130582994795)
          ·
            refine ⟨1247936740860195874492193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831957827240130582994795 1247936740860195874492193)
            ·
              refine ⟨935952555645146905869145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247936740860195874492193 935952555645146905869145)
              ·
                refine ⟨701964416733860179401859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935952555645146905869145 701964416733860179401859)
                ·
                  refine ⟨1052946625100790269102789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701964416733860179401859 1052946625100790269102789)
                  ·
                    refine ⟨197427492206398175456773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1052946625100790269102789 197427492206398175456773)
                    ·
                      rfl

theorem cell22_576733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_576733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576733 prefixEnd_576733 := by exact prefixLift 576733
  have htrace : WordTrace (prefixWord ++ tailWord_576733) baseStart_576733 baseEnd_576733 := by
    simpa [prefixWord, tailWord_576733, baseEnd_576733] using wordTrace_append hprefix tailTrace_576733
  have hstable : (prefixWord ++ tailWord_576733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576733).length < 2 ^ (prefixWord ++ tailWord_576733).sum := by decide
  have hdescent : baseEnd_576733 < baseStart_576733 := by decide
  rcases family_descends (prefixWord ++ tailWord_576733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576744 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_576744 : Nat := 118140960795 + 576744 * 2 ^ 59
def prefixEnd_576744 : Nat := 4983230072969 + 3 ^ 40 * 576744 * 2
def baseEnd_576744 : Nat := 197431257731197813431739

theorem tailTrace_576744 : CollatzResearch.WordTrace tailWord_576744 prefixEnd_576744 197431257731197813431739 := by
  unfold tailWord_576744
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517790911281231439160643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14023721215041641918880857 10517790911281231439160643)
  ·
    refine ⟨15776686366921847158740965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10517790911281231439160643 15776686366921847158740965)
    ·
      refine ⟨2958128693797846342263931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15776686366921847158740965 2958128693797846342263931)
      ·
        refine ⟨4437193040696769513395897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2958128693797846342263931 4437193040696769513395897)
        ·
          refine ⟨3327894780522577135046923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4437193040696769513395897 3327894780522577135046923)
          ·
            refine ⟨4991842170783865702570385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327894780522577135046923 4991842170783865702570385)
            ·
              refine ⟨3743881628087899276927789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4991842170783865702570385 3743881628087899276927789)
              ·
                refine ⟨1403955610532962228847921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3743881628087899276927789 1403955610532962228847921)
                ·
                  refine ⟨1052966707899721671635941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1403955610532962228847921 1052966707899721671635941)
                  ·
                    refine ⟨197431257731197813431739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1052966707899721671635941 197431257731197813431739)
                    ·
                      rfl

theorem cell22_576744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_576744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576744 prefixEnd_576744 := by exact prefixLift 576744
  have htrace : WordTrace (prefixWord ++ tailWord_576744) baseStart_576744 baseEnd_576744 := by
    simpa [prefixWord, tailWord_576744, baseEnd_576744] using wordTrace_append hprefix tailTrace_576744
  have hstable : (prefixWord ++ tailWord_576744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576744).length < 2 ^ (prefixWord ++ tailWord_576744).sum := by decide
  have hdescent : baseEnd_576744 < baseStart_576744 := by decide
  rcases family_descends (prefixWord ++ tailWord_576744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576821 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 5]
def baseStart_576821 : Nat := 118140960795 + 576821 * 2 ^ 59
def prefixEnd_576821 : Nat := 4983230072969 + 3 ^ 40 * 576821 * 2
def baseEnd_576821 : Nat := 65819205468265093085501

theorem tailTrace_576821 : CollatzResearch.WordTrace tailWord_576821 prefixEnd_576821 65819205468265093085501 := by
  unfold tailWord_576821
  simp only [CollatzResearch.WordTrace]
  refine ⟨21038390243283505028874317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14025593495522336685916211 21038390243283505028874317)
  ·
    refine ⟨7889396341231314385827869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21038390243283505028874317 7889396341231314385827869)
    ·
      refine ⟨2958523627961742894685451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7889396341231314385827869 2958523627961742894685451)
      ·
        refine ⟨4437785441942614342028177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2958523627961742894685451 4437785441942614342028177)
        ·
          refine ⟨3328339081456960756521133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4437785441942614342028177 3328339081456960756521133)
          ·
            refine ⟨1248127155546360283695425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3328339081456960756521133 1248127155546360283695425)
            ·
              refine ⟨936095366659770212771569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248127155546360283695425 936095366659770212771569)
              ·
                refine ⟨702071524994827659578677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 936095366659770212771569 702071524994827659578677)
                ·
                  refine ⟨65819205468265093085501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 702071524994827659578677 65819205468265093085501)
                  ·
                    rfl

theorem cell22_576821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_576821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576821 prefixEnd_576821 := by exact prefixLift 576821
  have htrace : WordTrace (prefixWord ++ tailWord_576821) baseStart_576821 baseEnd_576821 := by
    simpa [prefixWord, tailWord_576821, baseEnd_576821] using wordTrace_append hprefix tailTrace_576821
  have hstable : (prefixWord ++ tailWord_576821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576821).length < 2 ^ (prefixWord ++ tailWord_576821).sum := by decide
  have hdescent : baseEnd_576821 < baseStart_576821 := by decide
  rcases family_descends (prefixWord ++ tailWord_576821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576825 : List Nat := [1, 2, 1, 6, 2, 1, 1, 4, 1, 3]
def baseStart_576825 : Nat := 118140960795 + 576825 * 2 ^ 59
def prefixEnd_576825 : Nat := 4983230072969 + 3 ^ 40 * 576825 * 2
def baseEnd_576825 : Nat := 197458985686540602156491

theorem tailTrace_576825 : CollatzResearch.WordTrace tailWord_576825 prefixEnd_576825 197458985686540602156491 := by
  unfold tailWord_576825
  simp only [CollatzResearch.WordTrace]
  refine ⟨21038536135269013712019929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14025690756846009141346619 21038536135269013712019929)
  ·
    refine ⟨15778902101451760284014947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21038536135269013712019929 15778902101451760284014947)
    ·
      refine ⟨23668353152177640426022421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15778902101451760284014947 23668353152177640426022421)
      ·
        refine ⟨1109454054008326894969801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23668353152177640426022421 1109454054008326894969801)
        ·
          refine ⟨832090540506245171227351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1109454054008326894969801 832090540506245171227351)
          ·
            refine ⟨1248135810759367756841027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832090540506245171227351 1248135810759367756841027)
            ·
              refine ⟨1872203716139051635261541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248135810759367756841027 1872203716139051635261541)
              ·
                refine ⟨351038196776072181611539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1872203716139051635261541 351038196776072181611539)
                ·
                  refine ⟨526557295164108272417309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351038196776072181611539 526557295164108272417309)
                  ·
                    refine ⟨197458985686540602156491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 526557295164108272417309 197458985686540602156491)
                    ·
                      rfl

theorem cell22_576825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 1, 3].length) (baseStart_576825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576825 prefixEnd_576825 := by exact prefixLift 576825
  have htrace : WordTrace (prefixWord ++ tailWord_576825) baseStart_576825 baseEnd_576825 := by
    simpa [prefixWord, tailWord_576825, baseEnd_576825] using wordTrace_append hprefix tailTrace_576825
  have hstable : (prefixWord ++ tailWord_576825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576825).length < 2 ^ (prefixWord ++ tailWord_576825).sum := by decide
  have hdescent : baseEnd_576825 < baseStart_576825 := by decide
  rcases family_descends (prefixWord ++ tailWord_576825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576836 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_576836 : Nat := 118140960795 + 576836 * 2 ^ 59
def prefixEnd_576836 : Nat := 4983230072969 + 3 ^ 40 * 576836 * 2
def baseEnd_576836 : Nat := 197462751211340240131457

theorem tailTrace_576836 : CollatzResearch.WordTrace tailWord_576836 prefixEnd_576836 197462751211340240131457 := by
  unfold tailWord_576836
  simp only [CollatzResearch.WordTrace]
  refine ⟨10519468669114581295335181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14025958225486108393780241 10519468669114581295335181)
  ·
    refine ⟨3944800750917967985750693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10519468669114581295335181 3944800750917967985750693)
    ·
      refine ⟨739650140797118997328255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3944800750917967985750693 739650140797118997328255)
      ·
        refine ⟨1109475211195678495992383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739650140797118997328255 1109475211195678495992383)
        ·
          refine ⟨1664212816793517743988575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109475211195678495992383 1664212816793517743988575)
          ·
            refine ⟨2496319225190276615982863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664212816793517743988575 2496319225190276615982863)
            ·
              refine ⟨3744478837785414923974295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496319225190276615982863 3744478837785414923974295)
              ·
                refine ⟨5616718256678122385961443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3744478837785414923974295 5616718256678122385961443)
                ·
                  refine ⟨8425077385017183578942165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5616718256678122385961443 8425077385017183578942165)
                  ·
                    refine ⟨197462751211340240131457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8425077385017183578942165 197462751211340240131457)
                    ·
                      rfl

theorem cell22_576836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_576836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576836 prefixEnd_576836 := by exact prefixLift 576836
  have htrace : WordTrace (prefixWord ++ tailWord_576836) baseStart_576836 baseEnd_576836 := by
    simpa [prefixWord, tailWord_576836, baseEnd_576836] using wordTrace_append hprefix tailTrace_576836
  have hstable : (prefixWord ++ tailWord_576836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576836).length < 2 ^ (prefixWord ++ tailWord_576836).sum := by decide
  have hdescent : baseEnd_576836 < baseStart_576836 := by decide
  rcases family_descends (prefixWord ++ tailWord_576836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576849 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 6]
def baseStart_576849 : Nat := 118140960795 + 576849 * 2 ^ 59
def prefixEnd_576849 : Nat := 4983230072969 + 3 ^ 40 * 576849 * 2
def baseEnd_576849 : Nat := 65822400459004179852139

theorem tailTrace_576849 : CollatzResearch.WordTrace tailWord_576849 prefixEnd_576849 65822400459004179852139 := by
  unfold tailWord_576849
  simp only [CollatzResearch.WordTrace]
  refine ⟨21039411487182065810893601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14026274324788043873929067 21039411487182065810893601)
  ·
    refine ⟨15779558615386549358170201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21039411487182065810893601 15779558615386549358170201)
    ·
      refine ⟨11834668961539912018627651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15779558615386549358170201 11834668961539912018627651)
      ·
        refine ⟨17752003442309868027941477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11834668961539912018627651 17752003442309868027941477)
        ·
          refine ⟨3328500645433100255239027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17752003442309868027941477 3328500645433100255239027)
          ·
            refine ⟨4992750968149650382858541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3328500645433100255239027 4992750968149650382858541)
            ·
              refine ⟨1872281613056118893571953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4992750968149650382858541 1872281613056118893571953)
              ·
                refine ⟨1404211209792089170178965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1872281613056118893571953 1404211209792089170178965)
                ·
                  refine ⟨65822400459004179852139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1404211209792089170178965 65822400459004179852139)
                  ·
                    rfl

theorem cell22_576849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_576849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576849 prefixEnd_576849 := by exact prefixLift 576849
  have htrace : WordTrace (prefixWord ++ tailWord_576849) baseStart_576849 baseEnd_576849 := by
    simpa [prefixWord, tailWord_576849, baseEnd_576849] using wordTrace_append hprefix tailTrace_576849
  have hstable : (prefixWord ++ tailWord_576849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576849).length < 2 ^ (prefixWord ++ tailWord_576849).sum := by decide
  have hdescent : baseEnd_576849 < baseStart_576849 := by decide
  rcases family_descends (prefixWord ++ tailWord_576849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576868 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_576868 : Nat := 118140960795 + 576868 * 2 ^ 59
def prefixEnd_576868 : Nat := 4983230072969 + 3 ^ 40 * 576868 * 2
def baseEnd_576868 : Nat := 197473705465302823331359

theorem tailTrace_576868 : CollatzResearch.WordTrace tailWord_576868 prefixEnd_576868 197473705465302823331359 := by
  unfold tailWord_576868
  simp only [CollatzResearch.WordTrace]
  refine ⟨10520052237056616027917629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14026736316075488037223505 10520052237056616027917629)
  ·
    refine ⟨3945019588896231010469111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10520052237056616027917629 3945019588896231010469111)
    ·
      refine ⟨5917529383344346515703667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3945019588896231010469111 5917529383344346515703667)
      ·
        refine ⟨8876294075016519773555501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5917529383344346515703667 8876294075016519773555501)
        ·
          refine ⟨3328610278131194915083313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8876294075016519773555501 3328610278131194915083313)
          ·
            refine ⟨2496457708598396186312485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3328610278131194915083313 2496457708598396186312485)
            ·
              refine ⟨468085820362199284933591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2496457708598396186312485 468085820362199284933591)
              ·
                refine ⟨702128730543298927400387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468085820362199284933591 702128730543298927400387)
                ·
                  refine ⟨1053193095814948391100581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702128730543298927400387 1053193095814948391100581)
                  ·
                    refine ⟨197473705465302823331359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1053193095814948391100581 197473705465302823331359)
                    ·
                      rfl

theorem cell22_576868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_576868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576868 prefixEnd_576868 := by exact prefixLift 576868
  have htrace : WordTrace (prefixWord ++ tailWord_576868) baseStart_576868 baseEnd_576868 := by
    simpa [prefixWord, tailWord_576868, baseEnd_576868] using wordTrace_append hprefix tailTrace_576868
  have hstable : (prefixWord ++ tailWord_576868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576868).length < 2 ^ (prefixWord ++ tailWord_576868).sum := by decide
  have hdescent : baseEnd_576868 < baseStart_576868 := by decide
  rcases family_descends (prefixWord ++ tailWord_576868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576879 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 4, 4]
def baseStart_576879 : Nat := 118140960795 + 576879 * 2 ^ 59
def prefixEnd_576879 : Nat := 4983230072969 + 3 ^ 40 * 576879 * 2
def baseEnd_576879 : Nat := 197477470990102461306325

theorem tailTrace_576879 : CollatzResearch.WordTrace tailWord_576879 prefixEnd_576879 197477470990102461306325 := by
  unfold tailWord_576879
  simp only [CollatzResearch.WordTrace]
  refine ⟨21040505677073380934485691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14027003784715587289657127 21040505677073380934485691)
  ·
    refine ⟨31560758515610071401728537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21040505677073380934485691 31560758515610071401728537)
    ·
      refine ⟨23670568886707553551296403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31560758515610071401728537 23670568886707553551296403)
      ·
        refine ⟨35505853330061330326944605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23670568886707553551296403 35505853330061330326944605)
        ·
          refine ⟨13314694998772998872604227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35505853330061330326944605 13314694998772998872604227)
          ·
            refine ⟨19972042498159498308906341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13314694998772998872604227 19972042498159498308906341)
            ·
              refine ⟨3744757968404905932919939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19972042498159498308906341 3744757968404905932919939)
              ·
                refine ⟨5617136952607358899379909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3744757968404905932919939 5617136952607358899379909)
                ·
                  refine ⟨1053213178613879793633733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5617136952607358899379909 1053213178613879793633733)
                  ·
                    refine ⟨197477470990102461306325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1053213178613879793633733 197477470990102461306325)
                    ·
                      rfl

theorem cell22_576879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_576879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576879 prefixEnd_576879 := by exact prefixLift 576879
  have htrace : WordTrace (prefixWord ++ tailWord_576879) baseStart_576879 baseEnd_576879 := by
    simpa [prefixWord, tailWord_576879, baseEnd_576879] using wordTrace_append hprefix tailTrace_576879
  have hstable : (prefixWord ++ tailWord_576879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576879).length < 2 ^ (prefixWord ++ tailWord_576879).sum := by decide
  have hdescent : baseEnd_576879 < baseStart_576879 := by decide
  rcases family_descends (prefixWord ++ tailWord_576879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576943 : List Nat := [1, 1, 2, 1, 2, 2, 1, 8, 1, 3]
def baseStart_576943 : Nat := 118140960795 + 576943 * 2 ^ 59
def prefixEnd_576943 : Nat := 4983230072969 + 3 ^ 40 * 576943 * 2
def baseEnd_576943 : Nat := 197499379498027627706129

theorem tailTrace_576943 : CollatzResearch.WordTrace tailWord_576943 prefixEnd_576943 197499379498027627706129 := by
  unfold tailWord_576943
  simp only [CollatzResearch.WordTrace]
  refine ⟨21042839948841519864815483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14028559965894346576543655 21042839948841519864815483)
  ·
    refine ⟨31564259923262279797223225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21042839948841519864815483 31564259923262279797223225)
    ·
      refine ⟨23673194942446709847917419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31564259923262279797223225 23673194942446709847917419)
      ·
        refine ⟨35509792413670064771876129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23673194942446709847917419 35509792413670064771876129)
        ·
          refine ⟨26632344310252548578907097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35509792413670064771876129 26632344310252548578907097)
          ·
            refine ⟨19974258232689411434180323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26632344310252548578907097 19974258232689411434180323)
            ·
              refine ⟨29961387349034117151270485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19974258232689411434180323 29961387349034117151270485)
              ·
                refine ⟨351110007996493560366451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 29961387349034117151270485 351110007996493560366451)
                ·
                  refine ⟨526665011994740340549677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351110007996493560366451 526665011994740340549677)
                  ·
                    refine ⟨197499379498027627706129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 526665011994740340549677 197499379498027627706129)
                    ·
                      rfl

theorem cell22_576943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 1, 3].length) (baseStart_576943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576943 prefixEnd_576943 := by exact prefixLift 576943
  have htrace : WordTrace (prefixWord ++ tailWord_576943) baseStart_576943 baseEnd_576943 := by
    simpa [prefixWord, tailWord_576943, baseEnd_576943] using wordTrace_append hprefix tailTrace_576943
  have hstable : (prefixWord ++ tailWord_576943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576943).length < 2 ^ (prefixWord ++ tailWord_576943).sum := by decide
  have hdescent : baseEnd_576943 < baseStart_576943 := by decide
  rcases family_descends (prefixWord ++ tailWord_576943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577016 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_577016 : Nat := 118140960795 + 577016 * 2 ^ 59
def prefixEnd_577016 : Nat := 4983230072969 + 3 ^ 40 * 577016 * 2
def baseEnd_577016 : Nat := 197524368889879770630905

theorem tailTrace_577016 : CollatzResearch.WordTrace tailWord_577016 prefixEnd_577016 197524368889879770630905 := by
  unfold tailWord_577016
  simp only [CollatzResearch.WordTrace]
  refine ⟨10522751238788526666111451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14030334985051368888148601 10522751238788526666111451)
  ·
    refine ⟨15784126858182789999167177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10522751238788526666111451 15784126858182789999167177)
    ·
      refine ⟨11838095143637092499375383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15784126858182789999167177 11838095143637092499375383)
      ·
        refine ⟨17757142715455638749063075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11838095143637092499375383 17757142715455638749063075)
        ·
          refine ⟨26635714073183458123594613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17757142715455638749063075 26635714073183458123594613)
          ·
            refine ⟨2497098194360949199086995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26635714073183458123594613 2497098194360949199086995)
            ·
              refine ⟨3745647291541423798630493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497098194360949199086995 3745647291541423798630493)
              ·
                refine ⟨1404617734328033924486435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3745647291541423798630493 1404617734328033924486435)
                ·
                  refine ⟨2106926601492050886729653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404617734328033924486435 2106926601492050886729653)
                  ·
                    refine ⟨197524368889879770630905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2106926601492050886729653 197524368889879770630905)
                    ·
                      rfl

theorem cell22_577016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_577016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577016 prefixEnd_577016 := by exact prefixLift 577016
  have htrace : WordTrace (prefixWord ++ tailWord_577016) baseStart_577016 baseEnd_577016 := by
    simpa [prefixWord, tailWord_577016, baseEnd_577016] using wordTrace_append hprefix tailTrace_577016
  have hstable : (prefixWord ++ tailWord_577016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577016).length < 2 ^ (prefixWord ++ tailWord_577016).sum := by decide
  have hdescent : baseEnd_577016 < baseStart_577016 := by decide
  rcases family_descends (prefixWord ++ tailWord_577016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577035 : List Nat := [1, 1, 1, 1, 8, 1, 2, 3, 4]
def baseStart_577035 : Nat := 118140960795 + 577035 * 2 ^ 59
def prefixEnd_577035 : Nat := 4983230072969 + 3 ^ 40 * 577035 * 2
def baseEnd_577035 : Nat := 65843624326056684801949

theorem tailTrace_577035 : CollatzResearch.WordTrace tailWord_577035 prefixEnd_577035 65843624326056684801949 := by
  unfold tailWord_577035
  simp only [CollatzResearch.WordTrace]
  refine ⟨21046195464508219577164559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14030796976338813051443039 21046195464508219577164559)
  ·
    refine ⟨31569293196762329365746839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21046195464508219577164559 31569293196762329365746839)
    ·
      refine ⟨47353939795143494048620259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31569293196762329365746839 47353939795143494048620259)
      ·
        refine ⟨71030909692715241072930389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47353939795143494048620259 71030909692715241072930389)
        ·
          refine ⟨832393472961506731323403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 71030909692715241072930389 832393472961506731323403)
          ·
            refine ⟨1248590209442260096985105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832393472961506731323403 1248590209442260096985105)
            ·
              refine ⟨936442657081695072738829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248590209442260096985105 936442657081695072738829)
              ·
                refine ⟨351165996405635652277061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 936442657081695072738829 351165996405635652277061)
                ·
                  refine ⟨65843624326056684801949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351165996405635652277061 65843624326056684801949)
                  ·
                    rfl

theorem cell22_577035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 4].length) (baseStart_577035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577035 prefixEnd_577035 := by exact prefixLift 577035
  have htrace : WordTrace (prefixWord ++ tailWord_577035) baseStart_577035 baseEnd_577035 := by
    simpa [prefixWord, tailWord_577035, baseEnd_577035] using wordTrace_append hprefix tailTrace_577035
  have hstable : (prefixWord ++ tailWord_577035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577035).length < 2 ^ (prefixWord ++ tailWord_577035).sum := by decide
  have hdescent : baseEnd_577035 < baseStart_577035 := by decide
  rcases family_descends (prefixWord ++ tailWord_577035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577108 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 5]
def baseStart_577108 : Nat := 118140960795 + 577108 * 2 ^ 59
def prefixEnd_577108 : Nat := 4983230072969 + 3 ^ 40 * 577108 * 2
def baseEnd_577108 : Nat := 65851954123340732443541

theorem tailTrace_577108 : CollatzResearch.WordTrace tailWord_577108 prefixEnd_577108 65851954123340732443541 := by
  unfold tailWord_577108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10524428996621876522285989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14032571995495835363047985 10524428996621876522285989)
  ·
    refine ⟨1973330436866601847928623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10524428996621876522285989 1973330436866601847928623)
    ·
      refine ⟨2959995655299902771892935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1973330436866601847928623 2959995655299902771892935)
      ·
        refine ⟨4439993482949854157839403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2959995655299902771892935 4439993482949854157839403)
        ·
          refine ⟨6659990224424781236759105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4439993482949854157839403 6659990224424781236759105)
          ·
            refine ⟨4994992668318585927569329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6659990224424781236759105 4994992668318585927569329)
            ·
              refine ⟨3746244501238939445676997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4994992668318585927569329 3746244501238939445676997)
              ·
                refine ⟨702420843982301146064437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3746244501238939445676997 702420843982301146064437)
                ·
                  refine ⟨65851954123340732443541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 702420843982301146064437 65851954123340732443541)
                  ·
                    rfl

theorem cell22_577108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_577108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577108 prefixEnd_577108 := by exact prefixLift 577108
  have htrace : WordTrace (prefixWord ++ tailWord_577108) baseStart_577108 baseEnd_577108 := by
    simpa [prefixWord, tailWord_577108, baseEnd_577108] using wordTrace_append hprefix tailTrace_577108
  have hstable : (prefixWord ++ tailWord_577108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577108).length < 2 ^ (prefixWord ++ tailWord_577108).sum := by decide
  have hdescent : baseEnd_577108 < baseStart_577108 := by decide
  rcases family_descends (prefixWord ++ tailWord_577108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577125 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 5]
def baseStart_577125 : Nat := 118140960795 + 577125 * 2 ^ 59
def prefixEnd_577125 : Nat := 4983230072969 + 3 ^ 40 * 577125 * 2
def baseEnd_577125 : Nat := 65853893939146606551857

theorem tailTrace_577125 : CollatzResearch.WordTrace tailWord_577125 prefixEnd_577125 65853893939146606551857 := by
  unfold tailWord_577125
  simp only [CollatzResearch.WordTrace]
  refine ⟨21049478034182164947940829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14032985356121443298627219 21049478034182164947940829)
  ·
    refine ⟨7893554262818311855477811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21049478034182164947940829 7893554262818311855477811)
    ·
      refine ⟨11840331394227467783216717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7893554262818311855477811 11840331394227467783216717)
      ·
        refine ⟨4440124272835300418706269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11840331394227467783216717 4440124272835300418706269)
        ·
          refine ⟨1665046602313237657014851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4440124272835300418706269 1665046602313237657014851)
          ·
            refine ⟨2497569903469856485522277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665046602313237657014851 2497569903469856485522277)
            ·
              refine ⟨468294356900598091035427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2497569903469856485522277 468294356900598091035427)
              ·
                refine ⟨702441535350897136553141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468294356900598091035427 702441535350897136553141)
                ·
                  refine ⟨65853893939146606551857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 702441535350897136553141 65853893939146606551857)
                  ·
                    rfl

theorem cell22_577125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_577125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577125 prefixEnd_577125 := by exact prefixLift 577125
  have htrace : WordTrace (prefixWord ++ tailWord_577125) baseStart_577125 baseEnd_577125 := by
    simpa [prefixWord, tailWord_577125, baseEnd_577125] using wordTrace_append hprefix tailTrace_577125
  have hstable : (prefixWord ++ tailWord_577125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577125).length < 2 ^ (prefixWord ++ tailWord_577125).sum := by decide
  have hdescent : baseEnd_577125 < baseStart_577125 := by decide
  rcases family_descends (prefixWord ++ tailWord_577125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577168 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 4, 3]
def baseStart_577168 : Nat := 118140960795 + 577168 * 2 ^ 59
def prefixEnd_577168 : Nat := 4983230072969 + 3 ^ 40 * 577168 * 2
def baseEnd_577168 : Nat := 197576401596202040830439

theorem tailTrace_577168 : CollatzResearch.WordTrace tailWord_577168 prefixEnd_577168 197576401596202040830439 := by
  unfold tailWord_577168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10525523186513191645878079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14034030915350922194504105 10525523186513191645878079)
  ·
    refine ⟨15788284779769787468817119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10525523186513191645878079 15788284779769787468817119)
    ·
      refine ⟨23682427169654681203225679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15788284779769787468817119 23682427169654681203225679)
      ·
        refine ⟨35523640754482021804838519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23682427169654681203225679 35523640754482021804838519)
        ·
          refine ⟨53285461131723032707257779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35523640754482021804838519 53285461131723032707257779)
          ·
            refine ⟨79928191697584549060886669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53285461131723032707257779 79928191697584549060886669)
            ·
              refine ⟨29973071886594205897832501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79928191697584549060886669 29973071886594205897832501)
              ·
                refine ⟨2809975489368206802921797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29973071886594205897832501 2809975489368206802921797)
                ·
                  refine ⟨526870404256538775547837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2809975489368206802921797 526870404256538775547837)
                  ·
                    refine ⟨197576401596202040830439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 526870404256538775547837 197576401596202040830439)
                    ·
                      rfl

theorem cell22_577168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4, 3].length) (baseStart_577168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577168 prefixEnd_577168 := by exact prefixLift 577168
  have htrace : WordTrace (prefixWord ++ tailWord_577168) baseStart_577168 baseEnd_577168 := by
    simpa [prefixWord, tailWord_577168, baseEnd_577168] using wordTrace_append hprefix tailTrace_577168
  have hstable : (prefixWord ++ tailWord_577168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577168).length < 2 ^ (prefixWord ++ tailWord_577168).sum := by decide
  have hdescent : baseEnd_577168 < baseStart_577168 := by decide
  rcases family_descends (prefixWord ++ tailWord_577168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577185 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 1, 5]
def baseStart_577185 : Nat := 118140960795 + 577185 * 2 ^ 59
def prefixEnd_577185 : Nat := 4983230072969 + 3 ^ 40 * 577185 * 2
def baseEnd_577185 : Nat := 197582221043619663155387

theorem tailTrace_577185 : CollatzResearch.WordTrace tailWord_577185 prefixEnd_577185 197582221043619663155387 := by
  unfold tailWord_577185
  simp only [CollatzResearch.WordTrace]
  refine ⟨21051666413964795195125009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14034444275976530130083339 21051666413964795195125009)
  ·
    refine ⟨15788749810473596396343757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21051666413964795195125009 15788749810473596396343757)
    ·
      refine ⟨5920781178927598648628909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15788749810473596396343757 5920781178927598648628909)
      ·
        refine ⟨2220292942097849493235841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5920781178927598648628909 2220292942097849493235841)
        ·
          refine ⟨1665219706573387119926881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2220292942097849493235841 1665219706573387119926881)
          ·
            refine ⟨1248914779930040339945161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1665219706573387119926881 1248914779930040339945161)
            ·
              refine ⟨936686084947530254958871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248914779930040339945161 936686084947530254958871)
              ·
                refine ⟨1405029127421295382438307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936686084947530254958871 1405029127421295382438307)
                ·
                  refine ⟨2107543691131943073657461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405029127421295382438307 2107543691131943073657461)
                  ·
                    refine ⟨197582221043619663155387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2107543691131943073657461 197582221043619663155387)
                    ·
                      rfl

theorem cell22_577185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_577185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577185 prefixEnd_577185 := by exact prefixLift 577185
  have htrace : WordTrace (prefixWord ++ tailWord_577185) baseStart_577185 baseEnd_577185 := by
    simpa [prefixWord, tailWord_577185, baseEnd_577185] using wordTrace_append hprefix tailTrace_577185
  have hstable : (prefixWord ++ tailWord_577185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577185).length < 2 ^ (prefixWord ++ tailWord_577185).sum := by decide
  have hdescent : baseEnd_577185 < baseStart_577185 := by decide
  rcases family_descends (prefixWord ++ tailWord_577185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577206 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_577206 : Nat := 118140960795 + 577206 * 2 ^ 59
def prefixEnd_577206 : Nat := 4983230072969 + 3 ^ 40 * 577206 * 2
def baseEnd_577206 : Nat := 197589409772782608380323

theorem tailTrace_577206 : CollatzResearch.WordTrace tailWord_577206 prefixEnd_577206 197589409772782608380323 := by
  unfold tailWord_577206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315777021680544736352467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14034954897925810521092981 1315777021680544736352467)
  ·
    refine ⟨1973665532520817104528701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1315777021680544736352467 1973665532520817104528701)
    ·
      refine ⟨740124574695306414198263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1973665532520817104528701 740124574695306414198263)
      ·
        refine ⟨1110186862042959621297395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740124574695306414198263 1110186862042959621297395)
        ·
          refine ⟨1665280293064439431946093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110186862042959621297395 1665280293064439431946093)
          ·
            refine ⟨624480109899164786979785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1665280293064439431946093 624480109899164786979785)
            ·
              refine ⟨468360082424373590234839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624480109899164786979785 468360082424373590234839)
              ·
                refine ⟨702540123636560385352259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468360082424373590234839 702540123636560385352259)
                ·
                  refine ⟨1053810185454840578028389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702540123636560385352259 1053810185454840578028389)
                  ·
                    refine ⟨197589409772782608380323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1053810185454840578028389 197589409772782608380323)
                    ·
                      rfl

theorem cell22_577206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_577206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577206 prefixEnd_577206 := by exact prefixLift 577206
  have htrace : WordTrace (prefixWord ++ tailWord_577206) baseStart_577206 baseEnd_577206 := by
    simpa [prefixWord, tailWord_577206, baseEnd_577206] using wordTrace_append hprefix tailTrace_577206
  have hstable : (prefixWord ++ tailWord_577206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577206).length < 2 ^ (prefixWord ++ tailWord_577206).sum := by decide
  have hdescent : baseEnd_577206 < baseStart_577206 := by decide
  rcases family_descends (prefixWord ++ tailWord_577206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577258 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_577258 : Nat := 118140960795 + 577258 * 2 ^ 59
def prefixEnd_577258 : Nat := 4983230072969 + 3 ^ 40 * 577258 * 2
def baseEnd_577258 : Nat := 197607210435471806080163

theorem tailTrace_577258 : CollatzResearch.WordTrace tailWord_577258 prefixEnd_577258 197607210435471806080163 := by
  unfold tailWord_577258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5263582235675082165633107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14036219295133552441688285 5263582235675082165633107)
  ·
    refine ⟨7895373353512623248449661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5263582235675082165633107 7895373353512623248449661)
    ·
      refine ⟨2960765007567233718168623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7895373353512623248449661 2960765007567233718168623)
      ·
        refine ⟨4441147511350850577252935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960765007567233718168623 4441147511350850577252935)
        ·
          refine ⟨6661721267026275865879403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441147511350850577252935 6661721267026275865879403)
          ·
            refine ⟨9992581900539413798819105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6661721267026275865879403 9992581900539413798819105)
            ·
              refine ⟨7494436425404560349114329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9992581900539413798819105 7494436425404560349114329)
              ·
                refine ⟨5620827319053420261835747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7494436425404560349114329 5620827319053420261835747)
                ·
                  refine ⟨8431240978580130392753621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5620827319053420261835747 8431240978580130392753621)
                  ·
                    refine ⟨197607210435471806080163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8431240978580130392753621 197607210435471806080163)
                    ·
                      rfl

theorem cell22_577258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_577258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577258 prefixEnd_577258 := by exact prefixLift 577258
  have htrace : WordTrace (prefixWord ++ tailWord_577258) baseStart_577258 baseEnd_577258 := by
    simpa [prefixWord, tailWord_577258, baseEnd_577258] using wordTrace_append hprefix tailTrace_577258
  have hstable : (prefixWord ++ tailWord_577258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577258).length < 2 ^ (prefixWord ++ tailWord_577258).sum := by decide
  have hdescent : baseEnd_577258 < baseStart_577258 := by decide
  rcases family_descends (prefixWord ++ tailWord_577258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577273 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_577273 : Nat := 118140960795 + 577273 * 2 ^ 59
def prefixEnd_577273 : Nat := 4983230072969 + 3 ^ 40 * 577273 * 2
def baseEnd_577273 : Nat := 197612345242016766955117

theorem tailTrace_577273 : CollatzResearch.WordTrace tailWord_577273 prefixEnd_577273 197612345242016766955117 := by
  unfold tailWord_577273
  simp only [CollatzResearch.WordTrace]
  refine ⟨21054876037645986224328473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14036584025097324149552315 21054876037645986224328473)
  ·
    refine ⟨15791157028234489668246355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21054876037645986224328473 15791157028234489668246355)
    ·
      refine ⟨23686735542351734502369533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15791157028234489668246355 23686735542351734502369533)
      ·
        refine ⟨8882525828381900438388575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23686735542351734502369533 8882525828381900438388575)
        ·
          refine ⟨13323788742572850657582863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8882525828381900438388575 13323788742572850657582863)
          ·
            refine ⟨19985683113859275986374295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13323788742572850657582863 19985683113859275986374295)
            ·
              refine ⟨29978524670788913979561443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19985683113859275986374295 29978524670788913979561443)
              ·
                refine ⟨44967787006183370969342165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29978524670788913979561443 44967787006183370969342165)
                ·
                  refine ⟨1053932507957422757093957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 44967787006183370969342165 1053932507957422757093957)
                  ·
                    refine ⟨197612345242016766955117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1053932507957422757093957 197612345242016766955117)
                    ·
                      rfl

theorem cell22_577273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_577273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577273 prefixEnd_577273 := by exact prefixLift 577273
  have htrace : WordTrace (prefixWord ++ tailWord_577273) baseStart_577273 baseEnd_577273 := by
    simpa [prefixWord, tailWord_577273, baseEnd_577273] using wordTrace_append hprefix tailTrace_577273
  have hstable : (prefixWord ++ tailWord_577273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577273).length < 2 ^ (prefixWord ++ tailWord_577273).sum := by decide
  have hdescent : baseEnd_577273 < baseStart_577273 := by decide
  rcases family_descends (prefixWord ++ tailWord_577273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577320 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_577320 : Nat := 118140960795 + 577320 * 2 ^ 59
def prefixEnd_577320 : Nat := 4983230072969 + 3 ^ 40 * 577320 * 2
def baseEnd_577320 : Nat := 197628434302524311029973

theorem tailTrace_577320 : CollatzResearch.WordTrace tailWord_577320 prefixEnd_577320 197628434302524311029973 := by
  unfold tailWord_577320
  simp only [CollatzResearch.WordTrace]
  refine ⟨10528295134237856625644707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14037726845650475500859609 10528295134237856625644707)
  ·
    refine ⟨15792442701356784938467061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10528295134237856625644707 15792442701356784938467061)
    ·
      refine ⟨1480541503252198587981287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15792442701356784938467061 1480541503252198587981287)
      ·
        refine ⟨2220812254878297881971931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1480541503252198587981287 2220812254878297881971931)
        ·
          refine ⟨3331218382317446822957897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220812254878297881971931 3331218382317446822957897)
          ·
            refine ⟨2498413786738085117218423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3331218382317446822957897 2498413786738085117218423)
            ·
              refine ⟨3747620680107127675827635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2498413786738085117218423 3747620680107127675827635)
              ·
                refine ⟨5621431020160691513741453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3747620680107127675827635 5621431020160691513741453)
                ·
                  refine ⟨2108036632560259317653045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5621431020160691513741453 2108036632560259317653045)
                  ·
                    refine ⟨197628434302524311029973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2108036632560259317653045 197628434302524311029973)
                    ·
                      rfl

theorem cell22_577320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_577320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577320 prefixEnd_577320 := by exact prefixLift 577320
  have htrace : WordTrace (prefixWord ++ tailWord_577320) baseStart_577320 baseEnd_577320 := by
    simpa [prefixWord, tailWord_577320, baseEnd_577320] using wordTrace_append hprefix tailTrace_577320
  have hstable : (prefixWord ++ tailWord_577320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577320).length < 2 ^ (prefixWord ++ tailWord_577320).sum := by decide
  have hdescent : baseEnd_577320 < baseStart_577320 := by decide
  rcases family_descends (prefixWord ++ tailWord_577320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577333 : List Nat := [1, 3, 3, 1, 14]
def baseStart_577333 : Nat := 118140960795 + 577333 * 2 ^ 59
def prefixEnd_577333 : Nat := 4983230072969 + 3 ^ 40 * 577333 * 2
def baseEnd_577333 : Nat := 813304051309451071831

theorem tailTrace_577333 : CollatzResearch.WordTrace tailWord_577333 prefixEnd_577333 813304051309451071831 := by
  unfold tailWord_577333
  simp only [CollatzResearch.WordTrace]
  refine ⟨21057064417428616471512653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14038042944952410981008435 21057064417428616471512653)
  ·
    refine ⟨7896399156535731176817245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21057064417428616471512653 7896399156535731176817245)
    ·
      refine ⟨2961149683700899191306467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7896399156535731176817245 2961149683700899191306467)
      ·
        refine ⟨4441724525551348786959701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2961149683700899191306467 4441724525551348786959701)
        ·
          refine ⟨813304051309451071831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 4441724525551348786959701 813304051309451071831)
          ·
            rfl

theorem cell22_577333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 14].length) (baseStart_577333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577333 prefixEnd_577333 := by exact prefixLift 577333
  have htrace : WordTrace (prefixWord ++ tailWord_577333) baseStart_577333 baseEnd_577333 := by
    simpa [prefixWord, tailWord_577333, baseEnd_577333] using wordTrace_append hprefix tailTrace_577333
  have hstable : (prefixWord ++ tailWord_577333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577333).length < 2 ^ (prefixWord ++ tailWord_577333).sum := by decide
  have hdescent : baseEnd_577333 < baseStart_577333 := by decide
  rcases family_descends (prefixWord ++ tailWord_577333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577367 : List Nat := [1, 1, 3, 2, 5, 1, 3, 6]
def baseStart_577367 : Nat := 118140960795 + 577367 * 2 ^ 59
def prefixEnd_577367 : Nat := 4983230072969 + 3 ^ 40 * 577367 * 2
def baseEnd_577367 : Nat := 21960502595892428344981

theorem tailTrace_577367 : CollatzResearch.WordTrace tailWord_577367 prefixEnd_577367 21960502595892428344981 := by
  unfold tailWord_577367
  simp only [CollatzResearch.WordTrace]
  refine ⟨21058304499305440278250355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14038869666203626852166903 21058304499305440278250355)
  ·
    refine ⟨31587456748958160417375533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21058304499305440278250355 31587456748958160417375533)
    ·
      refine ⟨11845296280859310156515825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31587456748958160417375533 11845296280859310156515825)
      ·
        refine ⟨8883972210644482617386869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11845296280859310156515825 8883972210644482617386869)
        ·
          refine ⟨832872394747920245380019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8883972210644482617386869 832872394747920245380019)
          ·
            refine ⟨1249308592121880368070029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832872394747920245380019 1249308592121880368070029)
            ·
              refine ⟨468490722045705138026261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1249308592121880368070029 468490722045705138026261)
              ·
                refine ⟨21960502595892428344981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 468490722045705138026261 21960502595892428344981)
                ·
                  rfl

theorem cell22_577367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 6].length) (baseStart_577367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577367 prefixEnd_577367 := by exact prefixLift 577367
  have htrace : WordTrace (prefixWord ++ tailWord_577367) baseStart_577367 baseEnd_577367 := by
    simpa [prefixWord, tailWord_577367, baseEnd_577367] using wordTrace_append hprefix tailTrace_577367
  have hstable : (prefixWord ++ tailWord_577367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577367).length < 2 ^ (prefixWord ++ tailWord_577367).sum := by decide
  have hdescent : baseEnd_577367 < baseStart_577367 := by decide
  rcases family_descends (prefixWord ++ tailWord_577367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577425 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_577425 : Nat := 118140960795 + 577425 * 2 ^ 59
def prefixEnd_577425 : Nat := 4983230072969 + 3 ^ 40 * 577425 * 2
def baseEnd_577425 : Nat := 197664377948339037154651

theorem tailTrace_577425 : CollatzResearch.WordTrace tailWord_577425 prefixEnd_577425 197664377948339037154651 := by
  unfold tailWord_577425
  simp only [CollatzResearch.WordTrace]
  refine ⟨21060419933095316183861729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14040279955396877455907819 21060419933095316183861729)
  ·
    refine ⟨15795314949821487137896297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21060419933095316183861729 15795314949821487137896297)
    ·
      refine ⟨11846486212366115353422223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15795314949821487137896297 11846486212366115353422223)
      ·
        refine ⟨17769729318549173030133335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11846486212366115353422223 17769729318549173030133335)
        ·
          refine ⟨26654593977823759545200003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17769729318549173030133335 26654593977823759545200003)
          ·
            refine ⟨39981890966735639317800005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26654593977823759545200003 39981890966735639317800005)
            ·
              refine ⟨7496604556262932372087501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39981890966735639317800005 7496604556262932372087501)
              ·
                refine ⟨2811226708598599639532813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7496604556262932372087501 2811226708598599639532813)
                ·
                  refine ⟨1054210015724474864824805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2811226708598599639532813 1054210015724474864824805)
                  ·
                    refine ⟨197664377948339037154651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1054210015724474864824805 197664377948339037154651)
                    ·
                      rfl

theorem cell22_577425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_577425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577425 prefixEnd_577425 := by exact prefixLift 577425
  have htrace : WordTrace (prefixWord ++ tailWord_577425) baseStart_577425 baseEnd_577425 := by
    simpa [prefixWord, tailWord_577425, baseEnd_577425] using wordTrace_append hprefix tailTrace_577425
  have hstable : (prefixWord ++ tailWord_577425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577425).length < 2 ^ (prefixWord ++ tailWord_577425).sum := by decide
  have hdescent : baseEnd_577425 < baseStart_577425 := by decide
  rcases family_descends (prefixWord ++ tailWord_577425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577457 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 6]
def baseStart_577457 : Nat := 118140960795 + 577457 * 2 ^ 59
def prefixEnd_577457 : Nat := 4983230072969 + 3 ^ 40 * 577457 * 2
def baseEnd_577457 : Nat := 65891777400767206784851

theorem tailTrace_577457 : CollatzResearch.WordTrace tailWord_577457 prefixEnd_577457 65891777400767206784851 := by
  unfold tailWord_577457
  simp only [CollatzResearch.WordTrace]
  refine ⟨21061587068979385649026625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14041058045986257099351083 21061587068979385649026625)
  ·
    refine ⟨15796190301734539236769969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21061587068979385649026625 15796190301734539236769969)
    ·
      refine ⟨11847142726300904427577477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15796190301734539236769969 11847142726300904427577477)
      ·
        refine ⟨2221339261181419580170777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11847142726300904427577477 2221339261181419580170777)
        ·
          refine ⟨1666004445886064685128083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2221339261181419580170777 1666004445886064685128083)
          ·
            refine ⟨2499006668829097027692125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666004445886064685128083 2499006668829097027692125)
            ·
              refine ⟨937127500810911385384547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2499006668829097027692125 937127500810911385384547)
              ·
                refine ⟨1405691251216367078076821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937127500810911385384547 1405691251216367078076821)
                ·
                  refine ⟨65891777400767206784851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1405691251216367078076821 65891777400767206784851)
                  ·
                    rfl

theorem cell22_577457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_577457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577457 prefixEnd_577457 := by exact prefixLift 577457
  have htrace : WordTrace (prefixWord ++ tailWord_577457) baseStart_577457 baseEnd_577457 := by
    simpa [prefixWord, tailWord_577457, baseEnd_577457] using wordTrace_append hprefix tailTrace_577457
  have hstable : (prefixWord ++ tailWord_577457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577457).length < 2 ^ (prefixWord ++ tailWord_577457).sum := by decide
  have hdescent : baseEnd_577457 < baseStart_577457 := by decide
  rcases family_descends (prefixWord ++ tailWord_577457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577487 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 2, 4]
def baseStart_577487 : Nat := 118140960795 + 577487 * 2 ^ 59
def prefixEnd_577487 : Nat := 4983230072969 + 3 ^ 40 * 577487 * 2
def baseEnd_577487 : Nat := 197685601815391542104461

theorem tailTrace_577487 : CollatzResearch.WordTrace tailWord_577487 prefixEnd_577487 197685601815391542104461 := by
  unfold tailWord_577487
  simp only [CollatzResearch.WordTrace]
  refine ⟨21062681258870700772618715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14041787505913800515079143 21062681258870700772618715)
  ·
    refine ⟨31594021888306051158928073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21062681258870700772618715 31594021888306051158928073)
    ·
      refine ⟨23695516416229538369196055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31594021888306051158928073 23695516416229538369196055)
      ·
        refine ⟨35543274624344307553794083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23695516416229538369196055 35543274624344307553794083)
        ·
          refine ⟨53314911936516461330691125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35543274624344307553794083 53314911936516461330691125)
          ·
            refine ⟨4998272994048418249752293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53314911936516461330691125 4998272994048418249752293)
            ·
              refine ⟨937176186384078421828555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4998272994048418249752293 937176186384078421828555)
              ·
                refine ⟨1405764279576117632742833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937176186384078421828555 1405764279576117632742833)
                ·
                  refine ⟨1054323209682088224557125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1405764279576117632742833 1054323209682088224557125)
                  ·
                    refine ⟨197685601815391542104461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1054323209682088224557125 197685601815391542104461)
                    ·
                      rfl

theorem cell22_577487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_577487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577487 prefixEnd_577487 := by exact prefixLift 577487
  have htrace : WordTrace (prefixWord ++ tailWord_577487) baseStart_577487 baseEnd_577487 := by
    simpa [prefixWord, tailWord_577487, baseEnd_577487] using wordTrace_append hprefix tailTrace_577487
  have hstable : (prefixWord ++ tailWord_577487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577487).length < 2 ^ (prefixWord ++ tailWord_577487).sum := by decide
  have hdescent : baseEnd_577487 < baseStart_577487 := by decide
  rcases family_descends (prefixWord ++ tailWord_577487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577530 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_577530 : Nat := 118140960795 + 577530 * 2 ^ 59
def prefixEnd_577530 : Nat := 4983230072969 + 3 ^ 40 * 577530 * 2
def baseEnd_577530 : Nat := 65900107198051254426443

theorem tailTrace_577530 : CollatzResearch.WordTrace tailWord_577530 prefixEnd_577530 65900107198051254426443 := by
  unfold tailWord_577530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5266062399428729779108511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14042833065143279410956029 5266062399428729779108511)
  ·
    refine ⟨7899093599143094668662767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5266062399428729779108511 7899093599143094668662767)
    ·
      refine ⟨11848640398714642002994151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7899093599143094668662767 11848640398714642002994151)
      ·
        refine ⟨17772960598071963004491227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11848640398714642002994151 17772960598071963004491227)
        ·
          refine ⟨26659440897107944506736841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17772960598071963004491227 26659440897107944506736841)
          ·
            refine ⟨19994580672830958380052631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26659440897107944506736841 19994580672830958380052631)
            ·
              refine ⟨29991871009246437570078947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19994580672830958380052631 29991871009246437570078947)
              ·
                refine ⟨44987806513869656355118421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29991871009246437570078947 44987806513869656355118421)
                ·
                  refine ⟨65900107198051254426443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 44987806513869656355118421 65900107198051254426443)
                  ·
                    rfl

theorem cell22_577530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_577530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577530 prefixEnd_577530 := by exact prefixLift 577530
  have htrace : WordTrace (prefixWord ++ tailWord_577530) baseStart_577530 baseEnd_577530 := by
    simpa [prefixWord, tailWord_577530, baseEnd_577530] using wordTrace_append hprefix tailTrace_577530
  have hstable : (prefixWord ++ tailWord_577530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577530).length < 2 ^ (prefixWord ++ tailWord_577530).sum := by decide
  have hdescent : baseEnd_577530 < baseStart_577530 := by decide
  rcases family_descends (prefixWord ++ tailWord_577530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577542 : List Nat := [6, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_577542 : Nat := 118140960795 + 577542 * 2 ^ 59
def prefixEnd_577542 : Nat := 4983230072969 + 3 ^ 40 * 577542 * 2
def baseEnd_577542 : Nat := 65901476479796577326431

theorem tailTrace_577542 : CollatzResearch.WordTrace tailWord_577542 prefixEnd_577542 65901476479796577326431 := by
  unfold tailWord_577542
  simp only [CollatzResearch.WordTrace]
  refine ⟨658271477302232661433465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14043124849114296777247253 658271477302232661433465)
  ·
    refine ⟨493703607976674496075099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 658271477302232661433465 493703607976674496075099)
    ·
      refine ⟨740555411965011744112649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 493703607976674496075099 740555411965011744112649)
      ·
        refine ⟨555416558973758808084487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 740555411965011744112649 555416558973758808084487)
        ·
          refine ⟨833124838460638212126731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555416558973758808084487 833124838460638212126731)
          ·
            refine ⟨1249687257690957318190097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833124838460638212126731 1249687257690957318190097)
            ·
              refine ⟨937265443268217988642573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1249687257690957318190097 937265443268217988642573)
              ·
                refine ⟨351474541225581745740965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 937265443268217988642573 351474541225581745740965)
                ·
                  refine ⟨65901476479796577326431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351474541225581745740965 65901476479796577326431)
                  ·
                    rfl

theorem cell22_577542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_577542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577542 prefixEnd_577542 := by exact prefixLift 577542
  have htrace : WordTrace (prefixWord ++ tailWord_577542) baseStart_577542 baseEnd_577542 := by
    simpa [prefixWord, tailWord_577542, baseEnd_577542] using wordTrace_append hprefix tailTrace_577542
  have hstable : (prefixWord ++ tailWord_577542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577542).length < 2 ^ (prefixWord ++ tailWord_577542).sum := by decide
  have hdescent : baseEnd_577542 < baseStart_577542 := by decide
  rcases family_descends (prefixWord ++ tailWord_577542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577562 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_577562 : Nat := 118140960795 + 577562 * 2 ^ 59
def prefixEnd_577562 : Nat := 4983230072969 + 3 ^ 40 * 577562 * 2
def baseEnd_577562 : Nat := 197711275848116346479231

theorem tailTrace_577562 : CollatzResearch.WordTrace tailWord_577562 prefixEnd_577562 197711275848116346479231 := by
  unfold tailWord_577562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5266354183399747145399735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14043611155732659054399293 5266354183399747145399735)
  ·
    refine ⟨7899531275099620718099603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5266354183399747145399735 7899531275099620718099603)
    ·
      refine ⟨11849296912649431077149405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7899531275099620718099603 11849296912649431077149405)
      ·
        refine ⟨4443486342243536653931027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11849296912649431077149405 4443486342243536653931027)
        ·
          refine ⟨6665229513365304980896541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4443486342243536653931027 6665229513365304980896541)
          ·
            refine ⟨2499461067511989367836203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6665229513365304980896541 2499461067511989367836203)
            ·
              refine ⟨3749191601267984051754305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499461067511989367836203 3749191601267984051754305)
              ·
                refine ⟨2811893700950988038815729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3749191601267984051754305 2811893700950988038815729)
                ·
                  refine ⟨2108920275713241029111797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2811893700950988038815729 2108920275713241029111797)
                  ·
                    refine ⟨197711275848116346479231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2108920275713241029111797 197711275848116346479231)
                    ·
                      rfl

theorem cell22_577562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_577562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577562 prefixEnd_577562 := by exact prefixLift 577562
  have htrace : WordTrace (prefixWord ++ tailWord_577562) baseStart_577562 baseEnd_577562 := by
    simpa [prefixWord, tailWord_577562, baseEnd_577562] using wordTrace_append hprefix tailTrace_577562
  have hstable : (prefixWord ++ tailWord_577562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577562).length < 2 ^ (prefixWord ++ tailWord_577562).sum := by decide
  have hdescent : baseEnd_577562 < baseStart_577562 := by decide
  rcases family_descends (prefixWord ++ tailWord_577562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577564 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 5]
def baseStart_577564 : Nat := 118140960795 + 577564 * 2 ^ 59
def prefixEnd_577564 : Nat := 4983230072969 + 3 ^ 40 * 577564 * 2
def baseEnd_577564 : Nat := 65903986829663002643075

theorem tailTrace_577564 : CollatzResearch.WordTrace tailWord_577564 prefixEnd_577564 65903986829663002643075 := by
  unfold tailWord_577564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10532744839795871461585873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14043659786394495282114497 10532744839795871461585873)
  ·
    refine ⟨7899558629846903596189405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10532744839795871461585873 7899558629846903596189405)
    ·
      refine ⟨2962334486192588848571027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7899558629846903596189405 2962334486192588848571027)
      ·
        refine ⟨4443501729288883272856541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962334486192588848571027 4443501729288883272856541)
        ·
          refine ⟨1666313148483331227321203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4443501729288883272856541 1666313148483331227321203)
          ·
            refine ⟨2499469722724996840981805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666313148483331227321203 2499469722724996840981805)
            ·
              refine ⟨937301146021873815368177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2499469722724996840981805 937301146021873815368177)
              ·
                refine ⟨702975859516405361526133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937301146021873815368177 702975859516405361526133)
                ·
                  refine ⟨65903986829663002643075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 702975859516405361526133 65903986829663002643075)
                  ·
                    rfl

theorem cell22_577564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_577564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577564 prefixEnd_577564 := by exact prefixLift 577564
  have htrace : WordTrace (prefixWord ++ tailWord_577564) baseStart_577564 baseEnd_577564 := by
    simpa [prefixWord, tailWord_577564, baseEnd_577564] using wordTrace_append hprefix tailTrace_577564
  have hstable : (prefixWord ++ tailWord_577564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577564).length < 2 ^ (prefixWord ++ tailWord_577564).sum := by decide
  have hdescent : baseEnd_577564 < baseStart_577564 := by decide
  rcases family_descends (prefixWord ++ tailWord_577564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577607 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 3, 5]
def baseStart_577607 : Nat := 118140960795 + 577607 * 2 ^ 59
def prefixEnd_577607 : Nat := 4983230072969 + 3 ^ 40 * 577607 * 2
def baseEnd_577607 : Nat := 197726680267751229104093

theorem tailTrace_577607 : CollatzResearch.WordTrace tailWord_577607 prefixEnd_577607 197726680267751229104093 := by
  unfold tailWord_577607
  simp only [CollatzResearch.WordTrace]
  refine ⟨21067058018435961266987075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14044705345623974177991383 21067058018435961266987075)
  ·
    refine ⟨31600587027653941900480613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21067058018435961266987075 31600587027653941900480613)
    ·
      refine ⟨5925110067685114106340115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31600587027653941900480613 5925110067685114106340115)
      ·
        refine ⟨8887665101527671159510173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5925110067685114106340115 8887665101527671159510173)
        ·
          refine ⟨3332874413072876684816315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8887665101527671159510173 3332874413072876684816315)
          ·
            refine ⟨4999311619609315027224473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332874413072876684816315 4999311619609315027224473)
            ·
              refine ⟨3749483714706986270418355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4999311619609315027224473 3749483714706986270418355)
              ·
                refine ⟨5624225572060479405627533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749483714706986270418355 5624225572060479405627533)
                ·
                  refine ⟨2109084589522679777110325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5624225572060479405627533 2109084589522679777110325)
                  ·
                    refine ⟨197726680267751229104093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2109084589522679777110325 197726680267751229104093)
                    ·
                      rfl

theorem cell22_577607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_577607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577607 prefixEnd_577607 := by exact prefixLift 577607
  have htrace : WordTrace (prefixWord ++ tailWord_577607) baseStart_577607 baseEnd_577607 := by
    simpa [prefixWord, tailWord_577607, baseEnd_577607] using wordTrace_append hprefix tailTrace_577607
  have hstable : (prefixWord ++ tailWord_577607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577607).length < 2 ^ (prefixWord ++ tailWord_577607).sum := by decide
  have hdescent : baseEnd_577607 < baseStart_577607 := by decide
  rcases family_descends (prefixWord ++ tailWord_577607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577624 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 4, 3]
def baseStart_577624 : Nat := 118140960795 + 577624 * 2 ^ 59
def prefixEnd_577624 : Nat := 4983230072969 + 3 ^ 40 * 577624 * 2
def baseEnd_577624 : Nat := 197732499715168851429041

theorem tailTrace_577624 : CollatzResearch.WordTrace tailWord_577624 prefixEnd_577624 197732499715168851429041 := by
  unfold tailWord_577624
  simp only [CollatzResearch.WordTrace]
  refine ⟨10533839029687186585177963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14045118706249582113570617 10533839029687186585177963)
  ·
    refine ⟨15800758544530779877766945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10533839029687186585177963 15800758544530779877766945)
    ·
      refine ⟨11850568908398084908325209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15800758544530779877766945 11850568908398084908325209)
      ·
        refine ⟨8887926681298563681243907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11850568908398084908325209 8887926681298563681243907)
        ·
          refine ⟨13331890021947845521865861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8887926681298563681243907 13331890021947845521865861)
          ·
            refine ⟨2499729379115221035349849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13331890021947845521865861 2499729379115221035349849)
            ·
              refine ⟨1874797034336415776512387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2499729379115221035349849 1874797034336415776512387)
              ·
                refine ⟨2812195551504623664768581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874797034336415776512387 2812195551504623664768581)
                ·
                  refine ⟨527286665907116937144109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2812195551504623664768581 527286665907116937144109)
                  ·
                    refine ⟨197732499715168851429041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 527286665907116937144109 197732499715168851429041)
                    ·
                      rfl

theorem cell22_577624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_577624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577624 prefixEnd_577624 := by exact prefixLift 577624
  have htrace : WordTrace (prefixWord ++ tailWord_577624) baseStart_577624 baseEnd_577624 := by
    simpa [prefixWord, tailWord_577624, baseEnd_577624] using wordTrace_append hprefix tailTrace_577624
  have hstable : (prefixWord ++ tailWord_577624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577624).length < 2 ^ (prefixWord ++ tailWord_577624).sum := by decide
  have hdescent : baseEnd_577624 < baseStart_577624 := by decide
  rcases family_descends (prefixWord ++ tailWord_577624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577626 : List Nat := [3, 1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_577626 : Nat := 118140960795 + 577626 * 2 ^ 59
def prefixEnd_577626 : Nat := 4983230072969 + 3 ^ 40 * 577626 * 2
def baseEnd_577626 : Nat := 65911061452013837626345

theorem tailTrace_577626 : CollatzResearch.WordTrace tailWord_577626 prefixEnd_577626 65911061452013837626345 := by
  unfold tailWord_577626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5266937751341781877982183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14045167336911418341285821 5266937751341781877982183)
  ·
    refine ⟨7900406627012672816973275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5266937751341781877982183 7900406627012672816973275)
    ·
      refine ⟨11850609940519009225459913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7900406627012672816973275 11850609940519009225459913)
      ·
        refine ⟨8887957455389256919094935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11850609940519009225459913 8887957455389256919094935)
        ·
          refine ⟨13331936183083885378642403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8887957455389256919094935 13331936183083885378642403)
          ·
            refine ⟨19997904274625828067963605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13331936183083885378642403 19997904274625828067963605)
            ·
              refine ⟨468700881436542845342897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19997904274625828067963605 468700881436542845342897)
              ·
                refine ⟨351525661077407134007173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468700881436542845342897 351525661077407134007173)
                ·
                  refine ⟨65911061452013837626345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351525661077407134007173 65911061452013837626345)
                  ·
                    rfl

theorem cell22_577626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_577626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577626 prefixEnd_577626 := by exact prefixLift 577626
  have htrace : WordTrace (prefixWord ++ tailWord_577626) baseStart_577626 baseEnd_577626 := by
    simpa [prefixWord, tailWord_577626, baseEnd_577626] using wordTrace_append hprefix tailTrace_577626
  have hstable : (prefixWord ++ tailWord_577626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577626).length < 2 ^ (prefixWord ++ tailWord_577626).sum := by decide
  have hdescent : baseEnd_577626 < baseStart_577626 := by decide
  rcases family_descends (prefixWord ++ tailWord_577626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577637 : List Nat := [1, 3, 1, 3, 2, 2, 1, 9]
def baseStart_577637 : Nat := 118140960795 + 577637 * 2 ^ 59
def prefixEnd_577637 : Nat := 4983230072969 + 3 ^ 40 * 577637 * 2
def baseEnd_577637 : Nat := 21970772208982350094889

theorem tailTrace_577637 : CollatzResearch.WordTrace tailWord_577637 prefixEnd_577637 21970772208982350094889 := by
  unfold tailWord_577637
  simp only [CollatzResearch.WordTrace]
  refine ⟨21068152208327276390579165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14045434805551517593719443 21068152208327276390579165)
  ·
    refine ⟨7900557078122728646467187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21068152208327276390579165 7900557078122728646467187)
    ·
      refine ⟨11850835617184092969700781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7900557078122728646467187 11850835617184092969700781)
      ·
        refine ⟨4444063356444034863637793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11850835617184092969700781 4444063356444034863637793)
        ·
          refine ⟨3333047517333026147728345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4444063356444034863637793 3333047517333026147728345)
          ·
            refine ⟨2499785637999769610796259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3333047517333026147728345 2499785637999769610796259)
            ·
              refine ⟨3749678456999654416194389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499785637999769610796259 3749678456999654416194389)
              ·
                refine ⟨21970772208982350094889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3749678456999654416194389 21970772208982350094889)
                ·
                  rfl

theorem cell22_577637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 9].length) (baseStart_577637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577637 prefixEnd_577637 := by exact prefixLift 577637
  have htrace : WordTrace (prefixWord ++ tailWord_577637) baseStart_577637 baseEnd_577637 := by
    simpa [prefixWord, tailWord_577637, baseEnd_577637] using wordTrace_append hprefix tailTrace_577637
  have hstable : (prefixWord ++ tailWord_577637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577637).length < 2 ^ (prefixWord ++ tailWord_577637).sum := by decide
  have hdescent : baseEnd_577637 < baseStart_577637 := by decide
  rcases family_descends (prefixWord ++ tailWord_577637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577654 : List Nat := [5, 1, 1, 2, 1, 2, 2, 8]
def baseStart_577654 : Nat := 118140960795 + 577654 * 2 ^ 59
def prefixEnd_577654 : Nat := 4983230072969 + 3 ^ 40 * 577654 * 2
def baseEnd_577654 : Nat := 21971418814250974797661

theorem tailTrace_577654 : CollatzResearch.WordTrace tailWord_577654 prefixEnd_577654 21971418814250974797661 := by
  unfold tailWord_577654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316798265579105518371751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14045848166177125529298677 1316798265579105518371751)
  ·
    refine ⟨1975197398368658277557627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316798265579105518371751 1975197398368658277557627)
    ·
      refine ⟨2962796097552987416336441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1975197398368658277557627 2962796097552987416336441)
      ·
        refine ⟨2222097073164740562252331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2962796097552987416336441 2222097073164740562252331)
        ·
          refine ⟨3333145609747110843378497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222097073164740562252331 3333145609747110843378497)
          ·
            refine ⟨2499859207310333132533873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3333145609747110843378497 2499859207310333132533873)
            ·
              refine ⟨1874894405482749849400405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2499859207310333132533873 1874894405482749849400405)
              ·
                refine ⟨21971418814250974797661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1874894405482749849400405 21971418814250974797661)
                ·
                  rfl

theorem cell22_577654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_577654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577654 prefixEnd_577654 := by exact prefixLift 577654
  have htrace : WordTrace (prefixWord ++ tailWord_577654) baseStart_577654 baseEnd_577654 := by
    simpa [prefixWord, tailWord_577654, baseEnd_577654] using wordTrace_append hprefix tailTrace_577654
  have hstable : (prefixWord ++ tailWord_577654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577654).length < 2 ^ (prefixWord ++ tailWord_577654).sum := by decide
  have hdescent : baseEnd_577654 < baseStart_577654 := by decide
  rcases family_descends (prefixWord ++ tailWord_577654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577703 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 3, 3]
def baseStart_577703 : Nat := 118140960795 + 577703 * 2 ^ 59
def prefixEnd_577703 : Nat := 4983230072969 + 3 ^ 40 * 577703 * 2
def baseEnd_577703 : Nat := 197759543029638978703799

theorem tailTrace_577703 : CollatzResearch.WordTrace tailWord_577703 prefixEnd_577703 197759543029638978703799 := by
  unfold tailWord_577703
  simp only [CollatzResearch.WordTrace]
  refine ⟨21070559426088169662481763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14047039617392113108321175 21070559426088169662481763)
  ·
    refine ⟨31605839139132254493722645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21070559426088169662481763 31605839139132254493722645)
    ·
      refine ⟨1481523709646824429393249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31605839139132254493722645 1481523709646824429393249)
      ·
        refine ⟨1111142782235118322044937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1481523709646824429393249 1111142782235118322044937)
        ·
          refine ⟨833357086676338741533703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1111142782235118322044937 833357086676338741533703)
          ·
            refine ⟨1250035630014508112300555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833357086676338741533703 1250035630014508112300555)
            ·
              refine ⟨1875053445021762168450833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250035630014508112300555 1875053445021762168450833)
              ·
                refine ⟨1406290083766321626338125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1875053445021762168450833 1406290083766321626338125)
                ·
                  refine ⟨527358781412370609876797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1406290083766321626338125 527358781412370609876797)
                  ·
                    refine ⟨197759543029638978703799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 527358781412370609876797 197759543029638978703799)
                    ·
                      rfl

theorem cell22_577703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_577703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577703 prefixEnd_577703 := by exact prefixLift 577703
  have htrace : WordTrace (prefixWord ++ tailWord_577703) baseStart_577703 baseEnd_577703 := by
    simpa [prefixWord, tailWord_577703, baseEnd_577703] using wordTrace_append hprefix tailTrace_577703
  have hstable : (prefixWord ++ tailWord_577703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577703).length < 2 ^ (prefixWord ++ tailWord_577703).sum := by decide
  have hdescent : baseEnd_577703 < baseStart_577703 := by decide
  rcases family_descends (prefixWord ++ tailWord_577703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577727 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 10]
def baseStart_577727 : Nat := 118140960795 + 577727 * 2 ^ 59
def prefixEnd_577727 : Nat := 4983230072969 + 3 ^ 40 * 577727 * 2
def baseEnd_577727 : Nat := 65922586240036972034575

theorem tailTrace_577727 : CollatzResearch.WordTrace tailWord_577727 prefixEnd_577727 65922586240036972034575 := by
  unfold tailWord_577727
  simp only [CollatzResearch.WordTrace]
  refine ⟨21071434778001221761355435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14047623185334147840903623 21071434778001221761355435)
  ·
    refine ⟨31607152167001832642033153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21071434778001221761355435 31607152167001832642033153)
    ·
      refine ⟨23705364125251374481524865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31607152167001832642033153 23705364125251374481524865)
      ·
        refine ⟨17779023093938530861143649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23705364125251374481524865 17779023093938530861143649)
        ·
          refine ⟨13334267320453898145857737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17779023093938530861143649 13334267320453898145857737)
          ·
            refine ⟨10000700490340423609393303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13334267320453898145857737 10000700490340423609393303)
            ·
              refine ⟨15001050735510635414089955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10000700490340423609393303 15001050735510635414089955)
              ·
                refine ⟨22501576103265953121134933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15001050735510635414089955 22501576103265953121134933)
                ·
                  refine ⟨65922586240036972034575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 22501576103265953121134933 65922586240036972034575)
                  ·
                    rfl

theorem cell22_577727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 10].length) (baseStart_577727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577727 prefixEnd_577727 := by exact prefixLift 577727
  have htrace : WordTrace (prefixWord ++ tailWord_577727) baseStart_577727 baseEnd_577727 := by
    simpa [prefixWord, tailWord_577727, baseEnd_577727] using wordTrace_append hprefix tailTrace_577727
  have hstable : (prefixWord ++ tailWord_577727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577727).length < 2 ^ (prefixWord ++ tailWord_577727).sum := by decide
  have hdescent : baseEnd_577727 < baseStart_577727 := by decide
  rcases family_descends (prefixWord ++ tailWord_577727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577750 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_577750 : Nat := 118140960795 + 577750 * 2 ^ 59
def prefixEnd_577750 : Nat := 4983230072969 + 3 ^ 40 * 577750 * 2
def baseEnd_577750 : Nat := 65925210696715507592885

theorem tailTrace_577750 : CollatzResearch.WordTrace tailWord_577750 prefixEnd_577750 65925210696715507592885 := by
  unfold tailWord_577750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317017103557368543090169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14048182437945264459628469 1317017103557368543090169)
  ·
    refine ⟨987762827668026407317627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1317017103557368543090169 987762827668026407317627)
    ·
      refine ⟨1481644241502039610976441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 987762827668026407317627 1481644241502039610976441)
      ·
        refine ⟨1111233181126529708232331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1481644241502039610976441 1111233181126529708232331)
        ·
          refine ⟨1666849771689794562348497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111233181126529708232331 1666849771689794562348497)
          ·
            refine ⟨1250137328767345921761373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1666849771689794562348497 1250137328767345921761373)
            ·
              refine ⟨468801498287754720660515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1250137328767345921761373 468801498287754720660515)
              ·
                refine ⟨703202247431632080990773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468801498287754720660515 703202247431632080990773)
                ·
                  refine ⟨65925210696715507592885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 703202247431632080990773 65925210696715507592885)
                  ·
                    rfl

theorem cell22_577750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_577750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577750 prefixEnd_577750 := by exact prefixLift 577750
  have htrace : WordTrace (prefixWord ++ tailWord_577750) baseStart_577750 baseEnd_577750 := by
    simpa [prefixWord, tailWord_577750, baseEnd_577750] using wordTrace_append hprefix tailTrace_577750
  have hstable : (prefixWord ++ tailWord_577750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577750).length < 2 ^ (prefixWord ++ tailWord_577750).sum := by decide
  have hdescent : baseEnd_577750 < baseStart_577750 := by decide
  rcases family_descends (prefixWord ++ tailWord_577750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577778 : List Nat := [3, 2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_577778 : Nat := 118140960795 + 577778 * 2 ^ 59
def prefixEnd_577778 : Nat := 4983230072969 + 3 ^ 40 * 577778 * 2
def baseEnd_577778 : Nat := 65928405687454594359523

theorem tailTrace_577778 : CollatzResearch.WordTrace tailWord_577778 prefixEnd_577778 65928405687454594359523 := by
  unfold tailWord_577778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5268323725204114367865497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14048863267210971647641325 5268323725204114367865497)
  ·
    refine ⟨3951242793903085775899123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5268323725204114367865497 3951242793903085775899123)
    ·
      refine ⟨5926864190854628663848685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3951242793903085775899123 5926864190854628663848685)
      ·
        refine ⟨2222574071570485748943257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5926864190854628663848685 2222574071570485748943257)
        ·
          refine ⟨1666930553677864311707443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2222574071570485748943257 1666930553677864311707443)
          ·
            refine ⟨2500395830516796467561165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666930553677864311707443 2500395830516796467561165)
            ·
              refine ⟨937648436443798675335437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2500395830516796467561165 937648436443798675335437)
              ·
                refine ⟨351618163666424503250789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 937648436443798675335437 351618163666424503250789)
                ·
                  refine ⟨65928405687454594359523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351618163666424503250789 65928405687454594359523)
                  ·
                    rfl

theorem cell22_577778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_577778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577778 prefixEnd_577778 := by exact prefixLift 577778
  have htrace : WordTrace (prefixWord ++ tailWord_577778) baseStart_577778 baseEnd_577778 := by
    simpa [prefixWord, tailWord_577778, baseEnd_577778] using wordTrace_append hprefix tailTrace_577778
  have hstable : (prefixWord ++ tailWord_577778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577778).length < 2 ^ (prefixWord ++ tailWord_577778).sum := by decide
  have hdescent : baseEnd_577778 < baseStart_577778 := by decide
  rcases family_descends (prefixWord ++ tailWord_577778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577881 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 1, 4]
def baseStart_577881 : Nat := 118140960795 + 577881 * 2 ^ 59
def prefixEnd_577881 : Nat := 4983230072969 + 3 ^ 40 * 577881 * 2
def baseEnd_577881 : Nat := 197820476067305847753253

theorem tailTrace_577881 : CollatzResearch.WordTrace tailWord_577881 prefixEnd_577881 197820476067305847753253 := by
  unfold tailWord_577881
  simp only [CollatzResearch.WordTrace]
  refine ⟨21077051619443306062461497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14051367746295537374974331 21077051619443306062461497)
  ·
    refine ⟨15807788714582479546846123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21077051619443306062461497 15807788714582479546846123)
    ·
      refine ⟨23711683071873719320269185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15807788714582479546846123 23711683071873719320269185)
      ·
        refine ⟨17783762303905289490201889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23711683071873719320269185 17783762303905289490201889)
        ·
          refine ⟨13337821727928967117651417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17783762303905289490201889 13337821727928967117651417)
          ·
            refine ⟨10003366295946725338238563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13337821727928967117651417 10003366295946725338238563)
            ·
              refine ⟨15005049443920088007357845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10003366295946725338238563 15005049443920088007357845)
              ·
                refine ⟨703361692683754125344899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15005049443920088007357845 703361692683754125344899)
                ·
                  refine ⟨1055042539025631188017349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703361692683754125344899 1055042539025631188017349)
                  ·
                    refine ⟨197820476067305847753253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1055042539025631188017349 197820476067305847753253)
                    ·
                      rfl

theorem cell22_577881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_577881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577881 prefixEnd_577881 := by exact prefixLift 577881
  have htrace : WordTrace (prefixWord ++ tailWord_577881) baseStart_577881 baseEnd_577881 := by
    simpa [prefixWord, tailWord_577881, baseEnd_577881] using wordTrace_append hprefix tailTrace_577881
  have hstable : (prefixWord ++ tailWord_577881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577881).length < 2 ^ (prefixWord ++ tailWord_577881).sum := by decide
  have hdescent : baseEnd_577881 < baseStart_577881 := by decide
  rcases family_descends (prefixWord ++ tailWord_577881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577960 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 2, 4]
def baseStart_577960 : Nat := 118140960795 + 577960 * 2 ^ 59
def prefixEnd_577960 : Nat := 4983230072969 + 3 ^ 40 * 577960 * 2
def baseEnd_577960 : Nat := 197847519381775975028011

theorem tailTrace_577960 : CollatzResearch.WordTrace tailWord_577960 prefixEnd_577960 197847519381775975028011 := by
  unfold tailWord_577960
  simp only [CollatzResearch.WordTrace]
  refine ⟨10539966493078551277293667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14053288657438068369724889 10539966493078551277293667)
  ·
    refine ⟨15809949739617826915940501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10539966493078551277293667 15809949739617826915940501)
    ·
      refine ⟨741091394044585636684711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15809949739617826915940501 741091394044585636684711)
      ·
        refine ⟨1111637091066878455027067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741091394044585636684711 1111637091066878455027067)
        ·
          refine ⟨1667455636600317682540601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111637091066878455027067 1667455636600317682540601)
          ·
            refine ⟨1250591727450238261905451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1667455636600317682540601 1250591727450238261905451)
            ·
              refine ⟨1875887591175357392858177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250591727450238261905451 1875887591175357392858177)
              ·
                refine ⟨1406915693381518044643633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1875887591175357392858177 1406915693381518044643633)
                ·
                  refine ⟨1055186770036138533482725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1406915693381518044643633 1055186770036138533482725)
                  ·
                    refine ⟨197847519381775975028011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1055186770036138533482725 197847519381775975028011)
                    ·
                      rfl

theorem cell22_577960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_577960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_577960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_577960 prefixEnd_577960 := by exact prefixLift 577960
  have htrace : WordTrace (prefixWord ++ tailWord_577960) baseStart_577960 baseEnd_577960 := by
    simpa [prefixWord, tailWord_577960, baseEnd_577960] using wordTrace_append hprefix tailTrace_577960
  have hstable : (prefixWord ++ tailWord_577960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577960).length < 2 ^ (prefixWord ++ tailWord_577960).sum := by decide
  have hdescent : baseEnd_577960 < baseStart_577960 := by decide
  rcases family_descends (prefixWord ++ tailWord_577960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578024 : List Nat := [2, 1, 4, 1, 1, 5, 2, 2, 1, 3]
def baseStart_578024 : Nat := 118140960795 + 578024 * 2 ^ 59
def prefixEnd_578024 : Nat := 4983230072969 + 3 ^ 40 * 578024 * 2
def baseEnd_578024 : Nat := 197869427889701141427815

theorem tailTrace_578024 : CollatzResearch.WordTrace tailWord_578024 prefixEnd_578024 197869427889701141427815 := by
  unfold tailWord_578024
  simp only [CollatzResearch.WordTrace]
  refine ⟨10541133628962620742458563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14054844838616827656611417 10541133628962620742458563)
  ·
    refine ⟨15811700443443931113687845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10541133628962620742458563 15811700443443931113687845)
    ·
      refine ⟨2964693833145737083816471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15811700443443931113687845 2964693833145737083816471)
      ·
        refine ⟨4447040749718605625724707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964693833145737083816471 4447040749718605625724707)
        ·
          refine ⟨6670561124577908438587061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4447040749718605625724707 6670561124577908438587061)
          ·
            refine ⟨625365105429178916117537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6670561124577908438587061 625365105429178916117537)
            ·
              refine ⟨469023829071884187088153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625365105429178916117537 469023829071884187088153)
              ·
                refine ⟨351767871803913140316115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469023829071884187088153 351767871803913140316115)
                ·
                  refine ⟨527651807705869710474173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351767871803913140316115 527651807705869710474173)
                  ·
                    refine ⟨197869427889701141427815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 527651807705869710474173 197869427889701141427815)
                    ·
                      rfl

theorem cell22_578024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_578024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578024 prefixEnd_578024 := by exact prefixLift 578024
  have htrace : WordTrace (prefixWord ++ tailWord_578024) baseStart_578024 baseEnd_578024 := by
    simpa [prefixWord, tailWord_578024, baseEnd_578024] using wordTrace_append hprefix tailTrace_578024
  have hstable : (prefixWord ++ tailWord_578024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578024).length < 2 ^ (prefixWord ++ tailWord_578024).sum := by decide
  have hdescent : baseEnd_578024 < baseStart_578024 := by decide
  rcases family_descends (prefixWord ++ tailWord_578024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578031 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 6]
def baseStart_578031 : Nat := 118140960795 + 578031 * 2 ^ 59
def prefixEnd_578031 : Nat := 4983230072969 + 3 ^ 40 * 578031 * 2
def baseEnd_578031 : Nat := 65957274710918485500931

theorem tailTrace_578031 : CollatzResearch.WordTrace tailWord_578031 prefixEnd_578031 65957274710918485500931 := by
  unfold tailWord_578031
  simp only [CollatzResearch.WordTrace]
  refine ⟨21082522568899881680421947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14055015045933254453614631 21082522568899881680421947)
  ·
    refine ⟨31623783853349822520632921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21082522568899881680421947 31623783853349822520632921)
    ·
      refine ⟨23717837890012366890474691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31623783853349822520632921 23717837890012366890474691)
      ·
        refine ⟨35576756835018550335712037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23717837890012366890474691 35576756835018550335712037)
        ·
          refine ⟨6670641906565978187946007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35576756835018550335712037 6670641906565978187946007)
          ·
            refine ⟨10005962859848967281919011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6670641906565978187946007 10005962859848967281919011)
            ·
              refine ⟨15008944289773450922878517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10005962859848967281919011 15008944289773450922878517)
              ·
                refine ⟨1407088527166261024019861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15008944289773450922878517 1407088527166261024019861)
                ·
                  refine ⟨65957274710918485500931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1407088527166261024019861 65957274710918485500931)
                  ·
                    rfl

theorem cell22_578031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 6].length) (baseStart_578031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578031 prefixEnd_578031 := by exact prefixLift 578031
  have htrace : WordTrace (prefixWord ++ tailWord_578031) baseStart_578031 baseEnd_578031 := by
    simpa [prefixWord, tailWord_578031, baseEnd_578031] using wordTrace_append hprefix tailTrace_578031
  have hstable : (prefixWord ++ tailWord_578031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578031).length < 2 ^ (prefixWord ++ tailWord_578031).sum := by decide
  have hdescent : baseEnd_578031 < baseStart_578031 := by decide
  rcases family_descends (prefixWord ++ tailWord_578031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578168 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_578168 : Nat := 118140960795 + 578168 * 2 ^ 59
def prefixEnd_578168 : Nat := 4983230072969 + 3 ^ 40 * 578168 * 2
def baseEnd_578168 : Nat := 197918722032532765827373

theorem tailTrace_578168 : CollatzResearch.WordTrace tailWord_578168 prefixEnd_578168 197918722032532765827373 := by
  unfold tailWord_578168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10543759684701777039079579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14058346246269036052106105 10543759684701777039079579)
  ·
    refine ⟨15815639527052665558619369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10543759684701777039079579 15815639527052665558619369)
    ·
      refine ⟨11861729645289499168964527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15815639527052665558619369 11861729645289499168964527)
      ·
        refine ⟨17792594467934248753446791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11861729645289499168964527 17792594467934248753446791)
        ·
          refine ⟨26688891701901373130170187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17792594467934248753446791 26688891701901373130170187)
          ·
            refine ⟨40033337552852059695255281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26688891701901373130170187 40033337552852059695255281)
            ·
              refine ⟨30025003164639044771441461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40033337552852059695255281 30025003164639044771441461)
              ·
                refine ⟨2814844046684910447322637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30025003164639044771441461 2814844046684910447322637)
                ·
                  refine ⟨1055566517506841417745989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2814844046684910447322637 1055566517506841417745989)
                  ·
                    refine ⟨197918722032532765827373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1055566517506841417745989 197918722032532765827373)
                    ·
                      rfl

theorem cell22_578168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_578168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578168 prefixEnd_578168 := by exact prefixLift 578168
  have htrace : WordTrace (prefixWord ++ tailWord_578168) baseStart_578168 baseEnd_578168 := by
    simpa [prefixWord, tailWord_578168, baseEnd_578168] using wordTrace_append hprefix tailTrace_578168
  have hstable : (prefixWord ++ tailWord_578168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578168).length < 2 ^ (prefixWord ++ tailWord_578168).sum := by decide
  have hdescent : baseEnd_578168 < baseStart_578168 := by decide
  rcases family_descends (prefixWord ++ tailWord_578168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578213 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_578213 : Nat := 118140960795 + 578213 * 2 ^ 59
def prefixEnd_578213 : Nat := 4983230072969 + 3 ^ 40 * 578213 * 2
def baseEnd_578213 : Nat := 197934126452167648452235

theorem tailTrace_578213 : CollatzResearch.WordTrace tailWord_578213 prefixEnd_578213 197934126452167648452235 := by
  unfold tailWord_578213
  simp only [CollatzResearch.WordTrace]
  refine ⟨21089160654240526763547293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14059440436160351175698195 21089160654240526763547293)
  ·
    refine ⟨7908435245340197536330235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21089160654240526763547293 7908435245340197536330235)
    ·
      refine ⟨11862652868010296304495353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7908435245340197536330235 11862652868010296304495353)
      ·
        refine ⟨8896989651007722228371515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11862652868010296304495353 8896989651007722228371515)
        ·
          refine ⟨13345484476511583342557273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8896989651007722228371515 13345484476511583342557273)
          ·
            refine ⟨10009113357383687506917955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13345484476511583342557273 10009113357383687506917955)
            ·
              refine ⟨15013670036075531260376933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10009113357383687506917955 15013670036075531260376933)
              ·
                refine ⟨2815063131764162111320675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15013670036075531260376933 2815063131764162111320675)
                ·
                  refine ⟨4222594697646243166981013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815063131764162111320675 4222594697646243166981013)
                  ·
                    refine ⟨197934126452167648452235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4222594697646243166981013 197934126452167648452235)
                    ·
                      rfl

theorem cell22_578213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_578213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578213 prefixEnd_578213 := by exact prefixLift 578213
  have htrace : WordTrace (prefixWord ++ tailWord_578213) baseStart_578213 baseEnd_578213 := by
    simpa [prefixWord, tailWord_578213, baseEnd_578213] using wordTrace_append hprefix tailTrace_578213
  have hstable : (prefixWord ++ tailWord_578213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578213).length < 2 ^ (prefixWord ++ tailWord_578213).sum := by decide
  have hdescent : baseEnd_578213 < baseStart_578213 := by decide
  rcases family_descends (prefixWord ++ tailWord_578213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578277 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 3, 3]
def baseStart_578277 : Nat := 118140960795 + 578277 * 2 ^ 59
def prefixEnd_578277 : Nat := 4983230072969 + 3 ^ 40 * 578277 * 2
def baseEnd_578277 : Nat := 197956034960092814852039

theorem tailTrace_578277 : CollatzResearch.WordTrace tailWord_578277 prefixEnd_578277 197956034960092814852039 := by
  unfold tailWord_578277
  simp only [CollatzResearch.WordTrace]
  refine ⟨21091494926008665693877085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14060996617339110462584723 21091494926008665693877085)
  ·
    refine ⟨7909310597253249635203907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21091494926008665693877085 7909310597253249635203907)
    ·
      refine ⟨11863965895879874452805861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7909310597253249635203907 11863965895879874452805861)
      ·
        refine ⟨2224493605477476459901099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11863965895879874452805861 2224493605477476459901099)
        ·
          refine ⟨3336740408216214689851649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224493605477476459901099 3336740408216214689851649)
          ·
            refine ⟨2502555306162161017388737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3336740408216214689851649 2502555306162161017388737)
            ·
              refine ⟨1876916479621620763041553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2502555306162161017388737 1876916479621620763041553)
              ·
                refine ⟨1407687359716215572281165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1876916479621620763041553 1407687359716215572281165)
                ·
                  refine ⟨527882759893580839605437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1407687359716215572281165 527882759893580839605437)
                  ·
                    refine ⟨197956034960092814852039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 527882759893580839605437 197956034960092814852039)
                    ·
                      rfl

theorem cell22_578277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_578277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578277 prefixEnd_578277 := by exact prefixLift 578277
  have htrace : WordTrace (prefixWord ++ tailWord_578277) baseStart_578277 baseEnd_578277 := by
    simpa [prefixWord, tailWord_578277, baseEnd_578277] using wordTrace_append hprefix tailTrace_578277
  have hstable : (prefixWord ++ tailWord_578277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578277).length < 2 ^ (prefixWord ++ tailWord_578277).sum := by decide
  have hdescent : baseEnd_578277 < baseStart_578277 := by decide
  rcases family_descends (prefixWord ++ tailWord_578277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578290 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_578290 : Nat := 118140960795 + 578290 * 2 ^ 59
def prefixEnd_578290 : Nat := 4983230072969 + 3 ^ 40 * 578290 * 2
def baseEnd_578290 : Nat := 65986828375255038092333

theorem tailTrace_578290 : CollatzResearch.WordTrace tailWord_578290 prefixEnd_578290 65986828375255038092333 := by
  unfold tailWord_578290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272992268740392228525081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14061312716641045942733549 5272992268740392228525081)
  ·
    refine ⟨3954744201555294171393811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5272992268740392228525081 3954744201555294171393811)
    ·
      refine ⟨5932116302332941257090717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3954744201555294171393811 5932116302332941257090717)
      ·
        refine ⟨2224543613374852971409019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5932116302332941257090717 2224543613374852971409019)
        ·
          refine ⟨3336815420062279457113529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224543613374852971409019 3336815420062279457113529)
          ·
            refine ⟨2502611565046709592835147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3336815420062279457113529 2502611565046709592835147)
            ·
              refine ⟨3753917347570064389252721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502611565046709592835147 3753917347570064389252721)
              ·
                refine ⟨2815438010677548291939541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3753917347570064389252721 2815438010677548291939541)
                ·
                  refine ⟨65986828375255038092333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2815438010677548291939541 65986828375255038092333)
                  ·
                    rfl

theorem cell22_578290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_578290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578290 prefixEnd_578290 := by exact prefixLift 578290
  have htrace : WordTrace (prefixWord ++ tailWord_578290) baseStart_578290 baseEnd_578290 := by
    simpa [prefixWord, tailWord_578290, baseEnd_578290] using wordTrace_append hprefix tailTrace_578290
  have hstable : (prefixWord ++ tailWord_578290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578290).length < 2 ^ (prefixWord ++ tailWord_578290).sum := by decide
  have hdescent : baseEnd_578290 < baseStart_578290 := by decide
  rcases family_descends (prefixWord ++ tailWord_578290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578354 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_578354 : Nat := 118140960795 + 578354 * 2 ^ 59
def prefixEnd_578354 : Nat := 4983230072969 + 3 ^ 40 * 578354 * 2
def baseEnd_578354 : Nat := 197982393633690280676803

theorem tailTrace_578354 : CollatzResearch.WordTrace tailWord_578354 prefixEnd_578354 197982393633690280676803 := by
  unfold tailWord_578354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5273575836682426961107529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14062868897819805229620077 5273575836682426961107529)
  ·
    refine ⟨3955181877511820220830647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5273575836682426961107529 3955181877511820220830647)
    ·
      refine ⟨5932772816267730331245971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3955181877511820220830647 5932772816267730331245971)
      ·
        refine ⟨8899159224401595496868957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5932772816267730331245971 8899159224401595496868957)
        ·
          refine ⟨3337184709150598311325859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8899159224401595496868957 3337184709150598311325859)
          ·
            refine ⟨5005777063725897466988789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3337184709150598311325859 5005777063725897466988789)
            ·
              refine ⟨469291599724302887530199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5005777063725897466988789 469291599724302887530199)
              ·
                refine ⟨703937399586454331295299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469291599724302887530199 703937399586454331295299)
                ·
                  refine ⟨1055906099379681496942949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703937399586454331295299 1055906099379681496942949)
                  ·
                    refine ⟨197982393633690280676803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1055906099379681496942949 197982393633690280676803)
                    ·
                      rfl

theorem cell22_578354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_578354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578354 prefixEnd_578354 := by exact prefixLift 578354
  have htrace : WordTrace (prefixWord ++ tailWord_578354) baseStart_578354 baseEnd_578354 := by
    simpa [prefixWord, tailWord_578354, baseEnd_578354] using wordTrace_append hprefix tailTrace_578354
  have hstable : (prefixWord ++ tailWord_578354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578354).length < 2 ^ (prefixWord ++ tailWord_578354).sum := by decide
  have hdescent : baseEnd_578354 < baseStart_578354 := by decide
  rcases family_descends (prefixWord ++ tailWord_578354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578412 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 5, 3]
def baseStart_578412 : Nat := 118140960795 + 578412 * 2 ^ 59
def prefixEnd_578412 : Nat := 4983230072969 + 3 ^ 40 * 578412 * 2
def baseEnd_578412 : Nat := 198002248218997462726625

theorem tailTrace_578412 : CollatzResearch.WordTrace tailWord_578412 prefixEnd_578412 198002248218997462726625 := by
  unfold tailWord_578412
  simp only [CollatzResearch.WordTrace]
  refine ⟨10548209390259791875020745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14064279187013055833360993 10548209390259791875020745)
  ·
    refine ⟨7911157042694843906265559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10548209390259791875020745 7911157042694843906265559)
    ·
      refine ⟨11866735564042265859398339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7911157042694843906265559 11866735564042265859398339)
      ·
        refine ⟨17800103346063398789097509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11866735564042265859398339 17800103346063398789097509)
        ·
          refine ⟨3337519377386887272955783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17800103346063398789097509 3337519377386887272955783)
          ·
            refine ⟨5006279066080330909433675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3337519377386887272955783 5006279066080330909433675)
            ·
              refine ⟨7509418599120496364150513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5006279066080330909433675 7509418599120496364150513)
              ·
                refine ⟨5632063949340372273112885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7509418599120496364150513 5632063949340372273112885)
                ·
                  refine ⟨528005995250659900604333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5632063949340372273112885 528005995250659900604333)
                  ·
                    refine ⟨198002248218997462726625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 528005995250659900604333 198002248218997462726625)
                    ·
                      rfl

theorem cell22_578412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_578412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578412 prefixEnd_578412 := by exact prefixLift 578412
  have htrace : WordTrace (prefixWord ++ tailWord_578412) baseStart_578412 baseEnd_578412 := by
    simpa [prefixWord, tailWord_578412, baseEnd_578412] using wordTrace_append hprefix tailTrace_578412
  have hstable : (prefixWord ++ tailWord_578412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578412).length < 2 ^ (prefixWord ++ tailWord_578412).sum := by decide
  have hdescent : baseEnd_578412 < baseStart_578412 := by decide
  rcases family_descends (prefixWord ++ tailWord_578412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578463 : List Nat := [1, 1, 2, 5, 2, 3, 1, 3, 1, 3]
def baseStart_578463 : Nat := 118140960795 + 578463 * 2 ^ 59
def prefixEnd_578463 : Nat := 4983230072969 + 3 ^ 40 * 578463 * 2
def baseEnd_578463 : Nat := 198019706561250329701469

theorem tailTrace_578463 : CollatzResearch.WordTrace tailWord_578463 prefixEnd_578463 198019706561250329701469 := by
  unfold tailWord_578463
  simp only [CollatzResearch.WordTrace]
  refine ⟨21098278903334819460148043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14065519268889879640098695 21098278903334819460148043)
  ·
    refine ⟨31647418355002229190222065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21098278903334819460148043 31647418355002229190222065)
    ·
      refine ⟨23735563766251671892666549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31647418355002229190222065 23735563766251671892666549)
      ·
        refine ⟨2225209103086094239937489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23735563766251671892666549 2225209103086094239937489)
        ·
          refine ⟨1668906827314570679953117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2225209103086094239937489 1668906827314570679953117)
          ·
            refine ⟨625840060242964004982419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1668906827314570679953117 625840060242964004982419)
            ·
              refine ⟨938760090364446007473629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625840060242964004982419 938760090364446007473629)
              ·
                refine ⟨352035033886667252802611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 938760090364446007473629 352035033886667252802611)
                ·
                  refine ⟨528052550830000879203917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352035033886667252802611 528052550830000879203917)
                  ·
                    refine ⟨198019706561250329701469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 528052550830000879203917 198019706561250329701469)
                    ·
                      rfl

theorem cell22_578463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 1, 3].length) (baseStart_578463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578463 prefixEnd_578463 := by exact prefixLift 578463
  have htrace : WordTrace (prefixWord ++ tailWord_578463) baseStart_578463 baseEnd_578463 := by
    simpa [prefixWord, tailWord_578463, baseEnd_578463] using wordTrace_append hprefix tailTrace_578463
  have hstable : (prefixWord ++ tailWord_578463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578463).length < 2 ^ (prefixWord ++ tailWord_578463).sum := by decide
  have hdescent : baseEnd_578463 < baseStart_578463 := by decide
  rcases family_descends (prefixWord ++ tailWord_578463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578487 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 6]
def baseStart_578487 : Nat := 118140960795 + 578487 * 2 ^ 59
def prefixEnd_578487 : Nat := 4983230072969 + 3 ^ 40 * 578487 * 2
def baseEnd_578487 : Nat := 66009307417240755700465

theorem tailTrace_578487 : CollatzResearch.WordTrace tailWord_578487 prefixEnd_578487 66009307417240755700465 := by
  unfold tailWord_578487
  simp only [CollatzResearch.WordTrace]
  refine ⟨21099154255247871559021715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14066102836831914372681143 21099154255247871559021715)
  ·
    refine ⟨31648731382871807338532573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21099154255247871559021715 31648731382871807338532573)
    ·
      refine ⟨11868274268576927751949715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31648731382871807338532573 11868274268576927751949715)
      ·
        refine ⟨17802411402865391627924573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11868274268576927751949715 17802411402865391627924573)
        ·
          refine ⟨6675904276074521860471715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17802411402865391627924573 6675904276074521860471715)
          ·
            refine ⟨10013856414111782790707573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6675904276074521860471715 10013856414111782790707573)
            ·
              refine ⟨938799038822979636628835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10013856414111782790707573 938799038822979636628835)
              ·
                refine ⟨1408198558234469454943253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938799038822979636628835 1408198558234469454943253)
                ·
                  refine ⟨66009307417240755700465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1408198558234469454943253 66009307417240755700465)
                  ·
                    rfl

theorem cell22_578487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 6].length) (baseStart_578487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578487 prefixEnd_578487 := by exact prefixLift 578487
  have htrace : WordTrace (prefixWord ++ tailWord_578487) baseStart_578487 baseEnd_578487 := by
    simpa [prefixWord, tailWord_578487, baseEnd_578487] using wordTrace_append hprefix tailTrace_578487
  have hstable : (prefixWord ++ tailWord_578487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578487).length < 2 ^ (prefixWord ++ tailWord_578487).sum := by decide
  have hdescent : baseEnd_578487 < baseStart_578487 := by decide
  rcases family_descends (prefixWord ++ tailWord_578487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578493 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 5]
def baseStart_578493 : Nat := 118140960795 + 578493 * 2 ^ 59
def prefixEnd_578493 : Nat := 4983230072969 + 3 ^ 40 * 578493 * 2
def baseEnd_578493 : Nat := 66009992058113417150459

theorem tailTrace_578493 : CollatzResearch.WordTrace tailWord_578493 prefixEnd_578493 66009992058113417150459 := by
  unfold tailWord_578493
  simp only [CollatzResearch.WordTrace]
  refine ⟨21099373093226134583740133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14066248728817423055826755 21099373093226134583740133)
  ·
    refine ⟨3956132454979900234451275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21099373093226134583740133 3956132454979900234451275)
    ·
      refine ⟨5934198682469850351676913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3956132454979900234451275 5934198682469850351676913)
      ·
        refine ⟨4450649011852387763757685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5934198682469850351676913 4450649011852387763757685)
        ·
          refine ⟨417248344861161352852283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4450649011852387763757685 417248344861161352852283)
          ·
            refine ⟨625872517291742029278425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417248344861161352852283 625872517291742029278425)
            ·
              refine ⟨469404387968806521958819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625872517291742029278425 469404387968806521958819)
              ·
                refine ⟨704106581953209782938229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469404387968806521958819 704106581953209782938229)
                ·
                  refine ⟨66009992058113417150459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 704106581953209782938229 66009992058113417150459)
                  ·
                    rfl

theorem cell22_578493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_578493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578493 prefixEnd_578493 := by exact prefixLift 578493
  have htrace : WordTrace (prefixWord ++ tailWord_578493) baseStart_578493 baseEnd_578493 := by
    simpa [prefixWord, tailWord_578493, baseEnd_578493] using wordTrace_append hprefix tailTrace_578493
  have hstable : (prefixWord ++ tailWord_578493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578493).length < 2 ^ (prefixWord ++ tailWord_578493).sum := by decide
  have hdescent : baseEnd_578493 < baseStart_578493 := by decide
  rcases family_descends (prefixWord ++ tailWord_578493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578538 : List Nat := [3, 1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_578538 : Nat := 118140960795 + 578538 * 2 ^ 59
def prefixEnd_578538 : Nat := 4983230072969 + 3 ^ 40 * 578538 * 2
def baseEnd_578538 : Nat := 66015126864658378025413

theorem tailTrace_578538 : CollatzResearch.WordTrace tailWord_578538 prefixEnd_578538 66015126864658378025413 := by
  unfold tailWord_578538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275253594515776817282067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14067342918708738179418845 5275253594515776817282067)
  ·
    refine ⟨7912880391773665225923101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5275253594515776817282067 7912880391773665225923101)
    ·
      refine ⟨2967330146915124459721163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7912880391773665225923101 2967330146915124459721163)
      ·
        refine ⟨4450995220372686689581745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2967330146915124459721163 4450995220372686689581745)
        ·
          refine ⟨3338246415279515017186309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4450995220372686689581745 3338246415279515017186309)
          ·
            refine ⟨625921202864909065722433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3338246415279515017186309 625921202864909065722433)
            ·
              refine ⟨469440902148681799291825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625921202864909065722433 469440902148681799291825)
              ·
                refine ⟨352080676611511349468869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469440902148681799291825 352080676611511349468869)
                ·
                  refine ⟨66015126864658378025413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352080676611511349468869 66015126864658378025413)
                  ·
                    rfl

theorem cell22_578538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_578538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578538 prefixEnd_578538 := by exact prefixLift 578538
  have htrace : WordTrace (prefixWord ++ tailWord_578538) baseStart_578538 baseEnd_578538 := by
    simpa [prefixWord, tailWord_578538, baseEnd_578538] using wordTrace_append hprefix tailTrace_578538
  have hstable : (prefixWord ++ tailWord_578538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578538).length < 2 ^ (prefixWord ++ tailWord_578538).sum := by decide
  have hdescent : baseEnd_578538 < baseStart_578538 := by decide
  rcases family_descends (prefixWord ++ tailWord_578538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578594 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_578594 : Nat := 118140960795 + 578594 * 2 ^ 59
def prefixEnd_578594 : Nat := 4983230072969 + 3 ^ 40 * 578594 * 2
def baseEnd_578594 : Nat := 66021516846136551558689

theorem tailTrace_578594 : CollatzResearch.WordTrace tailWord_578594 prefixEnd_578594 66021516846136551558689 := by
  unfold tailWord_578594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275764216465057208291709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14068704577240152555444557 5275764216465057208291709)
  ·
    refine ⟨1978411581174396453109391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5275764216465057208291709 1978411581174396453109391)
    ·
      refine ⟨2967617371761594679664087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1978411581174396453109391 2967617371761594679664087)
      ·
        refine ⟨4451426057642392019496131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2967617371761594679664087 4451426057642392019496131)
        ·
          refine ⟨6677139086463588029244197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4451426057642392019496131 6677139086463588029244197)
          ·
            refine ⟨1251963578711922755483287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6677139086463588029244197 1251963578711922755483287)
            ·
              refine ⟨1877945368067884133224931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251963578711922755483287 1877945368067884133224931)
              ·
                refine ⟨2816918052101826199837397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877945368067884133224931 2816918052101826199837397)
                ·
                  refine ⟨66021516846136551558689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2816918052101826199837397 66021516846136551558689)
                  ·
                    rfl

theorem cell22_578594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_578594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578594 prefixEnd_578594 := by exact prefixLift 578594
  have htrace : WordTrace (prefixWord ++ tailWord_578594) baseStart_578594 baseEnd_578594 := by
    simpa [prefixWord, tailWord_578594, baseEnd_578594] using wordTrace_append hprefix tailTrace_578594
  have hstable : (prefixWord ++ tailWord_578594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578594).length < 2 ^ (prefixWord ++ tailWord_578594).sum := by decide
  have hdescent : baseEnd_578594 < baseStart_578594 := by decide
  rcases family_descends (prefixWord ++ tailWord_578594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578671 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 2, 3]
def baseStart_578671 : Nat := 118140960795 + 578671 * 2 ^ 59
def prefixEnd_578671 : Nat := 4983230072969 + 3 ^ 40 * 578671 * 2
def baseEnd_578671 : Nat := 198090909212007120500831

theorem tailTrace_578671 : CollatzResearch.WordTrace tailWord_578671 prefixEnd_578671 198090909212007120500831 := by
  unfold tailWord_578671
  simp only [CollatzResearch.WordTrace]
  refine ⟨21105865286581270983719867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14070576857720847322479911 21105865286581270983719867)
  ·
    refine ⟨31658797929871906475579801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21105865286581270983719867 31658797929871906475579801)
    ·
      refine ⟨23744098447403929856684851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31658797929871906475579801 23744098447403929856684851)
      ·
        refine ⟨35616147671105894785027277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23744098447403929856684851 35616147671105894785027277)
        ·
          refine ⟨13356055376664710544385229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35616147671105894785027277 13356055376664710544385229)
          ·
            refine ⟨5008520766249266454144461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13356055376664710544385229 5008520766249266454144461)
            ·
              refine ⟨1878195287343474920304173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5008520766249266454144461 1878195287343474920304173)
              ·
                refine ⟨704323232753803095114065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1878195287343474920304173 704323232753803095114065)
                ·
                  refine ⟨528242424565352321335549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704323232753803095114065 528242424565352321335549)
                  ·
                    refine ⟨198090909212007120500831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 528242424565352321335549 198090909212007120500831)
                    ·
                      rfl

theorem cell22_578671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 3].length) (baseStart_578671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578671 prefixEnd_578671 := by exact prefixLift 578671
  have htrace : WordTrace (prefixWord ++ tailWord_578671) baseStart_578671 baseEnd_578671 := by
    simpa [prefixWord, tailWord_578671, baseEnd_578671] using wordTrace_append hprefix tailTrace_578671
  have hstable : (prefixWord ++ tailWord_578671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578671).length < 2 ^ (prefixWord ++ tailWord_578671).sum := by decide
  have hdescent : baseEnd_578671 < baseStart_578671 := by decide
  rcases family_descends (prefixWord ++ tailWord_578671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578718 : List Nat := [4, 3, 1, 1, 2, 3, 1, 7]
def baseStart_578718 : Nat := 118140960795 + 578718 * 2 ^ 59
def prefixEnd_578718 : Nat := 4983230072969 + 3 ^ 40 * 578718 * 2
def baseEnd_578718 : Nat := 22011888696946073841743

theorem tailTrace_578718 : CollatzResearch.WordTrace tailWord_578718 prefixEnd_578718 22011888696946073841743 := by
  unfold tailWord_578718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2638447439676374751335101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14071719678273998673787205 2638447439676374751335101)
  ·
    refine ⟨989417789878640531750663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2638447439676374751335101 989417789878640531750663)
    ·
      refine ⟨1484126684817960797625995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989417789878640531750663 1484126684817960797625995)
      ·
        refine ⟨2226190027226941196438993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1484126684817960797625995 2226190027226941196438993)
        ·
          refine ⟨1669642520420205897329245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2226190027226941196438993 1669642520420205897329245)
          ·
            refine ⟨626115945157577211498467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1669642520420205897329245 626115945157577211498467)
            ·
              refine ⟨939173917736365817247701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626115945157577211498467 939173917736365817247701)
              ·
                refine ⟨22011888696946073841743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 939173917736365817247701 22011888696946073841743)
                ·
                  rfl

theorem cell22_578718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_578718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578718 prefixEnd_578718 := by exact prefixLift 578718
  have htrace : WordTrace (prefixWord ++ tailWord_578718) baseStart_578718 baseEnd_578718 := by
    simpa [prefixWord, tailWord_578718, baseEnd_578718] using wordTrace_append hprefix tailTrace_578718
  have hstable : (prefixWord ++ tailWord_578718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578718).length < 2 ^ (prefixWord ++ tailWord_578718).sum := by decide
  have hdescent : baseEnd_578718 < baseStart_578718 := by decide
  rcases family_descends (prefixWord ++ tailWord_578718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578750 : List Nat := [4, 2, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_578750 : Nat := 118140960795 + 578750 * 2 ^ 59
def prefixEnd_578750 : Nat := 4983230072969 + 3 ^ 40 * 578750 * 2
def baseEnd_578750 : Nat := 198117952526477247775589

theorem tailTrace_578750 : CollatzResearch.WordTrace tailWord_578750 prefixEnd_578750 198117952526477247775589 := by
  unfold tailWord_578750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2638593331661883434480713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14072497768863378317230469 2638593331661883434480713)
  ·
    refine ⟨1978944998746412575860535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2638593331661883434480713 1978944998746412575860535)
    ·
      refine ⟨2968417498119618863790803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1978944998746412575860535 2968417498119618863790803)
      ·
        refine ⟨4452626247179428295686205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2968417498119618863790803 4452626247179428295686205)
        ·
          refine ⟨1669734842692285610882327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4452626247179428295686205 1669734842692285610882327)
          ·
            refine ⟨2504602264038428416323491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669734842692285610882327 2504602264038428416323491)
            ·
              refine ⟨3756903396057642624485237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504602264038428416323491 3756903396057642624485237)
              ·
                refine ⟨352209693380403996045491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3756903396057642624485237 352209693380403996045491)
                ·
                  refine ⟨528314540070605994068237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352209693380403996045491 528314540070605994068237)
                  ·
                    refine ⟨198117952526477247775589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 528314540070605994068237 198117952526477247775589)
                    ·
                      rfl

theorem cell22_578750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_578750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578750 prefixEnd_578750 := by exact prefixLift 578750
  have htrace : WordTrace (prefixWord ++ tailWord_578750) baseStart_578750 baseEnd_578750 := by
    simpa [prefixWord, tailWord_578750, baseEnd_578750] using wordTrace_append hprefix tailTrace_578750
  have hstable : (prefixWord ++ tailWord_578750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578750).length < 2 ^ (prefixWord ++ tailWord_578750).sum := by decide
  have hdescent : baseEnd_578750 < baseStart_578750 := by decide
  rcases family_descends (prefixWord ++ tailWord_578750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578806 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_578806 : Nat := 118140960795 + 578806 * 2 ^ 59
def prefixEnd_578806 : Nat := 4983230072969 + 3 ^ 40 * 578806 * 2
def baseEnd_578806 : Nat := 198137122470911768375417

theorem tailTrace_578806 : CollatzResearch.WordTrace tailWord_578806 prefixEnd_578806 198137122470911768375417 := by
  unfold tailWord_578806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319424321318261814992767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14073859427394792693256181 1319424321318261814992767)
  ·
    refine ⟨1979136481977392722489151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1319424321318261814992767 1979136481977392722489151)
    ·
      refine ⟨2968704722966089083733727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1979136481977392722489151 2968704722966089083733727)
      ·
        refine ⟨4453057084449133625600591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2968704722966089083733727 4453057084449133625600591)
        ·
          refine ⟨6679585626673700438400887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4453057084449133625600591 6679585626673700438400887)
          ·
            refine ⟨10019378440010550657601331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6679585626673700438400887 10019378440010550657601331)
            ·
              refine ⟨15029067660015825986401997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10019378440010550657601331 15029067660015825986401997)
              ·
                refine ⟨5635900372505934744900749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15029067660015825986401997 5635900372505934744900749)
                ·
                  refine ⟨2113462639689725529337781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5635900372505934744900749 2113462639689725529337781)
                  ·
                    refine ⟨198137122470911768375417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2113462639689725529337781 198137122470911768375417)
                    ·
                      rfl

theorem cell22_578806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_578806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578806 prefixEnd_578806 := by exact prefixLift 578806
  have htrace : WordTrace (prefixWord ++ tailWord_578806) baseStart_578806 baseEnd_578806 := by
    simpa [prefixWord, tailWord_578806, baseEnd_578806] using wordTrace_append hprefix tailTrace_578806
  have hstable : (prefixWord ++ tailWord_578806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578806).length < 2 ^ (prefixWord ++ tailWord_578806).sum := by decide
  have hdescent : baseEnd_578806 < baseStart_578806 := by decide
  rcases family_descends (prefixWord ++ tailWord_578806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578819 : List Nat := [1, 1, 1, 3, 2, 4, 10]
def baseStart_578819 : Nat := 118140960795 + 578819 * 2 ^ 59
def prefixEnd_578819 : Nat := 4983230072969 + 3 ^ 40 * 578819 * 2
def baseEnd_578819 : Nat := 7338576764317928437051

theorem tailTrace_578819 : CollatzResearch.WordTrace tailWord_578819 prefixEnd_578819 7338576764317928437051 := by
  unfold tailWord_578819
  simp only [CollatzResearch.WordTrace]
  refine ⟨21111263290045092260107511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14074175526696728173405007 21111263290045092260107511)
  ·
    refine ⟨31666894935067638390161267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21111263290045092260107511 31666894935067638390161267)
    ·
      refine ⟨47500342402601457585241901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31666894935067638390161267 47500342402601457585241901)
      ·
        refine ⟨17812628400975546594465713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47500342402601457585241901 17812628400975546594465713)
        ·
          refine ⟨13359471300731659945849285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17812628400975546594465713 13359471300731659945849285)
          ·
            refine ⟨2504900868887186239846741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13359471300731659945849285 2504900868887186239846741)
            ·
              refine ⟨7338576764317928437051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2504900868887186239846741 7338576764317928437051)
              ·
                rfl

theorem cell22_578819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 10].length) (baseStart_578819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578819 prefixEnd_578819 := by exact prefixLift 578819
  have htrace : WordTrace (prefixWord ++ tailWord_578819) baseStart_578819 baseEnd_578819 := by
    simpa [prefixWord, tailWord_578819, baseEnd_578819] using wordTrace_append hprefix tailTrace_578819
  have hstable : (prefixWord ++ tailWord_578819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578819).length < 2 ^ (prefixWord ++ tailWord_578819).sum := by decide
  have hdescent : baseEnd_578819 < baseStart_578819 := by decide
  rcases family_descends (prefixWord ++ tailWord_578819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578821 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_578821 : Nat := 118140960795 + 578821 * 2 ^ 59
def prefixEnd_578821 : Nat := 4983230072969 + 3 ^ 40 * 578821 * 2
def baseEnd_578821 : Nat := 198142257277456729250371

theorem tailTrace_578821 : CollatzResearch.WordTrace tailWord_578821 prefixEnd_578821 198142257277456729250371 := by
  unfold tailWord_578821
  simp only [CollatzResearch.WordTrace]
  refine ⟨21111336236037846601680317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14074224157358564401120211 21111336236037846601680317)
  ·
    refine ⟨7916751088514192475630119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21111336236037846601680317 7916751088514192475630119)
    ·
      refine ⟨11875126632771288713445179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7916751088514192475630119 11875126632771288713445179)
      ·
        refine ⟨17812689949156933070167769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11875126632771288713445179 17812689949156933070167769)
        ·
          refine ⟨13359517461867699802625827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17812689949156933070167769 13359517461867699802625827)
          ·
            refine ⟨20039276192801549703938741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13359517461867699802625827 20039276192801549703938741)
            ·
              refine ⟨1878682143075145284744257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20039276192801549703938741 1878682143075145284744257)
              ·
                refine ⟨1409011607306358963558193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1878682143075145284744257 1409011607306358963558193)
                ·
                  refine ⟨1056758705479769222668645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1409011607306358963558193 1056758705479769222668645)
                  ·
                    refine ⟨198142257277456729250371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1056758705479769222668645 198142257277456729250371)
                    ·
                      rfl

theorem cell22_578821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_578821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578821 prefixEnd_578821 := by exact prefixLift 578821
  have htrace : WordTrace (prefixWord ++ tailWord_578821) baseStart_578821 baseEnd_578821 := by
    simpa [prefixWord, tailWord_578821, baseEnd_578821] using wordTrace_append hprefix tailTrace_578821
  have hstable : (prefixWord ++ tailWord_578821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578821).length < 2 ^ (prefixWord ++ tailWord_578821).sum := by decide
  have hdescent : baseEnd_578821 < baseStart_578821 := by decide
  rcases family_descends (prefixWord ++ tailWord_578821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578840 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 2, 3]
def baseStart_578840 : Nat := 118140960795 + 578840 * 2 ^ 59
def prefixEnd_578840 : Nat := 4983230072969 + 3 ^ 40 * 578840 * 2
def baseEnd_578840 : Nat := 198148761365747013025313

theorem tailTrace_578840 : CollatzResearch.WordTrace tailWord_578840 prefixEnd_578840 198148761365747013025313 := by
  unfold tailWord_578840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10556014611484506423310987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14074686148646008564414649 10556014611484506423310987)
  ·
    refine ⟨15834021917226759634966481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10556014611484506423310987 15834021917226759634966481)
    ·
      refine ⟨11875516437920069726224861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15834021917226759634966481 11875516437920069726224861)
      ·
        refine ⟨4453318664220026147334323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11875516437920069726224861 4453318664220026147334323)
        ·
          refine ⟨6679977996330039221001485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4453318664220026147334323 6679977996330039221001485)
          ·
            refine ⟨2504991748623764707875557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6679977996330039221001485 2504991748623764707875557)
            ·
              refine ⟨469685952866955882726667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2504991748623764707875557 469685952866955882726667)
              ·
                refine ⟨704528929300433824090001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469685952866955882726667 704528929300433824090001)
                ·
                  refine ⟨528396696975325368067501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704528929300433824090001 528396696975325368067501)
                  ·
                    refine ⟨198148761365747013025313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 528396696975325368067501 198148761365747013025313)
                    ·
                      rfl

theorem cell22_578840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_578840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578840 prefixEnd_578840 := by exact prefixLift 578840
  have htrace : WordTrace (prefixWord ++ tailWord_578840) baseStart_578840 baseEnd_578840 := by
    simpa [prefixWord, tailWord_578840, baseEnd_578840] using wordTrace_append hprefix tailTrace_578840
  have hstable : (prefixWord ++ tailWord_578840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578840).length < 2 ^ (prefixWord ++ tailWord_578840).sum := by decide
  have hdescent : baseEnd_578840 < baseStart_578840 := by decide
  rcases family_descends (prefixWord ++ tailWord_578840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578870 : List Nat := [5, 1, 2, 3, 2, 9]
def baseStart_578870 : Nat := 118140960795 + 578870 * 2 ^ 59
def prefixEnd_578870 : Nat := 4983230072969 + 3 ^ 40 * 578870 * 2
def baseEnd_578870 : Nat := 2446407789862184379941

theorem tailTrace_578870 : CollatzResearch.WordTrace tailWord_578870 prefixEnd_578870 2446407789862184379941 := by
  unfold tailWord_578870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319570213303770498138379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14075415608573551980142709 1319570213303770498138379)
  ·
    refine ⟨1979355319955655747207569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1319570213303770498138379 1979355319955655747207569)
    ·
      refine ⟨1484516489966741810405677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1979355319955655747207569 1484516489966741810405677)
      ·
        refine ⟨556693683737528178902129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1484516489966741810405677 556693683737528178902129)
        ·
          refine ⟨417520262803146134176597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 556693683737528178902129 417520262803146134176597)
          ·
            refine ⟨2446407789862184379941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 417520262803146134176597 2446407789862184379941)
            ·
              rfl

theorem cell22_578870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 9].length) (baseStart_578870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578870 prefixEnd_578870 := by exact prefixLift 578870
  have htrace : WordTrace (prefixWord ++ tailWord_578870) baseStart_578870 baseEnd_578870 := by
    simpa [prefixWord, tailWord_578870, baseEnd_578870] using wordTrace_append hprefix tailTrace_578870
  have hstable : (prefixWord ++ tailWord_578870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578870).length < 2 ^ (prefixWord ++ tailWord_578870).sum := by decide
  have hdescent : baseEnd_578870 < baseStart_578870 := by decide
  rcases family_descends (prefixWord ++ tailWord_578870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578896 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_578896 : Nat := 118140960795 + 578896 * 2 ^ 59
def prefixEnd_578896 : Nat := 4983230072969 + 3 ^ 40 * 578896 * 2
def baseEnd_578896 : Nat := 198167931310181533625141

theorem tailTrace_578896 : CollatzResearch.WordTrace tailWord_578896 prefixEnd_578896 198167931310181533625141 := by
  unfold tailWord_578896
  simp only [CollatzResearch.WordTrace]
  refine ⟨10557035855383067205330271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14076047807177422940440361 10557035855383067205330271)
  ·
    refine ⟨15835553783074600807995407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10557035855383067205330271 15835553783074600807995407)
    ·
      refine ⟨23753330674611901211993111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15835553783074600807995407 23753330674611901211993111)
      ·
        refine ⟨35629996011917851817989667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23753330674611901211993111 35629996011917851817989667)
        ·
          refine ⟨53444994017876777726984501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35629996011917851817989667 53444994017876777726984501)
          ·
            refine ⟨5010468189175947911904797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53444994017876777726984501 5010468189175947911904797)
            ·
              refine ⟨1878925570940980466964299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5010468189175947911904797 1878925570940980466964299)
              ·
                refine ⟨2818388356411470700446449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878925570940980466964299 2818388356411470700446449)
                ·
                  refine ⟨2113791267308603025334837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2818388356411470700446449 2113791267308603025334837)
                  ·
                    refine ⟨198167931310181533625141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2113791267308603025334837 198167931310181533625141)
                    ·
                      rfl

theorem cell22_578896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_578896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578896 prefixEnd_578896 := by exact prefixLift 578896
  have htrace : WordTrace (prefixWord ++ tailWord_578896) baseStart_578896 baseEnd_578896 := by
    simpa [prefixWord, tailWord_578896, baseEnd_578896] using wordTrace_append hprefix tailTrace_578896
  have hstable : (prefixWord ++ tailWord_578896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578896).length < 2 ^ (prefixWord ++ tailWord_578896).sum := by decide
  have hdescent : baseEnd_578896 < baseStart_578896 := by decide
  rcases family_descends (prefixWord ++ tailWord_578896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578928 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 1, 4]
def baseStart_578928 : Nat := 118140960795 + 578928 * 2 ^ 59
def prefixEnd_578928 : Nat := 4983230072969 + 3 ^ 40 * 578928 * 2
def baseEnd_578928 : Nat := 198178885564144116825043

theorem tailTrace_578928 : CollatzResearch.WordTrace tailWord_578928 prefixEnd_578928 198178885564144116825043 := by
  unfold tailWord_578928
  simp only [CollatzResearch.WordTrace]
  refine ⟨10557619423325101937912719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14076825897766802583883625 10557619423325101937912719)
  ·
    refine ⟨15836429134987652906869079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10557619423325101937912719 15836429134987652906869079)
    ·
      refine ⟨23754643702481479360303619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15836429134987652906869079 23754643702481479360303619)
      ·
        refine ⟨35631965553722219040455429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23754643702481479360303619 35631965553722219040455429)
        ·
          refine ⟨6680993541322916070085393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35631965553722219040455429 6680993541322916070085393)
          ·
            refine ⟨5010745155992187052564045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6680993541322916070085393 5010745155992187052564045)
            ·
              refine ⟨1879029433497070144711517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5010745155992187052564045 1879029433497070144711517)
              ·
                refine ⟨704636037561401304266819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1879029433497070144711517 704636037561401304266819)
                ·
                  refine ⟨1056954056342101956400229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704636037561401304266819 1056954056342101956400229)
                  ·
                    refine ⟨198178885564144116825043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1056954056342101956400229 198178885564144116825043)
                    ·
                      rfl

theorem cell22_578928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_578928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578928 prefixEnd_578928 := by exact prefixLift 578928
  have htrace : WordTrace (prefixWord ++ tailWord_578928) baseStart_578928 baseEnd_578928 := by
    simpa [prefixWord, tailWord_578928, baseEnd_578928] using wordTrace_append hprefix tailTrace_578928
  have hstable : (prefixWord ++ tailWord_578928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578928).length < 2 ^ (prefixWord ++ tailWord_578928).sum := by decide
  have hdescent : baseEnd_578928 < baseStart_578928 := by decide
  rcases family_descends (prefixWord ++ tailWord_578928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578956 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_578956 : Nat := 118140960795 + 578956 * 2 ^ 59
def prefixEnd_578956 : Nat := 4983230072969 + 3 ^ 40 * 578956 * 2
def baseEnd_578956 : Nat := 198188470536361377124957

theorem tailTrace_578956 : CollatzResearch.WordTrace tailWord_578956 prefixEnd_578956 198188470536361377124957 := by
  unfold tailWord_578956
  simp only [CollatzResearch.WordTrace]
  refine ⟨10558130045274382328922361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14077506727032509771896481 10558130045274382328922361)
  ·
    refine ⟨7918597533955786746691771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10558130045274382328922361 7918597533955786746691771)
    ·
      refine ⟨11877896300933680120037657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7918597533955786746691771 11877896300933680120037657)
      ·
        refine ⟨8908422225700260090028243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11877896300933680120037657 8908422225700260090028243)
        ·
          refine ⟨13362633338550390135042365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8908422225700260090028243 13362633338550390135042365)
          ·
            refine ⟨5010987501956396300640887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13362633338550390135042365 5010987501956396300640887)
            ·
              refine ⟨7516481252934594450961331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5010987501956396300640887 7516481252934594450961331)
              ·
                refine ⟨11274721879401891676441997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7516481252934594450961331 11274721879401891676441997)
                ·
                  refine ⟨4228020704775709378665749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11274721879401891676441997 4228020704775709378665749)
                  ·
                    refine ⟨198188470536361377124957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4228020704775709378665749 198188470536361377124957)
                    ·
                      rfl

theorem cell22_578956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_578956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578956 prefixEnd_578956 := by exact prefixLift 578956
  have htrace : WordTrace (prefixWord ++ tailWord_578956) baseStart_578956 baseEnd_578956 := by
    simpa [prefixWord, tailWord_578956, baseEnd_578956] using wordTrace_append hprefix tailTrace_578956
  have hstable : (prefixWord ++ tailWord_578956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578956).length < 2 ^ (prefixWord ++ tailWord_578956).sum := by decide
  have hdescent : baseEnd_578956 < baseStart_578956 := by decide
  rcases family_descends (prefixWord ++ tailWord_578956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578973 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_578973 : Nat := 118140960795 + 578973 * 2 ^ 59
def prefixEnd_578973 : Nat := 4983230072969 + 3 ^ 40 * 578973 * 2
def baseEnd_578973 : Nat := 198194289983778999449905

theorem tailTrace_578973 : CollatzResearch.WordTrace tailWord_578973 prefixEnd_578973 198194289983778999449905 := by
  unfold tailWord_578973
  simp only [CollatzResearch.WordTrace]
  refine ⟨21116880131487176561213573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14077920087658117707475715 21116880131487176561213573)
  ·
    refine ⟨3959415024653845605227545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21116880131487176561213573 3959415024653845605227545)
    ·
      refine ⟨2969561268490384203920659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3959415024653845605227545 2969561268490384203920659)
      ·
        refine ⟨4454341902735576305880989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2969561268490384203920659 4454341902735576305880989)
        ·
          refine ⟨1670378213525841114705371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4454341902735576305880989 1670378213525841114705371)
          ·
            refine ⟨2505567320288761672058057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670378213525841114705371 2505567320288761672058057)
            ·
              refine ⟨1879175490216571254043543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2505567320288761672058057 1879175490216571254043543)
              ·
                refine ⟨2818763235324856881065315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879175490216571254043543 2818763235324856881065315)
                ·
                  refine ⟨4228144852987285321597973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818763235324856881065315 4228144852987285321597973)
                  ·
                    refine ⟨198194289983778999449905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4228144852987285321597973 198194289983778999449905)
                    ·
                      rfl

theorem cell22_578973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_578973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_578973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_578973 prefixEnd_578973 := by exact prefixLift 578973
  have htrace : WordTrace (prefixWord ++ tailWord_578973) baseStart_578973 baseEnd_578973 := by
    simpa [prefixWord, tailWord_578973, baseEnd_578973] using wordTrace_append hprefix tailTrace_578973
  have hstable : (prefixWord ++ tailWord_578973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578973).length < 2 ^ (prefixWord ++ tailWord_578973).sum := by decide
  have hdescent : baseEnd_578973 < baseStart_578973 := by decide
  rcases family_descends (prefixWord ++ tailWord_578973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579048 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_579048 : Nat := 118140960795 + 579048 * 2 ^ 59
def prefixEnd_579048 : Nat := 4983230072969 + 3 ^ 40 * 579048 * 2
def baseEnd_579048 : Nat := 198219964016503803824675

theorem tailTrace_579048 : CollatzResearch.WordTrace tailWord_579048 prefixEnd_579048 198219964016503803824675 := by
  unfold tailWord_579048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10559807803107732185096899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14079743737476976246795865 10559807803107732185096899)
  ·
    refine ⟨15839711704661598277645349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10559807803107732185096899 15839711704661598277645349)
    ·
      refine ⟨2969945944624049677058503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15839711704661598277645349 2969945944624049677058503)
      ·
        refine ⟨4454918916936074515587755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2969945944624049677058503 4454918916936074515587755)
        ·
          refine ⟨6682378375404111773381633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454918916936074515587755 6682378375404111773381633)
          ·
            refine ⟨5011783781553083830036225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6682378375404111773381633 5011783781553083830036225)
            ·
              refine ⟨3758837836164812872527169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5011783781553083830036225 3758837836164812872527169)
              ·
                refine ⟨2819128377123609654395377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3758837836164812872527169 2819128377123609654395377)
                ·
                  refine ⟨2114346282842707240796533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2819128377123609654395377 2114346282842707240796533)
                  ·
                    refine ⟨198219964016503803824675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2114346282842707240796533 198219964016503803824675)
                    ·
                      rfl

theorem cell22_579048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_579048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579048 prefixEnd_579048 := by exact prefixLift 579048
  have htrace : WordTrace (prefixWord ++ tailWord_579048) baseStart_579048 baseEnd_579048 := by
    simpa [prefixWord, tailWord_579048, baseEnd_579048] using wordTrace_append hprefix tailTrace_579048
  have hstable : (prefixWord ++ tailWord_579048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579048).length < 2 ^ (prefixWord ++ tailWord_579048).sum := by decide
  have hdescent : baseEnd_579048 < baseStart_579048 := by decide
  rcases family_descends (prefixWord ++ tailWord_579048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579112 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 6]
def baseStart_579112 : Nat := 118140960795 + 579112 * 2 ^ 59
def prefixEnd_579112 : Nat := 4983230072969 + 3 ^ 40 * 579112 * 2
def baseEnd_579112 : Nat := 66080624174809656741493

theorem tailTrace_579112 : CollatzResearch.WordTrace tailWord_579112 prefixEnd_579112 66080624174809656741493 := by
  unfold tailWord_579112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10560974938991801650261795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14081299918655735533682393 10560974938991801650261795)
  ·
    refine ⟨15841462408487702475392693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10560974938991801650261795 15841462408487702475392693)
    ·
      refine ⟨1485137100795722107068065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15841462408487702475392693 1485137100795722107068065)
      ·
        refine ⟨1113852825596791580301049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1485137100795722107068065 1113852825596791580301049)
        ·
          refine ⟨835389619197593685225787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1113852825596791580301049 835389619197593685225787)
          ·
            refine ⟨1253084428796390527838681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835389619197593685225787 1253084428796390527838681)
            ·
              refine ⟨939813321597292895879011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253084428796390527838681 939813321597292895879011)
              ·
                refine ⟨1409719982395939343818517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939813321597292895879011 1409719982395939343818517)
                ·
                  refine ⟨66080624174809656741493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1409719982395939343818517 66080624174809656741493)
                  ·
                    rfl

theorem cell22_579112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_579112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579112 prefixEnd_579112 := by exact prefixLift 579112
  have htrace : WordTrace (prefixWord ++ tailWord_579112) baseStart_579112 baseEnd_579112 := by
    simpa [prefixWord, tailWord_579112, baseEnd_579112] using wordTrace_append hprefix tailTrace_579112
  have hstable : (prefixWord ++ tailWord_579112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579112).length < 2 ^ (prefixWord ++ tailWord_579112).sum := by decide
  have hdescent : baseEnd_579112 < baseStart_579112 := by decide
  rcases family_descends (prefixWord ++ tailWord_579112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579172 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_579172 : Nat := 118140960795 + 579172 * 2 ^ 59
def prefixEnd_579172 : Nat := 4983230072969 + 3 ^ 40 * 579172 * 2
def baseEnd_579172 : Nat := 198262411750608813724295

theorem tailTrace_579172 : CollatzResearch.WordTrace tailWord_579172 prefixEnd_579172 198262411750608813724295 := by
  unfold tailWord_579172
  simp only [CollatzResearch.WordTrace]
  refine ⟨10562069128883116773853885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14082758838510822365138513 10562069128883116773853885)
  ·
    refine ⟨3960775923331168790195207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10562069128883116773853885 3960775923331168790195207)
    ·
      refine ⟨5941163884996753185292811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3960775923331168790195207 5941163884996753185292811)
      ·
        refine ⟨8911745827495129777939217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5941163884996753185292811 8911745827495129777939217)
        ·
          refine ⟨6683809370621347333454413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8911745827495129777939217 6683809370621347333454413)
          ·
            refine ⟨2506428513983005250045405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6683809370621347333454413 2506428513983005250045405)
            ·
              refine ⟨939910692743626968767027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2506428513983005250045405 939910692743626968767027)
              ·
                refine ⟨1409866039115440453150541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939910692743626968767027 1409866039115440453150541)
                ·
                  refine ⟨528699764668290169931453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1409866039115440453150541 528699764668290169931453)
                  ·
                    refine ⟨198262411750608813724295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 528699764668290169931453 198262411750608813724295)
                    ·
                      rfl

theorem cell22_579172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_579172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579172 prefixEnd_579172 := by exact prefixLift 579172
  have htrace : WordTrace (prefixWord ++ tailWord_579172) baseStart_579172 baseEnd_579172 := by
    simpa [prefixWord, tailWord_579172, baseEnd_579172] using wordTrace_append hprefix tailTrace_579172
  have hstable : (prefixWord ++ tailWord_579172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579172).length < 2 ^ (prefixWord ++ tailWord_579172).sum := by decide
  have hdescent : baseEnd_579172 < baseStart_579172 := by decide
  rcases family_descends (prefixWord ++ tailWord_579172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579183 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 1, 7]
def baseStart_579183 : Nat := 118140960795 + 579183 * 2 ^ 59
def prefixEnd_579183 : Nat := 4983230072969 + 3 ^ 40 * 579183 * 2
def baseEnd_579183 : Nat := 198266177275408451699261

theorem tailTrace_579183 : CollatzResearch.WordTrace tailWord_579183 prefixEnd_579183 198266177275408451699261 := by
  unfold tailWord_579183
  simp only [CollatzResearch.WordTrace]
  refine ⟨21124539460726382426358203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14083026307150921617572135 21124539460726382426358203)
  ·
    refine ⟨31686809191089573639537305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21124539460726382426358203 31686809191089573639537305)
    ·
      refine ⟨23765106893317180229652979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31686809191089573639537305 23765106893317180229652979)
      ·
        refine ⟨35647660339975770344479469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23765106893317180229652979 35647660339975770344479469)
        ·
          refine ⟨13367872627490913879179801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35647660339975770344479469 13367872627490913879179801)
          ·
            refine ⟨10025904470618185409384851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13367872627490913879179801 10025904470618185409384851)
            ·
              refine ⟨15038856705927278114077277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10025904470618185409384851 15038856705927278114077277)
              ·
                refine ⟨5639571264722729292778979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15038856705927278114077277 5639571264722729292778979)
                ·
                  refine ⟨8459356897084093939168469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5639571264722729292778979 8459356897084093939168469)
                  ·
                    refine ⟨198266177275408451699261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8459356897084093939168469 198266177275408451699261)
                    ·
                      rfl

theorem cell22_579183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_579183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579183 prefixEnd_579183 := by exact prefixLift 579183
  have htrace : WordTrace (prefixWord ++ tailWord_579183) baseStart_579183 baseEnd_579183 := by
    simpa [prefixWord, tailWord_579183, baseEnd_579183] using wordTrace_append hprefix tailTrace_579183
  have hstable : (prefixWord ++ tailWord_579183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579183).length < 2 ^ (prefixWord ++ tailWord_579183).sum := by decide
  have hdescent : baseEnd_579183 < baseStart_579183 := by decide
  rcases family_descends (prefixWord ++ tailWord_579183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579234 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_579234 : Nat := 118140960795 + 579234 * 2 ^ 59
def prefixEnd_579234 : Nat := 4983230072969 + 3 ^ 40 * 579234 * 2
def baseEnd_579234 : Nat := 198283635617661318674105

theorem tailTrace_579234 : CollatzResearch.WordTrace tailWord_579234 prefixEnd_579234 198283635617661318674105 := by
  unfold tailWord_579234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281599895885404534116189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14084266389027745424309837 5281599895885404534116189)
  ·
    refine ⟨1980599960957026700293571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5281599895885404534116189 1980599960957026700293571)
    ·
      refine ⟨2970899941435540050440357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1980599960957026700293571 2970899941435540050440357)
      ·
        refine ⟨557043739019163759457567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2970899941435540050440357 557043739019163759457567)
        ·
          refine ⟨835565608528745639186351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557043739019163759457567 835565608528745639186351)
          ·
            refine ⟨1253348412793118458779527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835565608528745639186351 1253348412793118458779527)
            ·
              refine ⟨1880022619189677688169291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253348412793118458779527 1880022619189677688169291)
              ·
                refine ⟨2820033928784516532253937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1880022619189677688169291 2820033928784516532253937)
                ·
                  refine ⟨2115025446588387399190453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2820033928784516532253937 2115025446588387399190453)
                  ·
                    refine ⟨198283635617661318674105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2115025446588387399190453 198283635617661318674105)
                    ·
                      rfl

theorem cell22_579234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_579234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579234 prefixEnd_579234 := by exact prefixLift 579234
  have htrace : WordTrace (prefixWord ++ tailWord_579234) baseStart_579234 baseEnd_579234 := by
    simpa [prefixWord, tailWord_579234, baseEnd_579234] using wordTrace_append hprefix tailTrace_579234
  have hstable : (prefixWord ++ tailWord_579234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579234).length < 2 ^ (prefixWord ++ tailWord_579234).sum := by decide
  have hdescent : baseEnd_579234 < baseStart_579234 := by decide
  rcases family_descends (prefixWord ++ tailWord_579234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579262 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_579262 : Nat := 118140960795 + 579262 * 2 ^ 59
def prefixEnd_579262 : Nat := 4983230072969 + 3 ^ 40 * 579262 * 2
def baseEnd_579262 : Nat := 198293220589878578974019

theorem tailTrace_579262 : CollatzResearch.WordTrace tailWord_579262 prefixEnd_579262 198293220589878578974019 := by
  unfold tailWord_579262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640927603430022364810505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14084947218293452612322693 2640927603430022364810505)
  ·
    refine ⟨1980695702572516773607879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2640927603430022364810505 1980695702572516773607879)
    ·
      refine ⟨2971043553858775160411819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1980695702572516773607879 2971043553858775160411819)
      ·
        refine ⟨4456565330788162740617729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2971043553858775160411819 4456565330788162740617729)
        ·
          refine ⟨3342423998091122055463297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4456565330788162740617729 3342423998091122055463297)
          ·
            refine ⟨2506817998568341541597473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3342423998091122055463297 2506817998568341541597473)
            ·
              refine ⟨1880113498926256156198105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506817998568341541597473 1880113498926256156198105)
              ·
                refine ⟨1410085124194692117148579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1880113498926256156198105 1410085124194692117148579)
                ·
                  refine ⟨2115127686292038175722869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410085124194692117148579 2115127686292038175722869)
                  ·
                    refine ⟨198293220589878578974019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2115127686292038175722869 198293220589878578974019)
                    ·
                      rfl

theorem cell22_579262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_579262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579262 prefixEnd_579262 := by exact prefixLift 579262
  have htrace : WordTrace (prefixWord ++ tailWord_579262) baseStart_579262 baseEnd_579262 := by
    simpa [prefixWord, tailWord_579262, baseEnd_579262] using wordTrace_append hprefix tailTrace_579262
  have hstable : (prefixWord ++ tailWord_579262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579262).length < 2 ^ (prefixWord ++ tailWord_579262).sum := by decide
  have hdescent : baseEnd_579262 < baseStart_579262 := by decide
  rcases family_descends (prefixWord ++ tailWord_579262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579307 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 3, 3]
def baseStart_579307 : Nat := 118140960795 + 579307 * 2 ^ 59
def prefixEnd_579307 : Nat := 4983230072969 + 3 ^ 40 * 579307 * 2
def baseEnd_579307 : Nat := 198308625009513461598881

theorem tailTrace_579307 : CollatzResearch.WordTrace tailWord_579307 prefixEnd_579307 198308625009513461598881 := by
  unfold tailWord_579307
  simp only [CollatzResearch.WordTrace]
  refine ⟨21129062112277151603872175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14086041408184767735914783 21129062112277151603872175)
  ·
    refine ⟨31693593168415727405808263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21129062112277151603872175 31693593168415727405808263)
    ·
      refine ⟨47540389752623591108712395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31693593168415727405808263 47540389752623591108712395)
      ·
        refine ⟨71310584628935386663068593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47540389752623591108712395 71310584628935386663068593)
        ·
          refine ⟨53482938471701539997301445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71310584628935386663068593 53482938471701539997301445)
          ·
            refine ⟨10028050963444038749494021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53482938471701539997301445 10028050963444038749494021)
            ·
              refine ⟨1880259555645757265530129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10028050963444038749494021 1880259555645757265530129)
              ·
                refine ⟨1410194666734317949147597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1880259555645757265530129 1410194666734317949147597)
                ·
                  refine ⟨528823000025369230930349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1410194666734317949147597 528823000025369230930349)
                  ·
                    refine ⟨198308625009513461598881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 528823000025369230930349 198308625009513461598881)
                    ·
                      rfl

theorem cell22_579307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 3].length) (baseStart_579307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579307 prefixEnd_579307 := by exact prefixLift 579307
  have htrace : WordTrace (prefixWord ++ tailWord_579307) baseStart_579307 baseEnd_579307 := by
    simpa [prefixWord, tailWord_579307, baseEnd_579307] using wordTrace_append hprefix tailTrace_579307
  have hstable : (prefixWord ++ tailWord_579307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579307).length < 2 ^ (prefixWord ++ tailWord_579307).sum := by decide
  have hdescent : baseEnd_579307 < baseStart_579307 := by decide
  rcases family_descends (prefixWord ++ tailWord_579307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579309 : List Nat := [1, 5, 1, 2, 1, 4, 2, 6]
def baseStart_579309 : Nat := 118140960795 + 579309 * 2 ^ 59
def prefixEnd_579309 : Nat := 4983230072969 + 3 ^ 40 * 579309 * 2
def baseEnd_579309 : Nat := 22034367738931791449875

theorem tailTrace_579309 : CollatzResearch.WordTrace tailWord_579309 prefixEnd_579309 22034367738931791449875 := by
  unfold tailWord_579309
  simp only [CollatzResearch.WordTrace]
  refine ⟨21129135058269905945444981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14086090038846603963629987 21129135058269905945444981)
  ·
    refine ⟨1980856411712803682385467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21129135058269905945444981 1980856411712803682385467)
    ·
      refine ⟨2971284617569205523578201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1980856411712803682385467 2971284617569205523578201)
      ·
        refine ⟨2228463463176904142683651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2971284617569205523578201 2228463463176904142683651)
        ·
          refine ⟨3342695194765356214025477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228463463176904142683651 3342695194765356214025477)
          ·
            refine ⟨626755349018504290129777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3342695194765356214025477 626755349018504290129777)
            ·
              refine ⟨470066511763878217597333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626755349018504290129777 470066511763878217597333)
              ·
                refine ⟨22034367738931791449875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 470066511763878217597333 22034367738931791449875)
                ·
                  rfl

theorem cell22_579309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 6].length) (baseStart_579309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579309 prefixEnd_579309 := by exact prefixLift 579309
  have htrace : WordTrace (prefixWord ++ tailWord_579309) baseStart_579309 baseEnd_579309 := by
    simpa [prefixWord, tailWord_579309, baseEnd_579309] using wordTrace_append hprefix tailTrace_579309
  have hstable : (prefixWord ++ tailWord_579309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579309).length < 2 ^ (prefixWord ++ tailWord_579309).sum := by decide
  have hdescent : baseEnd_579309 < baseStart_579309 := by decide
  rcases family_descends (prefixWord ++ tailWord_579309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579354 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_579354 : Nat := 118140960795 + 579354 * 2 ^ 59
def prefixEnd_579354 : Nat := 4983230072969 + 3 ^ 40 * 579354 * 2
def baseEnd_579354 : Nat := 66108238023340335224579

theorem tailTrace_579354 : CollatzResearch.WordTrace tailWord_579354 prefixEnd_579354 66108238023340335224579 := by
  unfold tailWord_579354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5282694085776719657708279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14087184228737919087222077 5282694085776719657708279)
  ·
    refine ⟨7924041128665079486562419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5282694085776719657708279 7924041128665079486562419)
    ·
      refine ⟨11886061692997619229843629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7924041128665079486562419 11886061692997619229843629)
      ·
        refine ⟨4457273134874107211191361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11886061692997619229843629 4457273134874107211191361)
        ·
          refine ⟨3342954851155580408393521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4457273134874107211191361 3342954851155580408393521)
          ·
            refine ⟨2507216138366685306295141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3342954851155580408393521 2507216138366685306295141)
            ·
              refine ⟨470103025943753494930339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2507216138366685306295141 470103025943753494930339)
              ·
                refine ⟨705154538915630242395509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470103025943753494930339 705154538915630242395509)
                ·
                  refine ⟨66108238023340335224579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 705154538915630242395509 66108238023340335224579)
                  ·
                    rfl

theorem cell22_579354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_579354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579354 prefixEnd_579354 := by exact prefixLift 579354
  have htrace : WordTrace (prefixWord ++ tailWord_579354) baseStart_579354 baseEnd_579354 := by
    simpa [prefixWord, tailWord_579354, baseEnd_579354] using wordTrace_append hprefix tailTrace_579354
  have hstable : (prefixWord ++ tailWord_579354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579354).length < 2 ^ (prefixWord ++ tailWord_579354).sum := by decide
  have hdescent : baseEnd_579354 < baseStart_579354 := by decide
  rcases family_descends (prefixWord ++ tailWord_579354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579459 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 3, 3]
def baseStart_579459 : Nat := 118140960795 + 579459 * 2 ^ 59
def prefixEnd_579459 : Nat := 4983230072969 + 3 ^ 40 * 579459 * 2
def baseEnd_579459 : Nat := 198360657715835731798415

theorem tailTrace_579459 : CollatzResearch.WordTrace tailWord_579459 prefixEnd_579459 198360657715835731798415 := by
  unfold tailWord_579459
  simp only [CollatzResearch.WordTrace]
  refine ⟨21134606007726481563405431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14089737338484321042270287 21134606007726481563405431)
  ·
    refine ⟨31701909011589722345108147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21134606007726481563405431 31701909011589722345108147)
    ·
      refine ⟨47552863517384583517662221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31701909011589722345108147 47552863517384583517662221)
      ·
        refine ⟨17832323819019218819123333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47552863517384583517662221 17832323819019218819123333)
        ·
          refine ⟨3343560716066103528585625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17832323819019218819123333 3343560716066103528585625)
          ·
            refine ⟨2507670537049577646439219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3343560716066103528585625 2507670537049577646439219)
            ·
              refine ⟨3761505805574366469658829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507670537049577646439219 3761505805574366469658829)
              ·
                refine ⟨1410564677090387426122061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3761505805574366469658829 1410564677090387426122061)
                ·
                  refine ⟨528961753908895284795773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1410564677090387426122061 528961753908895284795773)
                  ·
                    refine ⟨198360657715835731798415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 528961753908895284795773 198360657715835731798415)
                    ·
                      rfl

theorem cell22_579459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 3].length) (baseStart_579459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579459 prefixEnd_579459 := by exact prefixLift 579459
  have htrace : WordTrace (prefixWord ++ tailWord_579459) baseStart_579459 baseEnd_579459 := by
    simpa [prefixWord, tailWord_579459, baseEnd_579459] using wordTrace_append hprefix tailTrace_579459
  have hstable : (prefixWord ++ tailWord_579459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579459).length < 2 ^ (prefixWord ++ tailWord_579459).sum := by decide
  have hdescent : baseEnd_579459 < baseStart_579459 := by decide
  rcases family_descends (prefixWord ++ tailWord_579459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579476 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_579476 : Nat := 118140960795 + 579476 * 2 ^ 59
def prefixEnd_579476 : Nat := 4983230072969 + 3 ^ 40 * 579476 * 2
def baseEnd_579476 : Nat := 198366477163253354123363

theorem tailTrace_579476 : CollatzResearch.WordTrace tailWord_579476 prefixEnd_579476 198366477163253354123363 := by
  unfold tailWord_579476
  simp only [CollatzResearch.WordTrace]
  refine ⟨10567613024332446733387141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14090150699109928977849521 10567613024332446733387141)
  ·
    refine ⟨1981427442062333762510089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10567613024332446733387141 1981427442062333762510089)
    ·
      refine ⟨1486070581546750321882567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1981427442062333762510089 1486070581546750321882567)
      ·
        refine ⟨2229105872320125482823851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1486070581546750321882567 2229105872320125482823851)
        ·
          refine ⟨3343658808480188224235777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2229105872320125482823851 3343658808480188224235777)
          ·
            refine ⟨2507744106360141168176833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3343658808480188224235777 2507744106360141168176833)
            ·
              refine ⟨1880808079770105876132625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2507744106360141168176833 1880808079770105876132625)
              ·
                refine ⟨1410606059827579407099469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1880808079770105876132625 1410606059827579407099469)
                ·
                  refine ⟨528977272435342277662301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1410606059827579407099469 528977272435342277662301)
                  ·
                    refine ⟨198366477163253354123363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 528977272435342277662301 198366477163253354123363)
                    ·
                      rfl

theorem cell22_579476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_579476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579476 prefixEnd_579476 := by exact prefixLift 579476
  have htrace : WordTrace (prefixWord ++ tailWord_579476) baseStart_579476 baseEnd_579476 := by
    simpa [prefixWord, tailWord_579476, baseEnd_579476] using wordTrace_append hprefix tailTrace_579476
  have hstable : (prefixWord ++ tailWord_579476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579476).length < 2 ^ (prefixWord ++ tailWord_579476).sum := by decide
  have hdescent : baseEnd_579476 < baseStart_579476 := by decide
  rcases family_descends (prefixWord ++ tailWord_579476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579478 : List Nat := [5, 3, 1, 1, 2, 1, 1, 8]
def baseStart_579478 : Nat := 118140960795 + 579478 * 2 ^ 59
def prefixEnd_579478 : Nat := 4983230072969 + 3 ^ 40 * 579478 * 2
def baseEnd_579478 : Nat := 22040795756014001730373

theorem tailTrace_579478 : CollatzResearch.WordTrace tailWord_579478 prefixEnd_579478 22040795756014001730373 := by
  unfold tailWord_579478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1320956187166102988021693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14090199329771765205564725 1320956187166102988021693)
  ·
    refine ⟨495358570187288620508135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1320956187166102988021693 495358570187288620508135)
    ·
      refine ⟨743037855280932930762203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495358570187288620508135 743037855280932930762203)
      ·
        refine ⟨1114556782921399396143305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743037855280932930762203 1114556782921399396143305)
        ·
          refine ⟨835917587191049547107479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1114556782921399396143305 835917587191049547107479)
          ·
            refine ⟨1253876380786574320661219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835917587191049547107479 1253876380786574320661219)
            ·
              refine ⟨1880814571179861480991829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253876380786574320661219 1880814571179861480991829)
              ·
                refine ⟨22040795756014001730373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1880814571179861480991829 22040795756014001730373)
                ·
                  rfl

theorem cell22_579478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_579478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579478 prefixEnd_579478 := by exact prefixLift 579478
  have htrace : WordTrace (prefixWord ++ tailWord_579478) baseStart_579478 baseEnd_579478 := by
    simpa [prefixWord, tailWord_579478, baseEnd_579478] using wordTrace_append hprefix tailTrace_579478
  have hstable : (prefixWord ++ tailWord_579478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579478).length < 2 ^ (prefixWord ++ tailWord_579478).sum := by decide
  have hdescent : baseEnd_579478 < baseStart_579478 := by decide
  rcases family_descends (prefixWord ++ tailWord_579478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579604 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_579604 : Nat := 118140960795 + 579604 * 2 ^ 59
def prefixEnd_579604 : Nat := 4983230072969 + 3 ^ 40 * 579604 * 2
def baseEnd_579604 : Nat := 198410294179103686922971

theorem tailTrace_579604 : CollatzResearch.WordTrace tailWord_579604 prefixEnd_579604 198410294179103686922971 := by
  unfold tailWord_579604
  simp only [CollatzResearch.WordTrace]
  refine ⟨10569947296100585663716933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14093263061467447551622577 10569947296100585663716933)
  ·
    refine ⟨1981865118018859811946925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10569947296100585663716933 1981865118018859811946925)
    ·
      refine ⟨743199419257072429480097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1981865118018859811946925 743199419257072429480097)
      ·
        refine ⟨557399564442804322110073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743199419257072429480097 557399564442804322110073)
        ·
          refine ⟨418049673332103241582555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557399564442804322110073 418049673332103241582555)
          ·
            refine ⟨627074509998154862373833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418049673332103241582555 627074509998154862373833)
            ·
              refine ⟨470305882498616146780375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627074509998154862373833 470305882498616146780375)
              ·
                refine ⟨705458823747924220170563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470305882498616146780375 705458823747924220170563)
                ·
                  refine ⟨1058188235621886330255845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705458823747924220170563 1058188235621886330255845)
                  ·
                    refine ⟨198410294179103686922971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1058188235621886330255845 198410294179103686922971)
                    ·
                      rfl

theorem cell22_579604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_579604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579604 prefixEnd_579604 := by exact prefixLift 579604
  have htrace : WordTrace (prefixWord ++ tailWord_579604) baseStart_579604 baseEnd_579604 := by
    simpa [prefixWord, tailWord_579604, baseEnd_579604] using wordTrace_append hprefix tailTrace_579604
  have hstable : (prefixWord ++ tailWord_579604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579604).length < 2 ^ (prefixWord ++ tailWord_579604).sum := by decide
  have hdescent : baseEnd_579604 < baseStart_579604 := by decide
  rcases family_descends (prefixWord ++ tailWord_579604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579639 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 2, 5]
def baseStart_579639 : Nat := 118140960795 + 579639 * 2 ^ 59
def prefixEnd_579639 : Nat := 4983230072969 + 3 ^ 40 * 579639 * 2
def baseEnd_579639 : Nat := 198422275394375262297863

theorem tailTrace_579639 : CollatzResearch.WordTrace tailWord_579639 prefixEnd_579639 198422275394375262297863 := by
  unfold tailWord_579639
  simp only [CollatzResearch.WordTrace]
  refine ⟨21141171147074372304957971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14094114098049581536638647 21141171147074372304957971)
  ·
    refine ⟨31711756720611558457436957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21141171147074372304957971 31711756720611558457436957)
    ·
      refine ⟨11891908770229334421538859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31711756720611558457436957 11891908770229334421538859)
      ·
        refine ⟨17837863155344001632308289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11891908770229334421538859 17837863155344001632308289)
        ·
          refine ⟨13378397366508001224231217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17837863155344001632308289 13378397366508001224231217)
          ·
            refine ⟨10033798024881000918173413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13378397366508001224231217 10033798024881000918173413)
            ·
              refine ⟨1881337129665187672157515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10033798024881000918173413 1881337129665187672157515)
              ·
                refine ⟨2822005694497781508236273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881337129665187672157515 2822005694497781508236273)
                ·
                  refine ⟨2116504270873336131177205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2822005694497781508236273 2116504270873336131177205)
                  ·
                    refine ⟨198422275394375262297863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2116504270873336131177205 198422275394375262297863)
                    ·
                      rfl

theorem cell22_579639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_579639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579639 prefixEnd_579639 := by exact prefixLift 579639
  have htrace : WordTrace (prefixWord ++ tailWord_579639) baseStart_579639 baseEnd_579639 := by
    simpa [prefixWord, tailWord_579639, baseEnd_579639] using wordTrace_append hprefix tailTrace_579639
  have hstable : (prefixWord ++ tailWord_579639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579639).length < 2 ^ (prefixWord ++ tailWord_579639).sum := by decide
  have hdescent : baseEnd_579639 < baseStart_579639 := by decide
  rcases family_descends (prefixWord ++ tailWord_579639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579671 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 1, 4]
def baseStart_579671 : Nat := 118140960795 + 579671 * 2 ^ 59
def prefixEnd_579671 : Nat := 4983230072969 + 3 ^ 40 * 579671 * 2
def baseEnd_579671 : Nat := 198433229648337845497765

theorem tailTrace_579671 : CollatzResearch.WordTrace tailWord_579671 prefixEnd_579671 198433229648337845497765 := by
  unfold tailWord_579671
  simp only [CollatzResearch.WordTrace]
  refine ⟨21142338282958441770122867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14094892188638961180081911 21142338282958441770122867)
  ·
    refine ⟨31713507424437662655184301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21142338282958441770122867 31713507424437662655184301)
    ·
      refine ⟨11892565284164123495694113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31713507424437662655184301 11892565284164123495694113)
      ·
        refine ⟨8919423963123092621770585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11892565284164123495694113 8919423963123092621770585)
        ·
          refine ⟨6689567972342319466327939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8919423963123092621770585 6689567972342319466327939)
          ·
            refine ⟨10034351958513479199491909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6689567972342319466327939 10034351958513479199491909)
            ·
              refine ⟨1881440992221277349904733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10034351958513479199491909 1881440992221277349904733)
              ·
                refine ⟨705540372082979006214275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1881440992221277349904733 705540372082979006214275)
                ·
                  refine ⟨1058310558124468509321413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705540372082979006214275 1058310558124468509321413)
                  ·
                    refine ⟨198433229648337845497765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1058310558124468509321413 198433229648337845497765)
                    ·
                      rfl

theorem cell22_579671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_579671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579671 prefixEnd_579671 := by exact prefixLift 579671
  have htrace : WordTrace (prefixWord ++ tailWord_579671) baseStart_579671 baseEnd_579671 := by
    simpa [prefixWord, tailWord_579671, baseEnd_579671] using wordTrace_append hprefix tailTrace_579671
  have hstable : (prefixWord ++ tailWord_579671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579671).length < 2 ^ (prefixWord ++ tailWord_579671).sum := by decide
  have hdescent : baseEnd_579671 < baseStart_579671 := by decide
  rcases family_descends (prefixWord ++ tailWord_579671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579735 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 2, 3]
def baseStart_579735 : Nat := 118140960795 + 579735 * 2 ^ 59
def prefixEnd_579735 : Nat := 4983230072969 + 3 ^ 40 * 579735 * 2
def baseEnd_579735 : Nat := 198455138156263011897569

theorem tailTrace_579735 : CollatzResearch.WordTrace tailWord_579735 prefixEnd_579735 198455138156263011897569 := by
  unfold tailWord_579735
  simp only [CollatzResearch.WordTrace]
  refine ⟨21144672554726580700452659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14096448369817720466968439 21144672554726580700452659)
  ·
    refine ⟨31717008832089871050678989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21144672554726580700452659 31717008832089871050678989)
    ·
      refine ⟨11893878312033701644004621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31717008832089871050678989 11893878312033701644004621)
      ·
        refine ⟨4460204367012638116501733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11893878312033701644004621 4460204367012638116501733)
        ·
          refine ⟨836288318814869646844075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4460204367012638116501733 836288318814869646844075)
          ·
            refine ⟨1254432478222304470266113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836288318814869646844075 1254432478222304470266113)
            ·
              refine ⟨940824358666728352699585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254432478222304470266113 940824358666728352699585)
              ·
                refine ⟨705618269000046264524689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940824358666728352699585 705618269000046264524689)
                ·
                  refine ⟨529213701750034698393517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 705618269000046264524689 529213701750034698393517)
                  ·
                    refine ⟨198455138156263011897569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 529213701750034698393517 198455138156263011897569)
                    ·
                      rfl

theorem cell22_579735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_579735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579735 prefixEnd_579735 := by exact prefixLift 579735
  have htrace : WordTrace (prefixWord ++ tailWord_579735) baseStart_579735 baseEnd_579735 := by
    simpa [prefixWord, tailWord_579735, baseEnd_579735] using wordTrace_append hprefix tailTrace_579735
  have hstable : (prefixWord ++ tailWord_579735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579735).length < 2 ^ (prefixWord ++ tailWord_579735).sum := by decide
  have hdescent : baseEnd_579735 < baseStart_579735 := by decide
  rcases family_descends (prefixWord ++ tailWord_579735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579748 : List Nat := [2, 3, 1, 2, 4, 2, 1, 7]
def baseStart_579748 : Nat := 118140960795 + 579748 * 2 ^ 59
def prefixEnd_579748 : Nat := 4983230072969 + 3 ^ 40 * 579748 * 2
def baseEnd_579748 : Nat := 22051065369103923480281

theorem tailTrace_579748 : CollatzResearch.WordTrace tailWord_579748 prefixEnd_579748 22051065369103923480281 := by
  unfold tailWord_579748
  simp only [CollatzResearch.WordTrace]
  refine ⟨10572573351839741960337949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14096764469119655947117265 10572573351839741960337949)
  ·
    refine ⟨3964715006939903235126731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10572573351839741960337949 3964715006939903235126731)
    ·
      refine ⟨5947072510409854852690097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3964715006939903235126731 5947072510409854852690097)
      ·
        refine ⟨4460304382807391139517573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5947072510409854852690097 4460304382807391139517573)
        ·
          refine ⟨836307071776385838659545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4460304382807391139517573 836307071776385838659545)
          ·
            refine ⟨627230303832289378994659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 836307071776385838659545 627230303832289378994659)
            ·
              refine ⟨940845455748434068491989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627230303832289378994659 940845455748434068491989)
              ·
                refine ⟨22051065369103923480281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 940845455748434068491989 22051065369103923480281)
                ·
                  rfl

theorem cell22_579748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 7].length) (baseStart_579748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579748 prefixEnd_579748 := by exact prefixLift 579748
  have htrace : WordTrace (prefixWord ++ tailWord_579748) baseStart_579748 baseEnd_579748 := by
    simpa [prefixWord, tailWord_579748, baseEnd_579748] using wordTrace_append hprefix tailTrace_579748
  have hstable : (prefixWord ++ tailWord_579748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579748).length < 2 ^ (prefixWord ++ tailWord_579748).sum := by decide
  have hdescent : baseEnd_579748 < baseStart_579748 := by decide
  rcases family_descends (prefixWord ++ tailWord_579748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579759 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 9]
def baseStart_579759 : Nat := 118140960795 + 579759 * 2 ^ 59
def prefixEnd_579759 : Nat := 4983230072969 + 3 ^ 40 * 579759 * 2
def baseEnd_579759 : Nat := 66154451282244983099165

theorem tailTrace_579759 : CollatzResearch.WordTrace tailWord_579759 prefixEnd_579759 66154451282244983099165 := by
  unfold tailWord_579759
  simp only [CollatzResearch.WordTrace]
  refine ⟨21145547906639632799326331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14097031937759755199550887 21145547906639632799326331)
  ·
    refine ⟨31718321859959449198989497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21145547906639632799326331 31718321859959449198989497)
    ·
      refine ⟨23788741394969586899242123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31718321859959449198989497 23788741394969586899242123)
      ·
        refine ⟨35683112092454380348863185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23788741394969586899242123 35683112092454380348863185)
        ·
          refine ⟨26762334069340785261647389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35683112092454380348863185 26762334069340785261647389)
          ·
            refine ⟨10035875276002794473117771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26762334069340785261647389 10035875276002794473117771)
            ·
              refine ⟨15053812914004191709676657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10035875276002794473117771 15053812914004191709676657)
              ·
                refine ⟨11290359685503143782257493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15053812914004191709676657 11290359685503143782257493)
                ·
                  refine ⟨66154451282244983099165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11290359685503143782257493 66154451282244983099165)
                  ·
                    rfl

theorem cell22_579759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 9].length) (baseStart_579759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579759 prefixEnd_579759 := by exact prefixLift 579759
  have htrace : WordTrace (prefixWord ++ tailWord_579759) baseStart_579759 baseEnd_579759 := by
    simpa [prefixWord, tailWord_579759, baseEnd_579759] using wordTrace_append hprefix tailTrace_579759
  have hstable : (prefixWord ++ tailWord_579759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579759).length < 2 ^ (prefixWord ++ tailWord_579759).sum := by decide
  have hdescent : baseEnd_579759 < baseStart_579759 := by decide
  rcases family_descends (prefixWord ++ tailWord_579759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579765 : List Nat := [1, 3, 3, 4, 1, 1, 3, 6]
def baseStart_579765 : Nat := 118140960795 + 579765 * 2 ^ 59
def prefixEnd_579765 : Nat := 4983230072969 + 3 ^ 40 * 579765 * 2
def baseEnd_579765 : Nat := 22051711974372548183053

theorem tailTrace_579765 : CollatzResearch.WordTrace tailWord_579765 prefixEnd_579765 22051711974372548183053 := by
  unfold tailWord_579765
  simp only [CollatzResearch.WordTrace]
  refine ⟨21145766744617895824044749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14097177829745263882696499 21145766744617895824044749)
  ·
    refine ⟨7929662529231710934016781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21145766744617895824044749 7929662529231710934016781)
    ·
      refine ⟨2973623448461891600256293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7929662529231710934016781 2973623448461891600256293)
      ·
        refine ⟨557554396586604675048055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2973623448461891600256293 557554396586604675048055)
        ·
          refine ⟨836331594879907012572083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557554396586604675048055 836331594879907012572083)
          ·
            refine ⟨1254497392319860518858125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836331594879907012572083 1254497392319860518858125)
            ·
              refine ⟨470436522119947694571797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1254497392319860518858125 470436522119947694571797)
              ·
                refine ⟨22051711974372548183053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 470436522119947694571797 22051711974372548183053)
                ·
                  rfl

theorem cell22_579765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 6].length) (baseStart_579765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579765 prefixEnd_579765 := by exact prefixLift 579765
  have htrace : WordTrace (prefixWord ++ tailWord_579765) baseStart_579765 baseEnd_579765 := by
    simpa [prefixWord, tailWord_579765, baseEnd_579765] using wordTrace_append hprefix tailTrace_579765
  have hstable : (prefixWord ++ tailWord_579765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579765).length < 2 ^ (prefixWord ++ tailWord_579765).sum := by decide
  have hdescent : baseEnd_579765 < baseStart_579765 := by decide
  rcases family_descends (prefixWord ++ tailWord_579765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579823 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 1, 4]
def baseStart_579823 : Nat := 118140960795 + 579823 * 2 ^ 59
def prefixEnd_579823 : Nat := 4983230072969 + 3 ^ 40 * 579823 * 2
def baseEnd_579823 : Nat := 198485262354660115697299

theorem tailTrace_579823 : CollatzResearch.WordTrace tailWord_579823 prefixEnd_579823 198485262354660115697299 := by
  unfold tailWord_579823
  simp only [CollatzResearch.WordTrace]
  refine ⟨21147882178407771729656123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14098588118938514486437415 21147882178407771729656123)
  ·
    refine ⟨31721823267611657594484185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21147882178407771729656123 31721823267611657594484185)
    ·
      refine ⟨23791367450708743195863139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31721823267611657594484185 23791367450708743195863139)
      ·
        refine ⟨35687051176063114793794709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23791367450708743195863139 35687051176063114793794709)
        ·
          refine ⟨1672830523877958505959127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35687051176063114793794709 1672830523877958505959127)
          ·
            refine ⟨2509245785816937758938691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672830523877958505959127 2509245785816937758938691)
            ·
              refine ⟨3763868678725406638408037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2509245785816937758938691 3763868678725406638408037)
              ·
                refine ⟨705725377261013744701507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3763868678725406638408037 705725377261013744701507)
                ·
                  refine ⟨1058588065891520617052261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705725377261013744701507 1058588065891520617052261)
                  ·
                    refine ⟨198485262354660115697299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1058588065891520617052261 198485262354660115697299)
                    ·
                      rfl

theorem cell22_579823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_579823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579823 prefixEnd_579823 := by exact prefixLift 579823
  have htrace : WordTrace (prefixWord ++ tailWord_579823) baseStart_579823 baseEnd_579823 := by
    simpa [prefixWord, tailWord_579823, baseEnd_579823] using wordTrace_append hprefix tailTrace_579823
  have hstable : (prefixWord ++ tailWord_579823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579823).length < 2 ^ (prefixWord ++ tailWord_579823).sum := by decide
  have hdescent : baseEnd_579823 < baseStart_579823 := by decide
  rcases family_descends (prefixWord ++ tailWord_579823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579992 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 1, 4]
def baseStart_579992 : Nat := 118140960795 + 579992 * 2 ^ 59
def prefixEnd_579992 : Nat := 4983230072969 + 3 ^ 40 * 579992 * 2
def baseEnd_579992 : Nat := 198543114508400008221781

theorem tailTrace_579992 : CollatzResearch.WordTrace tailWord_579992 prefixEnd_579992 198543114508400008221781 := by
  unfold tailWord_579992
  simp only [CollatzResearch.WordTrace]
  refine ⟨10577023057397756796279115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14102697409863675728372153 10577023057397756796279115)
  ·
    refine ⟨15865534586096635194418673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10577023057397756796279115 15865534586096635194418673)
    ·
      refine ⟨11899150939572476395814005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15865534586096635194418673 11899150939572476395814005)
      ·
        refine ⟨1115545400584919662107563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11899150939572476395814005 1115545400584919662107563)
        ·
          refine ⟨1673318100877379493161345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115545400584919662107563 1673318100877379493161345)
          ·
            refine ⟨1254988575658034619871009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1673318100877379493161345 1254988575658034619871009)
            ·
              refine ⟨941241431743525964903257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254988575658034619871009 941241431743525964903257)
              ·
                refine ⟨705931073807644473677443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941241431743525964903257 705931073807644473677443)
                ·
                  refine ⟨1058896610711466710516165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705931073807644473677443 1058896610711466710516165)
                  ·
                    refine ⟨198543114508400008221781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1058896610711466710516165 198543114508400008221781)
                    ·
                      rfl

theorem cell22_579992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_579992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_579992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_579992 prefixEnd_579992 := by exact prefixLift 579992
  have htrace : WordTrace (prefixWord ++ tailWord_579992) baseStart_579992 baseEnd_579992 := by
    simpa [prefixWord, tailWord_579992, baseEnd_579992] using wordTrace_append hprefix tailTrace_579992
  have hstable : (prefixWord ++ tailWord_579992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579992).length < 2 ^ (prefixWord ++ tailWord_579992).sum := by decide
  have hdescent : baseEnd_579992 < baseStart_579992 := by decide
  rcases family_descends (prefixWord ++ tailWord_579992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580003 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 1, 6]
def baseStart_580003 : Nat := 118140960795 + 580003 * 2 ^ 59
def prefixEnd_580003 : Nat := 4983230072969 + 3 ^ 40 * 580003 * 2
def baseEnd_580003 : Nat := 198546880033199646196747

theorem tailTrace_580003 : CollatzResearch.WordTrace tailWord_580003 prefixEnd_580003 198546880033199646196747 := by
  unfold tailWord_580003
  simp only [CollatzResearch.WordTrace]
  refine ⟨21154447317755662471208663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14102964878503774980805775 21154447317755662471208663)
  ·
    refine ⟨31731670976633493706812995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21154447317755662471208663 31731670976633493706812995)
    ·
      refine ⟨47597506464950240560219493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31731670976633493706812995 47597506464950240560219493)
      ·
        refine ⟨8924532462178170105041155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47597506464950240560219493 8924532462178170105041155)
        ·
          refine ⟨13386798693267255157561733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8924532462178170105041155 13386798693267255157561733)
          ·
            refine ⟨2510024754987610342042825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13386798693267255157561733 2510024754987610342042825)
            ·
              refine ⟨1882518566240707756532119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2510024754987610342042825 1882518566240707756532119)
              ·
                refine ⟨2823777849361061634798179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1882518566240707756532119 2823777849361061634798179)
                ·
                  refine ⟨4235666774041592452197269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823777849361061634798179 4235666774041592452197269)
                  ·
                    refine ⟨198546880033199646196747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4235666774041592452197269 198546880033199646196747)
                    ·
                      rfl

theorem cell22_580003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 6].length) (baseStart_580003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580003 prefixEnd_580003 := by exact prefixLift 580003
  have htrace : WordTrace (prefixWord ++ tailWord_580003) baseStart_580003 baseEnd_580003 := by
    simpa [prefixWord, tailWord_580003, baseEnd_580003] using wordTrace_append hprefix tailTrace_580003
  have hstable : (prefixWord ++ tailWord_580003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580003).length < 2 ^ (prefixWord ++ tailWord_580003).sum := by decide
  have hdescent : baseEnd_580003 < baseStart_580003 := by decide
  rcases family_descends (prefixWord ++ tailWord_580003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580007 : List Nat := [1, 1, 6, 1, 1, 2, 3, 3, 4]
def baseStart_580007 : Nat := 118140960795 + 580007 * 2 ^ 59
def prefixEnd_580007 : Nat := 4983230072969 + 3 ^ 40 * 580007 * 2
def baseEnd_580007 : Nat := 66182749771648323032245

theorem tailTrace_580007 : CollatzResearch.WordTrace tailWord_580007 prefixEnd_580007 66182749771648323032245 := by
  unfold tailWord_580007
  simp only [CollatzResearch.WordTrace]
  refine ⟨21154593209741171154354275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14103062139827447436236183 21154593209741171154354275)
  ·
    refine ⟨31731889814611756731531413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21154593209741171154354275 31731889814611756731531413)
    ·
      refine ⟨1487432335059926096790535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31731889814611756731531413 1487432335059926096790535)
      ·
        refine ⟨2231148502589889145185803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1487432335059926096790535 2231148502589889145185803)
        ·
          refine ⟨3346722753884833717778705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2231148502589889145185803 3346722753884833717778705)
          ·
            refine ⟨2510042065413625288334029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3346722753884833717778705 2510042065413625288334029)
            ·
              refine ⟨941265774530109483125261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2510042065413625288334029 941265774530109483125261)
              ·
                refine ⟨352974665448791056171973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 941265774530109483125261 352974665448791056171973)
                ·
                  refine ⟨66182749771648323032245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352974665448791056171973 66182749771648323032245)
                  ·
                    rfl

theorem cell22_580007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 4].length) (baseStart_580007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580007 prefixEnd_580007 := by exact prefixLift 580007
  have htrace : WordTrace (prefixWord ++ tailWord_580007) baseStart_580007 baseEnd_580007 := by
    simpa [prefixWord, tailWord_580007, baseEnd_580007] using wordTrace_append hprefix tailTrace_580007
  have hstable : (prefixWord ++ tailWord_580007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580007).length < 2 ^ (prefixWord ++ tailWord_580007).sum := by decide
  have hdescent : baseEnd_580007 < baseStart_580007 := by decide
  rcases family_descends (prefixWord ++ tailWord_580007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580039 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 2, 3]
def baseStart_580039 : Nat := 118140960795 + 580039 * 2 ^ 59
def prefixEnd_580039 : Nat := 4983230072969 + 3 ^ 40 * 580039 * 2
def baseEnd_580039 : Nat := 198559203568907552296637

theorem tailTrace_580039 : CollatzResearch.WordTrace tailWord_580039 prefixEnd_580039 198559203568907552296637 := by
  unfold tailWord_580039
  simp only [CollatzResearch.WordTrace]
  refine ⟨21155760345625240619519171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14103840230416827079679447 21155760345625240619519171)
  ·
    refine ⟨31733640518437860929278757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21155760345625240619519171 31733640518437860929278757)
    ·
      refine ⟨5950057597207098924239767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31733640518437860929278757 5950057597207098924239767)
      ·
        refine ⟨8925086395810648386359651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5950057597207098924239767 8925086395810648386359651)
        ·
          refine ⟨13387629593715972579539477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8925086395810648386359651 13387629593715972579539477)
          ·
            refine ⟨627545137205436214665913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13387629593715972579539477 627545137205436214665913)
            ·
              refine ⟨470658852904077160999435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627545137205436214665913 470658852904077160999435)
              ·
                refine ⟨705988279356115741499153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470658852904077160999435 705988279356115741499153)
                ·
                  refine ⟨529491209517086806124365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 705988279356115741499153 529491209517086806124365)
                  ·
                    refine ⟨198559203568907552296637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 529491209517086806124365 198559203568907552296637)
                    ·
                      rfl

theorem cell22_580039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_580039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580039 prefixEnd_580039 := by exact prefixLift 580039
  have htrace : WordTrace (prefixWord ++ tailWord_580039) baseStart_580039 baseEnd_580039 := by
    simpa [prefixWord, tailWord_580039, baseEnd_580039] using wordTrace_append hprefix tailTrace_580039
  have hstable : (prefixWord ++ tailWord_580039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580039).length < 2 ^ (prefixWord ++ tailWord_580039).sum := by decide
  have hdescent : baseEnd_580039 < baseStart_580039 := by decide
  rcases family_descends (prefixWord ++ tailWord_580039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580080 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 5]
def baseStart_580080 : Nat := 118140960795 + 580080 * 2 ^ 59
def prefixEnd_580080 : Nat := 4983230072969 + 3 ^ 40 * 580080 * 2
def baseEnd_580080 : Nat := 66191079568932370673837

theorem tailTrace_580080 : CollatzResearch.WordTrace tailWord_580080 prefixEnd_580080 66191079568932370673837 := by
  unfold tailWord_580080
  simp only [CollatzResearch.WordTrace]
  refine ⟨10578627869238352310880847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14104837158984469747841129 10578627869238352310880847)
  ·
    refine ⟨15867941803857528466321271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10578627869238352310880847 15867941803857528466321271)
    ·
      refine ⟨23801912705786292699481907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15867941803857528466321271 23801912705786292699481907)
      ·
        refine ⟨35702869058679439049222861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23801912705786292699481907 35702869058679439049222861)
        ·
          refine ⟨13388575897004789643458573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35702869058679439049222861 13388575897004789643458573)
          ·
            refine ⟨5020715961376796116296965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13388575897004789643458573 5020715961376796116296965)
            ·
              refine ⟨941384242758149271805681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5020715961376796116296965 941384242758149271805681)
              ·
                refine ⟨706038182068611953854261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941384242758149271805681 706038182068611953854261)
                ·
                  refine ⟨66191079568932370673837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 706038182068611953854261 66191079568932370673837)
                  ·
                    rfl

theorem cell22_580080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_580080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580080 prefixEnd_580080 := by exact prefixLift 580080
  have htrace : WordTrace (prefixWord ++ tailWord_580080) baseStart_580080 baseEnd_580080 := by
    simpa [prefixWord, tailWord_580080, baseEnd_580080] using wordTrace_append hprefix tailTrace_580080
  have hstable : (prefixWord ++ tailWord_580080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580080).length < 2 ^ (prefixWord ++ tailWord_580080).sum := by decide
  have hdescent : baseEnd_580080 < baseStart_580080 := by decide
  rcases family_descends (prefixWord ++ tailWord_580080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580157 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_580157 : Nat := 118140960795 + 580157 * 2 ^ 59
def prefixEnd_580157 : Nat := 4983230072969 + 3 ^ 40 * 580157 * 2
def baseEnd_580157 : Nat := 198599597380394577846275

theorem tailTrace_580157 : CollatzResearch.WordTrace tailWord_580157 prefixEnd_580157 198599597380394577846275 := by
  unfold tailWord_580157
  simp only [CollatzResearch.WordTrace]
  refine ⟨21160064159197746772314725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14106709439465164514876483 21160064159197746772314725)
  ·
    refine ⟨3967512029849577519809011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21160064159197746772314725 3967512029849577519809011)
    ·
      refine ⟨5951268044774366279713517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3967512029849577519809011 5951268044774366279713517)
      ·
        refine ⟨2231725516790387354892569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5951268044774366279713517 2231725516790387354892569)
        ·
          refine ⟨1673794137592790516169427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2231725516790387354892569 1673794137592790516169427)
          ·
            refine ⟨2510691206389185774254141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673794137592790516169427 2510691206389185774254141)
            ·
              refine ⟨941509202395944665345303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2510691206389185774254141 941509202395944665345303)
              ·
                refine ⟨1412263803593916998017955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941509202395944665345303 1412263803593916998017955)
                ·
                  refine ⟨2118395705390875497026933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412263803593916998017955 2118395705390875497026933)
                  ·
                    refine ⟨198599597380394577846275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2118395705390875497026933 198599597380394577846275)
                    ·
                      rfl

theorem cell22_580157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_580157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580157 prefixEnd_580157 := by exact prefixLift 580157
  have htrace : WordTrace (prefixWord ++ tailWord_580157) baseStart_580157 baseEnd_580157 := by
    simpa [prefixWord, tailWord_580157, baseEnd_580157] using wordTrace_append hprefix tailTrace_580157
  have hstable : (prefixWord ++ tailWord_580157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580157).length < 2 ^ (prefixWord ++ tailWord_580157).sum := by decide
  have hdescent : baseEnd_580157 < baseStart_580157 := by decide
  rcases family_descends (prefixWord ++ tailWord_580157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580170 : List Nat := [3, 1, 2, 1, 1, 5, 1, 8]
def baseStart_580170 : Nat := 118140960795 + 580170 * 2 ^ 59
def prefixEnd_580170 : Nat := 4983230072969 + 3 ^ 40 * 580170 * 2
def baseEnd_580170 : Nat := 22067116394007430807915

theorem tailTrace_580170 : CollatzResearch.WordTrace tailWord_580170 prefixEnd_580170 22067116394007430807915 := by
  unfold tailWord_580170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5290134577037662498134491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14107025538767099995025309 5290134577037662498134491)
  ·
    refine ⟨7935201865556493747201737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5290134577037662498134491 7935201865556493747201737)
    ·
      refine ⟨5951401399167370310401303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7935201865556493747201737 5951401399167370310401303)
      ·
        refine ⟨8927102098751055465601955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5951401399167370310401303 8927102098751055465601955)
        ·
          refine ⟨13390653148126583198402933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8927102098751055465601955 13390653148126583198402933)
          ·
            refine ⟨1255373732636867174850275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13390653148126583198402933 1255373732636867174850275)
            ·
              refine ⟨1883060598955300762275413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255373732636867174850275 1883060598955300762275413)
              ·
                refine ⟨22067116394007430807915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1883060598955300762275413 22067116394007430807915)
                ·
                  rfl

theorem cell22_580170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_580170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580170 prefixEnd_580170 := by exact prefixLift 580170
  have htrace : WordTrace (prefixWord ++ tailWord_580170) baseStart_580170 baseEnd_580170 := by
    simpa [prefixWord, tailWord_580170, baseEnd_580170] using wordTrace_append hprefix tailTrace_580170
  have hstable : (prefixWord ++ tailWord_580170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580170).length < 2 ^ (prefixWord ++ tailWord_580170).sum := by decide
  have hdescent : baseEnd_580170 < baseStart_580170 := by decide
  rcases family_descends (prefixWord ++ tailWord_580170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580208 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 2, 3]
def baseStart_580208 : Nat := 118140960795 + 580208 * 2 ^ 59
def prefixEnd_580208 : Nat := 4983230072969 + 3 ^ 40 * 580208 * 2
def baseEnd_580208 : Nat := 198617055722647444821119

theorem tailTrace_580208 : CollatzResearch.WordTrace tailWord_580208 prefixEnd_580208 198617055722647444821119 := by
  unfold tailWord_580208
  simp only [CollatzResearch.WordTrace]
  refine ⟨10580962141006491241210639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14107949521341988321614185 10580962141006491241210639)
  ·
    refine ⟨15871443211509736861815959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10580962141006491241210639 15871443211509736861815959)
    ·
      refine ⟨23807164817264605292723939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15871443211509736861815959 23807164817264605292723939)
      ·
        refine ⟨35710747225896907939085909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23807164817264605292723939 35710747225896907939085909)
        ·
          refine ⟨418485319053479389911163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 35710747225896907939085909 418485319053479389911163)
          ·
            refine ⟨627727978580219084866745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418485319053479389911163 627727978580219084866745)
            ·
              refine ⟨470795983935164313650059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627727978580219084866745 470795983935164313650059)
              ·
                refine ⟨706193975902746470475089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470795983935164313650059 706193975902746470475089)
                ·
                  refine ⟨529645481927059852856317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 706193975902746470475089 529645481927059852856317)
                  ·
                    refine ⟨198617055722647444821119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 529645481927059852856317 198617055722647444821119)
                    ·
                      rfl

theorem cell22_580208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 2, 3].length) (baseStart_580208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580208 prefixEnd_580208 := by exact prefixLift 580208
  have htrace : WordTrace (prefixWord ++ tailWord_580208) baseStart_580208 baseEnd_580208 := by
    simpa [prefixWord, tailWord_580208, baseEnd_580208] using wordTrace_append hprefix tailTrace_580208
  have hstable : (prefixWord ++ tailWord_580208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580208).length < 2 ^ (prefixWord ++ tailWord_580208).sum := by decide
  have hdescent : baseEnd_580208 < baseStart_580208 := by decide
  rcases family_descends (prefixWord ++ tailWord_580208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580277 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 8]
def baseStart_580277 : Nat := 118140960795 + 580277 * 2 ^ 59
def prefixEnd_580277 : Nat := 4983230072969 + 3 ^ 40 * 580277 * 2
def baseEnd_580277 : Nat := 66213558610918088281969

theorem tailTrace_580277 : CollatzResearch.WordTrace tailWord_580277 prefixEnd_580277 66213558610918088281969 := by
  unfold tailWord_580277
  simp only [CollatzResearch.WordTrace]
  refine ⟨21164440918763007266683085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14109627279175338177788723 21164440918763007266683085)
  ·
    refine ⟨7936665344536127725006157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21164440918763007266683085 7936665344536127725006157)
    ·
      refine ⟨2976249504201047896877309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7936665344536127725006157 2976249504201047896877309)
      ·
        refine ⟨1116093564075392961328991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2976249504201047896877309 1116093564075392961328991)
        ·
          refine ⟨1674140346113089441993487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116093564075392961328991 1674140346113089441993487)
          ·
            refine ⟨2511210519169634162990231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674140346113089441993487 2511210519169634162990231)
            ·
              refine ⟨3766815778754451244485347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511210519169634162990231 3766815778754451244485347)
              ·
                refine ⟨5650223668131676866728021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766815778754451244485347 5650223668131676866728021)
                ·
                  refine ⟨66213558610918088281969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5650223668131676866728021 66213558610918088281969)
                  ·
                    rfl

theorem cell22_580277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_580277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580277 prefixEnd_580277 := by exact prefixLift 580277
  have htrace : WordTrace (prefixWord ++ tailWord_580277) baseStart_580277 baseEnd_580277 := by
    simpa [prefixWord, tailWord_580277, baseEnd_580277] using wordTrace_append hprefix tailTrace_580277
  have hstable : (prefixWord ++ tailWord_580277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580277).length < 2 ^ (prefixWord ++ tailWord_580277).sum := by decide
  have hdescent : baseEnd_580277 < baseStart_580277 := by decide
  rcases family_descends (prefixWord ++ tailWord_580277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580296 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 1, 4]
def baseStart_580296 : Nat := 118140960795 + 580296 * 2 ^ 59
def prefixEnd_580296 : Nat := 4983230072969 + 3 ^ 40 * 580296 * 2
def baseEnd_580296 : Nat := 198647179921044548620849

theorem tailTrace_580296 : CollatzResearch.WordTrace tailWord_580296 prefixEnd_580296 198647179921044548620849 := by
  unfold tailWord_580296
  simp only [CollatzResearch.WordTrace]
  refine ⟨10582566952847086755812371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14110089270462782341083161 10582566952847086755812371)
  ·
    refine ⟨15873850429270630133718557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10582566952847086755812371 15873850429270630133718557)
    ·
      refine ⟨5952693910976486300144459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15873850429270630133718557 5952693910976486300144459)
      ·
        refine ⟨8929040866464729450216689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5952693910976486300144459 8929040866464729450216689)
        ·
          refine ⟨6696780649848547087662517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8929040866464729450216689 6696780649848547087662517)
          ·
            refine ⟨627823185923301289468361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6696780649848547087662517 627823185923301289468361)
            ·
              refine ⟨470867389442475967101271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627823185923301289468361 470867389442475967101271)
              ·
                refine ⟨706301084163713950651907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470867389442475967101271 706301084163713950651907)
                ·
                  refine ⟨1059451626245570925977861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706301084163713950651907 1059451626245570925977861)
                  ·
                    refine ⟨198647179921044548620849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1059451626245570925977861 198647179921044548620849)
                    ·
                      rfl

theorem cell22_580296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_580296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580296 prefixEnd_580296 := by exact prefixLift 580296
  have htrace : WordTrace (prefixWord ++ tailWord_580296) baseStart_580296 baseEnd_580296 := by
    simpa [prefixWord, tailWord_580296, baseEnd_580296] using wordTrace_append hprefix tailTrace_580296
  have hstable : (prefixWord ++ tailWord_580296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580296).length < 2 ^ (prefixWord ++ tailWord_580296).sum := by decide
  have hdescent : baseEnd_580296 < baseStart_580296 := by decide
  rcases family_descends (prefixWord ++ tailWord_580296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580305 : List Nat := [1, 2, 2, 1, 2, 3, 11]
def baseStart_580305 : Nat := 118140960795 + 580305 * 2 ^ 59
def prefixEnd_580305 : Nat := 4983230072969 + 3 ^ 40 * 580305 * 2
def baseEnd_580305 : Nat := 7357417066850797227623

theorem tailTrace_580305 : CollatzResearch.WordTrace tailWord_580305 prefixEnd_580305 7357417066850797227623 := by
  unfold tailWord_580305
  simp only [CollatzResearch.WordTrace]
  refine ⟨21165462162661568048702369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14110308108441045365801579 21165462162661568048702369)
  ·
    refine ⟨15874096621996176036526777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21165462162661568048702369 15874096621996176036526777)
    ·
      refine ⟨11905572466497132027395083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15874096621996176036526777 11905572466497132027395083)
      ·
        refine ⟨17858358699745698041092625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11905572466497132027395083 17858358699745698041092625)
        ·
          refine ⟨13393769024809273530819469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17858358699745698041092625 13393769024809273530819469)
          ·
            refine ⟨5022663384303477574057301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13393769024809273530819469 5022663384303477574057301)
            ·
              refine ⟨7357417066850797227623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5022663384303477574057301 7357417066850797227623)
              ·
                rfl

theorem cell22_580305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 11].length) (baseStart_580305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580305 prefixEnd_580305 := by exact prefixLift 580305
  have htrace : WordTrace (prefixWord ++ tailWord_580305) baseStart_580305 baseEnd_580305 := by
    simpa [prefixWord, tailWord_580305, baseEnd_580305] using wordTrace_append hprefix tailTrace_580305
  have hstable : (prefixWord ++ tailWord_580305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580305).length < 2 ^ (prefixWord ++ tailWord_580305).sum := by decide
  have hdescent : baseEnd_580305 < baseStart_580305 := by decide
  rcases family_descends (prefixWord ++ tailWord_580305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580367 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 5]
def baseStart_580367 : Nat := 118140960795 + 580367 * 2 ^ 59
def prefixEnd_580367 : Nat := 4983230072969 + 3 ^ 40 * 580367 * 2
def baseEnd_580367 : Nat := 66223828224008010031877

theorem tailTrace_580367 : CollatzResearch.WordTrace tailWord_580367 prefixEnd_580367 66223828224008010031877 := by
  unfold tailWord_580367
  simp only [CollatzResearch.WordTrace]
  refine ⟨21167723488436952637459355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14111815658957968424972903 21167723488436952637459355)
  ·
    refine ⟨31751585232655428956189033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21167723488436952637459355 31751585232655428956189033)
    ·
      refine ⟨23813688924491571717141775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31751585232655428956189033 23813688924491571717141775)
      ·
        refine ⟨35720533386737357575712663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23813688924491571717141775 35720533386737357575712663)
        ·
          refine ⟨53580800080106036363568995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35720533386737357575712663 53580800080106036363568995)
          ·
            refine ⟨80371200120159054545353493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53580800080106036363568995 80371200120159054545353493)
            ·
              refine ⟨3767400005632455681813445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80371200120159054545353493 3767400005632455681813445)
              ·
                refine ⟨706387501056085440340021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3767400005632455681813445 706387501056085440340021)
                ·
                  refine ⟨66223828224008010031877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 706387501056085440340021 66223828224008010031877)
                  ·
                    rfl

theorem cell22_580367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 5].length) (baseStart_580367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580367 prefixEnd_580367 := by exact prefixLift 580367
  have htrace : WordTrace (prefixWord ++ tailWord_580367) baseStart_580367 baseEnd_580367 := by
    simpa [prefixWord, tailWord_580367, baseEnd_580367] using wordTrace_append hprefix tailTrace_580367
  have hstable : (prefixWord ++ tailWord_580367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580367).length < 2 ^ (prefixWord ++ tailWord_580367).sum := by decide
  have hdescent : baseEnd_580367 < baseStart_580367 := by decide
  rcases family_descends (prefixWord ++ tailWord_580367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580384 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 5]
def baseStart_580384 : Nat := 118140960795 + 580384 * 2 ^ 59
def prefixEnd_580384 : Nat := 4983230072969 + 3 ^ 40 * 580384 * 2
def baseEnd_580384 : Nat := 66225768039813884140193

theorem tailTrace_580384 : CollatzResearch.WordTrace tailWord_580384 prefixEnd_580384 66225768039813884140193 := by
  unfold tailWord_580384
  simp only [CollatzResearch.WordTrace]
  refine ⟨10584171764687682270414103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14112229019583576360552137 10584171764687682270414103)
  ·
    refine ⟨15876257647031523405621155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10584171764687682270414103 15876257647031523405621155)
    ·
      refine ⟨23814386470547285108431733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15876257647031523405621155 23814386470547285108431733)
      ·
        refine ⟨2232598731613807978915475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23814386470547285108431733 2232598731613807978915475)
        ·
          refine ⟨3348898097420711968373213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232598731613807978915475 3348898097420711968373213)
          ·
            refine ⟨1255836786532766988139955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3348898097420711968373213 1255836786532766988139955)
            ·
              refine ⟨1883755179799150482209933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255836786532766988139955 1883755179799150482209933)
              ·
                refine ⟨706408192424681430828725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1883755179799150482209933 706408192424681430828725)
                ·
                  refine ⟨66225768039813884140193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 706408192424681430828725 66225768039813884140193)
                  ·
                    rfl

theorem cell22_580384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_580384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580384 prefixEnd_580384 := by exact prefixLift 580384
  have htrace : WordTrace (prefixWord ++ tailWord_580384) baseStart_580384 baseEnd_580384 := by
    simpa [prefixWord, tailWord_580384, baseEnd_580384] using wordTrace_append hprefix tailTrace_580384
  have hstable : (prefixWord ++ tailWord_580384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580384).length < 2 ^ (prefixWord ++ tailWord_580384).sum := by decide
  have hdescent : baseEnd_580384 < baseStart_580384 := by decide
  rcases family_descends (prefixWord ++ tailWord_580384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580422 : List Nat := [6, 1, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_580422 : Nat := 118140960795 + 580422 * 2 ^ 59
def prefixEnd_580422 : Nat := 4983230072969 + 3 ^ 40 * 580422 * 2
def baseEnd_580422 : Nat := 198690312296022219970463

theorem tailTrace_580422 : CollatzResearch.WordTrace tailWord_580422 prefixEnd_580422 198690312296022219970463 := by
  unfold tailWord_580422
  simp only [CollatzResearch.WordTrace]
  refine ⟨661554046976178032209735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14113153002158464687141013 661554046976178032209735)
  ·
    refine ⟨992331070464267048314603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 661554046976178032209735 992331070464267048314603)
    ·
      refine ⟨1488496605696400572471905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 992331070464267048314603 1488496605696400572471905)
      ·
        refine ⟨1116372454272300429353929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1488496605696400572471905 1116372454272300429353929)
        ·
          refine ⟨837279340704225322015447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1116372454272300429353929 837279340704225322015447)
          ·
            refine ⟨1255919011056337983023171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837279340704225322015447 1255919011056337983023171)
            ·
              refine ⟨1883878516584506974534757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255919011056337983023171 1883878516584506974534757)
              ·
                refine ⟨353227221859595057725267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1883878516584506974534757 353227221859595057725267)
                ·
                  refine ⟨529840832789392586587901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353227221859595057725267 529840832789392586587901)
                  ·
                    refine ⟨198690312296022219970463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 529840832789392586587901 198690312296022219970463)
                    ·
                      rfl

theorem cell22_580422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_580422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580422 prefixEnd_580422 := by exact prefixLift 580422
  have htrace : WordTrace (prefixWord ++ tailWord_580422) baseStart_580422 baseEnd_580422 := by
    simpa [prefixWord, tailWord_580422, baseEnd_580422] using wordTrace_append hprefix tailTrace_580422
  have hstable : (prefixWord ++ tailWord_580422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580422).length < 2 ^ (prefixWord ++ tailWord_580422).sum := by decide
  have hdescent : baseEnd_580422 < baseStart_580422 := by decide
  rcases family_descends (prefixWord ++ tailWord_580422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580459 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 2, 4]
def baseStart_580459 : Nat := 118140960795 + 580459 * 2 ^ 59
def prefixEnd_580459 : Nat := 4983230072969 + 3 ^ 40 * 580459 * 2
def baseEnd_580459 : Nat := 198702978152166456795349

theorem tailTrace_580459 : CollatzResearch.WordTrace tailWord_580459 prefixEnd_580459 198702978152166456795349 := by
  unfold tailWord_580459
  simp only [CollatzResearch.WordTrace]
  refine ⟨21171079004103652349808431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14114052669402434899872287 21171079004103652349808431)
  ·
    refine ⟨31756618506155478524712647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21171079004103652349808431 31756618506155478524712647)
    ·
      refine ⟨47634927759233217787068971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31756618506155478524712647 47634927759233217787068971)
      ·
        refine ⟨71452391638849826680603457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47634927759233217787068971 71452391638849826680603457)
        ·
          refine ⟨53589293729137370010452593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71452391638849826680603457 53589293729137370010452593)
          ·
            refine ⟨40191970296853027507839445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53589293729137370010452593 40191970296853027507839445)
            ·
              refine ⟨941999303832492832214987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 40191970296853027507839445 941999303832492832214987)
              ·
                refine ⟨1412998955748739248322481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941999303832492832214987 1412998955748739248322481)
                ·
                  refine ⟨1059749216811554436241861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1412998955748739248322481 1059749216811554436241861)
                  ·
                    refine ⟨198702978152166456795349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1059749216811554436241861 198702978152166456795349)
                    ·
                      rfl

theorem cell22_580459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 4].length) (baseStart_580459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580459 prefixEnd_580459 := by exact prefixLift 580459
  have htrace : WordTrace (prefixWord ++ tailWord_580459) baseStart_580459 baseEnd_580459 := by
    simpa [prefixWord, tailWord_580459, baseEnd_580459] using wordTrace_append hprefix tailTrace_580459
  have hstable : (prefixWord ++ tailWord_580459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580459).length < 2 ^ (prefixWord ++ tailWord_580459).sum := by decide
  have hdescent : baseEnd_580459 < baseStart_580459 := by decide
  rcases family_descends (prefixWord ++ tailWord_580459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580508 : List Nat := [2, 2, 3, 3, 2, 2, 2, 6]
def baseStart_580508 : Nat := 118140960795 + 580508 * 2 ^ 59
def prefixEnd_580508 : Nat := 4983230072969 + 3 ^ 40 * 580508 * 2
def baseEnd_580508 : Nat := 22079972428171851368911

theorem tailTrace_580508 : CollatzResearch.WordTrace tailWord_580508 prefixEnd_580508 22079972428171851368911 := by
  unfold tailWord_580508
  simp only [CollatzResearch.WordTrace]
  refine ⟨10586433090463066859171089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14115244120617422478894785 10586433090463066859171089)
  ·
    refine ⟨7939824817847300144378317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10586433090463066859171089 7939824817847300144378317)
    ·
      refine ⟨2977434306692737554141869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7939824817847300144378317 2977434306692737554141869)
      ·
        refine ⟨1116537865009776582803201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2977434306692737554141869 1116537865009776582803201)
        ·
          refine ⟨837403398757332437102401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1116537865009776582803201 837403398757332437102401)
          ·
            refine ⟨628052549067999327826801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837403398757332437102401 628052549067999327826801)
            ·
              refine ⟨471039411800999495870101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628052549067999327826801 471039411800999495870101)
              ·
                refine ⟨22079972428171851368911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 471039411800999495870101 22079972428171851368911)
                ·
                  rfl

theorem cell22_580508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 6].length) (baseStart_580508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580508 prefixEnd_580508 := by exact prefixLift 580508
  have htrace : WordTrace (prefixWord ++ tailWord_580508) baseStart_580508 baseEnd_580508 := by
    simpa [prefixWord, tailWord_580508, baseEnd_580508] using wordTrace_append hprefix tailTrace_580508
  have hstable : (prefixWord ++ tailWord_580508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580508).length < 2 ^ (prefixWord ++ tailWord_580508).sum := by decide
  have hdescent : baseEnd_580508 < baseStart_580508 := by decide
  rcases family_descends (prefixWord ++ tailWord_580508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580647 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 2, 3]
def baseStart_580647 : Nat := 118140960795 + 580647 * 2 ^ 59
def prefixEnd_580647 : Nat := 4983230072969 + 3 ^ 40 * 580647 * 2
def baseEnd_580647 : Nat := 198767334394196633094773

theorem tailTrace_580647 : CollatzResearch.WordTrace tailWord_580647 prefixEnd_580647 198767334394196633094773 := by
  unfold tailWord_580647
  simp only [CollatzResearch.WordTrace]
  refine ⟨21177935927422560457652195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14118623951615040305101463 21177935927422560457652195)
  ·
    refine ⟨31766903891133840686478293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21177935927422560457652195 31766903891133840686478293)
    ·
      refine ⟨744536809948449391089335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 31766903891133840686478293 744536809948449391089335)
      ·
        refine ⟨1116805214922674086634003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744536809948449391089335 1116805214922674086634003)
        ·
          refine ⟨1675207822384011129951005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116805214922674086634003 1675207822384011129951005)
          ·
            refine ⟨628202933394004173731627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1675207822384011129951005 628202933394004173731627)
            ·
              refine ⟨942304400091006260597441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628202933394004173731627 942304400091006260597441)
              ·
                refine ⟨706728300068254695448081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942304400091006260597441 706728300068254695448081)
                ·
                  refine ⟨530046225051191021586061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 706728300068254695448081 530046225051191021586061)
                  ·
                    refine ⟨198767334394196633094773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530046225051191021586061 198767334394196633094773)
                    ·
                      rfl

theorem cell22_580647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_580647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580647 prefixEnd_580647 := by exact prefixLift 580647
  have htrace : WordTrace (prefixWord ++ tailWord_580647) baseStart_580647 baseEnd_580647 := by
    simpa [prefixWord, tailWord_580647, baseEnd_580647] using wordTrace_append hprefix tailTrace_580647
  have hstable : (prefixWord ++ tailWord_580647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580647).length < 2 ^ (prefixWord ++ tailWord_580647).sum := by decide
  have hdescent : baseEnd_580647 < baseStart_580647 := by decide
  rcases family_descends (prefixWord ++ tailWord_580647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580658 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_580658 : Nat := 118140960795 + 580658 * 2 ^ 59
def prefixEnd_580658 : Nat := 4983230072969 + 3 ^ 40 * 580658 * 2
def baseEnd_580658 : Nat := 198771099918996271069739

theorem tailTrace_580658 : CollatzResearch.WordTrace tailWord_580658 prefixEnd_580658 198771099918996271069739 := by
  unfold tailWord_580658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5294584282595677334075657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14118891420255139557535085 5294584282595677334075657)
  ·
    refine ⟨3970938211946758000556743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5294584282595677334075657 3970938211946758000556743)
    ·
      refine ⟨5956407317920137000835115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3970938211946758000556743 5956407317920137000835115)
      ·
        refine ⟨8934610976880205501252673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5956407317920137000835115 8934610976880205501252673)
        ·
          refine ⟨6700958232660154125939505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8934610976880205501252673 6700958232660154125939505)
          ·
            refine ⟨5025718674495115594454629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6700958232660154125939505 5025718674495115594454629)
            ·
              refine ⟨942322251467834173960243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5025718674495115594454629 942322251467834173960243)
              ·
                refine ⟨1413483377201751260940365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942322251467834173960243 1413483377201751260940365)
                ·
                  refine ⟨530056266450656722852637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1413483377201751260940365 530056266450656722852637)
                  ·
                    refine ⟨198771099918996271069739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530056266450656722852637 198771099918996271069739)
                    ·
                      rfl

theorem cell22_580658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_580658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580658 prefixEnd_580658 := by exact prefixLift 580658
  have htrace : WordTrace (prefixWord ++ tailWord_580658) baseStart_580658 baseEnd_580658 := by
    simpa [prefixWord, tailWord_580658, baseEnd_580658] using wordTrace_append hprefix tailTrace_580658
  have hstable : (prefixWord ++ tailWord_580658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580658).length < 2 ^ (prefixWord ++ tailWord_580658).sum := by decide
  have hdescent : baseEnd_580658 < baseStart_580658 := by decide
  rcases family_descends (prefixWord ++ tailWord_580658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580765 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_580765 : Nat := 118140960795 + 580765 * 2 ^ 59
def prefixEnd_580765 : Nat := 4983230072969 + 3 ^ 40 * 580765 * 2
def baseEnd_580765 : Nat := 198807728205683658644411

theorem tailTrace_580765 : CollatzResearch.WordTrace tailWord_580765 prefixEnd_580765 198807728205683658644411 := by
  unfold tailWord_580765
  simp only [CollatzResearch.WordTrace]
  refine ⟨21182239740995066610447749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14121493160663377740298499 21182239740995066610447749)
  ·
    refine ⟨3971669951436574989458953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21182239740995066610447749 3971669951436574989458953)
    ·
      refine ⟨2978752463577431242094215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3971669951436574989458953 2978752463577431242094215)
      ·
        refine ⟨4468128695366146863141323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2978752463577431242094215 4468128695366146863141323)
        ·
          refine ⟨6702193043049220294711985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4468128695366146863141323 6702193043049220294711985)
          ·
            refine ⟨5026644782286915221033989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6702193043049220294711985 5026644782286915221033989)
            ·
              refine ⟨942495896678796603943873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5026644782286915221033989 942495896678796603943873)
              ·
                refine ⟨706871922509097452957905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942495896678796603943873 706871922509097452957905)
                ·
                  refine ⟨530153941881823089718429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 706871922509097452957905 530153941881823089718429)
                  ·
                    refine ⟨198807728205683658644411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530153941881823089718429 198807728205683658644411)
                    ·
                      rfl

theorem cell22_580765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_580765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580765 prefixEnd_580765 := by exact prefixLift 580765
  have htrace : WordTrace (prefixWord ++ tailWord_580765) baseStart_580765 baseEnd_580765 := by
    simpa [prefixWord, tailWord_580765, baseEnd_580765] using wordTrace_append hprefix tailTrace_580765
  have hstable : (prefixWord ++ tailWord_580765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580765).length < 2 ^ (prefixWord ++ tailWord_580765).sum := by decide
  have hdescent : baseEnd_580765 < baseStart_580765 := by decide
  rcases family_descends (prefixWord ++ tailWord_580765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580791 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 2, 6]
def baseStart_580791 : Nat := 118140960795 + 580791 * 2 ^ 59
def prefixEnd_580791 : Nat := 4983230072969 + 3 ^ 40 * 580791 * 2
def baseEnd_580791 : Nat := 198816628537028257494331

theorem tailTrace_580791 : CollatzResearch.WordTrace tailWord_580791 prefixEnd_580791 198816628537028257494331 := by
  unfold tailWord_580791
  simp only [CollatzResearch.WordTrace]
  refine ⟨21183188038900873050894227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14122125359267248700596151 21183188038900873050894227)
  ·
    refine ⟨31774782058351309576341341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21183188038900873050894227 31774782058351309576341341)
    ·
      refine ⟨11915543271881741091128003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31774782058351309576341341 11915543271881741091128003)
      ·
        refine ⟨17873314907822611636692005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11915543271881741091128003 17873314907822611636692005)
        ·
          refine ⟨3351246545216739681879751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17873314907822611636692005 3351246545216739681879751)
          ·
            refine ⟨5026869817825109522819627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351246545216739681879751 5026869817825109522819627)
            ·
              refine ⟨7540304726737664284229441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5026869817825109522819627 7540304726737664284229441)
              ·
                refine ⟨5655228545053248213172081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7540304726737664284229441 5655228545053248213172081)
                ·
                  refine ⟨4241421408789936159879061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5655228545053248213172081 4241421408789936159879061)
                  ·
                    refine ⟨198816628537028257494331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4241421408789936159879061 198816628537028257494331)
                    ·
                      rfl

theorem cell22_580791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_580791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580791 prefixEnd_580791 := by exact prefixLift 580791
  have htrace : WordTrace (prefixWord ++ tailWord_580791) baseStart_580791 baseEnd_580791 := by
    simpa [prefixWord, tailWord_580791, baseEnd_580791] using wordTrace_append hprefix tailTrace_580791
  have hstable : (prefixWord ++ tailWord_580791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580791).length < 2 ^ (prefixWord ++ tailWord_580791).sum := by decide
  have hdescent : baseEnd_580791 < baseStart_580791 := by decide
  rcases family_descends (prefixWord ++ tailWord_580791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580793 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 5, 3]
def baseStart_580793 : Nat := 118140960795 + 580793 * 2 ^ 59
def prefixEnd_580793 : Nat := 4983230072969 + 3 ^ 40 * 580793 * 2
def baseEnd_580793 : Nat := 198817313177900918944325

theorem tailTrace_580793 : CollatzResearch.WordTrace tailWord_580793 prefixEnd_580793 198817313177900918944325 := by
  unfold tailWord_580793
  simp only [CollatzResearch.WordTrace]
  refine ⟨21183260984893627392467033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14122173989929084928311355 21183260984893627392467033)
  ·
    refine ⟨15887445738670220544350275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21183260984893627392467033 15887445738670220544350275)
    ·
      refine ⟨23831168608005330816525413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15887445738670220544350275 23831168608005330816525413)
      ·
        refine ⟨4468344114000999528098515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23831168608005330816525413 4468344114000999528098515)
        ·
          refine ⟨6702516171001499292147773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4468344114000999528098515 6702516171001499292147773)
          ·
            refine ⟨2513443564125562234555415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6702516171001499292147773 2513443564125562234555415)
            ·
              refine ⟨3770165346188343351833123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2513443564125562234555415 3770165346188343351833123)
              ·
                refine ⟨5655248019282515027749685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3770165346188343351833123 5655248019282515027749685)
                ·
                  refine ⟨530179501807735783851533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5655248019282515027749685 530179501807735783851533)
                  ·
                    refine ⟨198817313177900918944325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530179501807735783851533 198817313177900918944325)
                    ·
                      rfl

theorem cell22_580793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 3].length) (baseStart_580793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580793 prefixEnd_580793 := by exact prefixLift 580793
  have htrace : WordTrace (prefixWord ++ tailWord_580793) baseStart_580793 baseEnd_580793 := by
    simpa [prefixWord, tailWord_580793, baseEnd_580793] using wordTrace_append hprefix tailTrace_580793
  have hstable : (prefixWord ++ tailWord_580793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580793).length < 2 ^ (prefixWord ++ tailWord_580793).sum := by decide
  have hdescent : baseEnd_580793 < baseStart_580793 := by decide
  rcases family_descends (prefixWord ++ tailWord_580793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580823 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 5]
def baseStart_580823 : Nat := 118140960795 + 580823 * 2 ^ 59
def prefixEnd_580823 : Nat := 4983230072969 + 3 ^ 40 * 580823 * 2
def baseEnd_580823 : Nat := 66275860930330280231411

theorem tailTrace_580823 : CollatzResearch.WordTrace tailWord_580823 prefixEnd_580823 66275860930330280231411 := by
  unfold tailWord_580823
  simp only [CollatzResearch.WordTrace]
  refine ⟨21184355174784942516059123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14122903449856628344039415 21184355174784942516059123)
  ·
    refine ⟨31776532762177413774088685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21184355174784942516059123 31776532762177413774088685)
    ·
      refine ⟨11916199785816530165283257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31776532762177413774088685 11916199785816530165283257)
      ·
        refine ⟨8937149839362397623962443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11916199785816530165283257 8937149839362397623962443)
        ·
          refine ⟨13405724759043596435943665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8937149839362397623962443 13405724759043596435943665)
          ·
            refine ⟨10054293569282697326957749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13405724759043596435943665 10054293569282697326957749)
            ·
              refine ⟨942590022120252874402289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10054293569282697326957749 942590022120252874402289)
              ·
                refine ⟨706942516590189655801717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942590022120252874402289 706942516590189655801717)
                ·
                  refine ⟨66275860930330280231411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 706942516590189655801717 66275860930330280231411)
                  ·
                    rfl

theorem cell22_580823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 5].length) (baseStart_580823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580823 prefixEnd_580823 := by exact prefixLift 580823
  have htrace : WordTrace (prefixWord ++ tailWord_580823) baseStart_580823 baseEnd_580823 := by
    simpa [prefixWord, tailWord_580823, baseEnd_580823] using wordTrace_append hprefix tailTrace_580823
  have hstable : (prefixWord ++ tailWord_580823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580823).length < 2 ^ (prefixWord ++ tailWord_580823).sum := by decide
  have hdescent : baseEnd_580823 < baseStart_580823 := by decide
  rcases family_descends (prefixWord ++ tailWord_580823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580840 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 5]
def baseStart_580840 : Nat := 118140960795 + 580840 * 2 ^ 59
def prefixEnd_580840 : Nat := 4983230072969 + 3 ^ 40 * 580840 * 2
def baseEnd_580840 : Nat := 66277800746136154339727

theorem tailTrace_580840 : CollatzResearch.WordTrace tailWord_580840 prefixEnd_580840 66277800746136154339727 := by
  unfold tailWord_580840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10592487607861677209713987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14123316810482236279618649 10592487607861677209713987)
  ·
    refine ⟨15888731411792515814570981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10592487607861677209713987 15888731411792515814570981)
    ·
      refine ⟨2979137139711096715232059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15888731411792515814570981 2979137139711096715232059)
      ·
        refine ⟨4468705709566645072848089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2979137139711096715232059 4468705709566645072848089)
        ·
          refine ⟨3351529282174983804636067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4468705709566645072848089 3351529282174983804636067)
          ·
            refine ⟨5027293923262475706954101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351529282174983804636067 5027293923262475706954101)
            ·
              refine ⟨471308805305857097526947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5027293923262475706954101 471308805305857097526947)
              ·
                refine ⟨706963207958785646290421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471308805305857097526947 706963207958785646290421)
                ·
                  refine ⟨66277800746136154339727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 706963207958785646290421 66277800746136154339727)
                  ·
                    rfl

theorem cell22_580840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 5].length) (baseStart_580840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580840 prefixEnd_580840 := by exact prefixLift 580840
  have htrace : WordTrace (prefixWord ++ tailWord_580840) baseStart_580840 baseEnd_580840 := by
    simpa [prefixWord, tailWord_580840, baseEnd_580840] using wordTrace_append hprefix tailTrace_580840
  have hstable : (prefixWord ++ tailWord_580840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580840).length < 2 ^ (prefixWord ++ tailWord_580840).sum := by decide
  have hdescent : baseEnd_580840 < baseStart_580840 := by decide
  rcases family_descends (prefixWord ++ tailWord_580840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580913 : List Nat := [1, 2, 2, 3, 3, 1, 2, 8]
def baseStart_580913 : Nat := 118140960795 + 580913 * 2 ^ 59
def prefixEnd_580913 : Nat := 4983230072969 + 3 ^ 40 * 580913 * 2
def baseEnd_580913 : Nat := 22095376847806733993773

theorem tailTrace_580913 : CollatzResearch.WordTrace tailWord_580913 prefixEnd_580913 22095376847806733993773 := by
  unfold tailWord_580913
  simp only [CollatzResearch.WordTrace]
  refine ⟨21187637744458887886835393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14125091829639258591223595 21187637744458887886835393)
  ·
    refine ⟨15890728308344165915126545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21187637744458887886835393 15890728308344165915126545)
    ·
      refine ⟨11918046231258124436344909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15890728308344165915126545 11918046231258124436344909)
      ·
        refine ⟨4469267336721796663629341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11918046231258124436344909 4469267336721796663629341)
        ·
          refine ⟨1675975251270673748861003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4469267336721796663629341 1675975251270673748861003)
          ·
            refine ⟨2513962876906010623291505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675975251270673748861003 2513962876906010623291505)
            ·
              refine ⟨1885472157679507967468629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2513962876906010623291505 1885472157679507967468629)
              ·
                refine ⟨22095376847806733993773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1885472157679507967468629 22095376847806733993773)
                ·
                  rfl

theorem cell22_580913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 8].length) (baseStart_580913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580913 prefixEnd_580913 := by exact prefixLift 580913
  have htrace : WordTrace (prefixWord ++ tailWord_580913) baseStart_580913 baseEnd_580913 := by
    simpa [prefixWord, tailWord_580913, baseEnd_580913] using wordTrace_append hprefix tailTrace_580913
  have hstable : (prefixWord ++ tailWord_580913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580913).length < 2 ^ (prefixWord ++ tailWord_580913).sum := by decide
  have hdescent : baseEnd_580913 < baseStart_580913 := by decide
  rcases family_descends (prefixWord ++ tailWord_580913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580915 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 2, 4]
def baseStart_580915 : Nat := 118140960795 + 580915 * 2 ^ 59
def prefixEnd_580915 : Nat := 4983230072969 + 3 ^ 40 * 580915 * 2
def baseEnd_580915 : Nat := 198859076271133267393951

theorem tailTrace_580915 : CollatzResearch.WordTrace tailWord_580915 prefixEnd_580915 198859076271133267393951 := by
  unfold tailWord_580915
  simp only [CollatzResearch.WordTrace]
  refine ⟨21187710690451642228408199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14125140460301094818938799 21187710690451642228408199)
  ·
    refine ⟨31781566035677463342612299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21187710690451642228408199 31781566035677463342612299)
    ·
      refine ⟨47672349053516195013918449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31781566035677463342612299 47672349053516195013918449)
      ·
        refine ⟨35754261790137146260438837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47672349053516195013918449 35754261790137146260438837)
        ·
          refine ⟨3351962042825357461916141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35754261790137146260438837 3351962042825357461916141)
          ·
            refine ⟨1256985766059509048218553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3351962042825357461916141 1256985766059509048218553)
            ·
              refine ⟨942739324544631786163915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256985766059509048218553 942739324544631786163915)
              ·
                refine ⟨1414108986816947679245873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942739324544631786163915 1414108986816947679245873)
                ·
                  refine ⟨1060581740112710759434405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414108986816947679245873 1060581740112710759434405)
                  ·
                    refine ⟨198859076271133267393951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1060581740112710759434405 198859076271133267393951)
                    ·
                      rfl

theorem cell22_580915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 4].length) (baseStart_580915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580915 prefixEnd_580915 := by exact prefixLift 580915
  have htrace : WordTrace (prefixWord ++ tailWord_580915) baseStart_580915 baseEnd_580915 := by
    simpa [prefixWord, tailWord_580915, baseEnd_580915] using wordTrace_append hprefix tailTrace_580915
  have hstable : (prefixWord ++ tailWord_580915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580915).length < 2 ^ (prefixWord ++ tailWord_580915).sum := by decide
  have hdescent : baseEnd_580915 < baseStart_580915 := by decide
  rcases family_descends (prefixWord ++ tailWord_580915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580932 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_580932 : Nat := 118140960795 + 580932 * 2 ^ 59
def prefixEnd_580932 : Nat := 4983230072969 + 3 ^ 40 * 580932 * 2
def baseEnd_580932 : Nat := 198864895718550889718899

theorem tailTrace_580932 : CollatzResearch.WordTrace tailWord_580932 prefixEnd_580932 198864895718550889718899 := by
  unfold tailWord_580932
  simp only [CollatzResearch.WordTrace]
  refine ⟨10594165365695027065888525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14125553820926702754518033 10594165365695027065888525)
  ·
    refine ⟨3972812012135635149708197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10594165365695027065888525 3972812012135635149708197)
    ·
      refine ⟨744902252275431590570287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3972812012135635149708197 744902252275431590570287)
      ·
        refine ⟨1117353378413147385855431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744902252275431590570287 1117353378413147385855431)
        ·
          refine ⟨1676030067619721078783147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117353378413147385855431 1676030067619721078783147)
          ·
            refine ⟨2514045101429581618174721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676030067619721078783147 2514045101429581618174721)
            ·
              refine ⟨1885533826072186213631041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2514045101429581618174721 1885533826072186213631041)
              ·
                refine ⟨1414150369554139660223281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1885533826072186213631041 1414150369554139660223281)
                ·
                  refine ⟨1060612777165604745167461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414150369554139660223281 1060612777165604745167461)
                  ·
                    refine ⟨198864895718550889718899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1060612777165604745167461 198864895718550889718899)
                    ·
                      rfl

theorem cell22_580932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_580932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580932 prefixEnd_580932 := by exact prefixLift 580932
  have htrace : WordTrace (prefixWord ++ tailWord_580932) baseStart_580932 baseEnd_580932 := by
    simpa [prefixWord, tailWord_580932, baseEnd_580932] using wordTrace_append hprefix tailTrace_580932
  have hstable : (prefixWord ++ tailWord_580932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580932).length < 2 ^ (prefixWord ++ tailWord_580932).sum := by decide
  have hdescent : baseEnd_580932 < baseStart_580932 := by decide
  rcases family_descends (prefixWord ++ tailWord_580932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580945 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 3, 3]
def baseStart_580945 : Nat := 118140960795 + 580945 * 2 ^ 59
def prefixEnd_580945 : Nat := 4983230072969 + 3 ^ 40 * 580945 * 2
def baseEnd_580945 : Nat := 198869345884223189143859

theorem tailTrace_580945 : CollatzResearch.WordTrace tailWord_580945 prefixEnd_580945 198869345884223189143859 := by
  unfold tailWord_580945
  simp only [CollatzResearch.WordTrace]
  refine ⟨21188804880342957352000289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14125869920228638234666859 21188804880342957352000289)
  ·
    refine ⟨15891603660257218014000217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21188804880342957352000289 15891603660257218014000217)
    ·
      refine ⟨11918702745192913510500163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15891603660257218014000217 11918702745192913510500163)
      ·
        refine ⟨17878054117789370265750245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11918702745192913510500163 17878054117789370265750245)
        ·
          refine ⟨3352135147085506924828171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17878054117789370265750245 3352135147085506924828171)
          ·
            refine ⟨5028202720628260387242257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352135147085506924828171 5028202720628260387242257)
            ·
              refine ⟨3771152040471195290431693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5028202720628260387242257 3771152040471195290431693)
              ·
                refine ⟨1414182015176698233911885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3771152040471195290431693 1414182015176698233911885)
                ·
                  refine ⟨530318255691261837716957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1414182015176698233911885 530318255691261837716957)
                  ·
                    refine ⟨198869345884223189143859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530318255691261837716957 198869345884223189143859)
                    ·
                      rfl

theorem cell22_580945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_580945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580945 prefixEnd_580945 := by exact prefixLift 580945
  have htrace : WordTrace (prefixWord ++ tailWord_580945) baseStart_580945 baseEnd_580945 := by
    simpa [prefixWord, tailWord_580945, baseEnd_580945] using wordTrace_append hprefix tailTrace_580945
  have hstable : (prefixWord ++ tailWord_580945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580945).length < 2 ^ (prefixWord ++ tailWord_580945).sum := by decide
  have hdescent : baseEnd_580945 < baseStart_580945 := by decide
  rcases family_descends (prefixWord ++ tailWord_580945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580962 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_580962 : Nat := 118140960795 + 580962 * 2 ^ 59
def prefixEnd_580962 : Nat := 4983230072969 + 3 ^ 40 * 580962 * 2
def baseEnd_580962 : Nat := 198875165331640811468807

theorem tailTrace_580962 : CollatzResearch.WordTrace tailWord_580962 prefixEnd_580962 198875165331640811468807 := by
  unfold tailWord_580962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5297356230320342313842285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14126283280854246170246093 5297356230320342313842285)
  ·
    refine ⟨1986508586370128367690857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5297356230320342313842285 1986508586370128367690857)
    ·
      refine ⟨1489881439777596275768143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1986508586370128367690857 1489881439777596275768143)
      ·
        refine ⟨2234822159666394413652215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1489881439777596275768143 2234822159666394413652215)
        ·
          refine ⟨3352233239499591620478323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234822159666394413652215 3352233239499591620478323)
          ·
            refine ⟨5028349859249387430717485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352233239499591620478323 5028349859249387430717485)
            ·
              refine ⟨1885631197218520286519057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5028349859249387430717485 1885631197218520286519057)
              ·
                refine ⟨1414223397913890214889293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1885631197218520286519057 1414223397913890214889293)
                ·
                  refine ⟨530333774217708830583485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1414223397913890214889293 530333774217708830583485)
                  ·
                    refine ⟨198875165331640811468807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530333774217708830583485 198875165331640811468807)
                    ·
                      rfl

theorem cell22_580962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_580962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_580962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_580962 prefixEnd_580962 := by exact prefixLift 580962
  have htrace : WordTrace (prefixWord ++ tailWord_580962) baseStart_580962 baseEnd_580962 := by
    simpa [prefixWord, tailWord_580962, baseEnd_580962] using wordTrace_append hprefix tailTrace_580962
  have hstable : (prefixWord ++ tailWord_580962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580962).length < 2 ^ (prefixWord ++ tailWord_580962).sum := by decide
  have hdescent : baseEnd_580962 < baseStart_580962 := by decide
  rcases family_descends (prefixWord ++ tailWord_580962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581048 : List Nat := [2, 1, 2, 1, 2, 2, 12]
def baseStart_581048 : Nat := 118140960795 + 581048 * 2 ^ 59
def prefixEnd_581048 : Nat := 4983230072969 + 3 ^ 40 * 581048 * 2
def baseEnd_581048 : Nat := 7366837218117231622909

theorem tailTrace_581048 : CollatzResearch.WordTrace tailWord_581048 prefixEnd_581048 7366837218117231622909 := by
  unfold tailWord_581048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10596280799484902971499899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14128374399313203961999865 10596280799484902971499899)
  ·
    refine ⟨15894421199227354457249849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10596280799484902971499899 15894421199227354457249849)
    ·
      refine ⟨11920815899420515842937387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15894421199227354457249849 11920815899420515842937387)
      ·
        refine ⟨17881223849130773764406081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11920815899420515842937387 17881223849130773764406081)
        ·
          refine ⟨13410917886848080323304561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17881223849130773764406081 13410917886848080323304561)
          ·
            refine ⟨10058188415136060242478421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13410917886848080323304561 10058188415136060242478421)
            ·
              refine ⟨7366837218117231622909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 10058188415136060242478421 7366837218117231622909)
              ·
                rfl

theorem cell22_581048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 12].length) (baseStart_581048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581048 prefixEnd_581048 := by exact prefixLift 581048
  have htrace : WordTrace (prefixWord ++ tailWord_581048) baseStart_581048 baseEnd_581048 := by
    simpa [prefixWord, tailWord_581048, baseEnd_581048] using wordTrace_append hprefix tailTrace_581048
  have hstable : (prefixWord ++ tailWord_581048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581048).length < 2 ^ (prefixWord ++ tailWord_581048).sum := by decide
  have hdescent : baseEnd_581048 < baseStart_581048 := by decide
  rcases family_descends (prefixWord ++ tailWord_581048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581114 : List Nat := [3, 1, 1, 1, 1, 2, 5, 4, 1, 3]
def baseStart_581114 : Nat := 118140960795 + 581114 * 2 ^ 59
def prefixEnd_581114 : Nat := 4983230072969 + 3 ^ 40 * 581114 * 2
def baseEnd_581114 : Nat := 198927198037963081668341

theorem tailTrace_581114 : CollatzResearch.WordTrace tailWord_581114 prefixEnd_581114 198927198037963081668341 := by
  unfold tailWord_581114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298742204182674803725599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14129979211153799476601597 5298742204182674803725599)
  ·
    refine ⟨7948113306274012205588399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5298742204182674803725599 7948113306274012205588399)
    ·
      refine ⟨11922169959411018308382599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7948113306274012205588399 11922169959411018308382599)
      ·
        refine ⟨17883254939116527462573899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11922169959411018308382599 17883254939116527462573899)
        ·
          refine ⟨26824882408674791193860849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17883254939116527462573899 26824882408674791193860849)
          ·
            refine ⟨20118661806506093395395637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26824882408674791193860849 20118661806506093395395637)
            ·
              refine ⟨1886124544359946255818341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20118661806506093395395637 1886124544359946255818341)
              ·
                refine ⟨353648352067489922965939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1886124544359946255818341 353648352067489922965939)
                ·
                  refine ⟨530472528101234884448909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353648352067489922965939 530472528101234884448909)
                  ·
                    refine ⟨198927198037963081668341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530472528101234884448909 198927198037963081668341)
                    ·
                      rfl

theorem cell22_581114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_581114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581114 prefixEnd_581114 := by exact prefixLift 581114
  have htrace : WordTrace (prefixWord ++ tailWord_581114) baseStart_581114 baseEnd_581114 := by
    simpa [prefixWord, tailWord_581114, baseEnd_581114] using wordTrace_append hprefix tailTrace_581114
  have hstable : (prefixWord ++ tailWord_581114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581114).length < 2 ^ (prefixWord ++ tailWord_581114).sum := by decide
  have hdescent : baseEnd_581114 < baseStart_581114 := by decide
  rcases family_descends (prefixWord ++ tailWord_581114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581127 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 5]
def baseStart_581127 : Nat := 118140960795 + 581127 * 2 ^ 59
def prefixEnd_581127 : Nat := 4983230072969 + 3 ^ 40 * 581127 * 2
def baseEnd_581127 : Nat := 66310549401211793697767

theorem tailTrace_581127 : CollatzResearch.WordTrace tailWord_581127 prefixEnd_581127 66310549401211793697767 := by
  unfold tailWord_581127
  simp only [CollatzResearch.WordTrace]
  refine ⟨21195442965683602435125635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14130295310455734956750423 21195442965683602435125635)
  ·
    refine ⟨31793164448525403652688453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21195442965683602435125635 31793164448525403652688453)
    ·
      refine ⟨5961218334098513184879085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31793164448525403652688453 5961218334098513184879085)
      ·
        refine ⟨2235456875286942444329657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5961218334098513184879085 2235456875286942444329657)
        ·
          refine ⟨1676592656465206833247243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2235456875286942444329657 1676592656465206833247243)
          ·
            refine ⟨2514888984697810249870865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676592656465206833247243 2514888984697810249870865)
            ·
              refine ⟨1886166738523357687403149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2514888984697810249870865 1886166738523357687403149)
              ·
                refine ⟨707312526946259132776181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1886166738523357687403149 707312526946259132776181)
                ·
                  refine ⟨66310549401211793697767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 707312526946259132776181 66310549401211793697767)
                  ·
                    rfl

theorem cell22_581127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 5].length) (baseStart_581127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581127 prefixEnd_581127 := by exact prefixLift 581127
  have htrace : WordTrace (prefixWord ++ tailWord_581127) baseStart_581127 baseEnd_581127 := by
    simpa [prefixWord, tailWord_581127, baseEnd_581127] using wordTrace_append hprefix tailTrace_581127
  have hstable : (prefixWord ++ tailWord_581127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581127).length < 2 ^ (prefixWord ++ tailWord_581127).sum := by decide
  have hdescent : baseEnd_581127 < baseStart_581127 := by decide
  rcases family_descends (prefixWord ++ tailWord_581127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581200 : List Nat := [2, 1, 1, 1, 1, 3, 5, 8]
def baseStart_581200 : Nat := 118140960795 + 581200 * 2 ^ 59
def prefixEnd_581200 : Nat := 4983230072969 + 3 ^ 40 * 581200 * 2
def baseEnd_581200 : Nat := 22106293066165280446453

theorem tailTrace_581200 : CollatzResearch.WordTrace tailWord_581200 prefixEnd_581200 22106293066165280446453 := by
  unfold tailWord_581200
  simp only [CollatzResearch.WordTrace]
  refine ⟨10599052747209567951266527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14132070329612757268355369 10599052747209567951266527)
  ·
    refine ⟨15898579120814351926899791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10599052747209567951266527 15898579120814351926899791)
    ·
      refine ⟨23847868681221527890349687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15898579120814351926899791 23847868681221527890349687)
      ·
        refine ⟨35771803021832291835524531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23847868681221527890349687 35771803021832291835524531)
        ·
          refine ⟨53657704532748437753286797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35771803021832291835524531 53657704532748437753286797)
          ·
            refine ⟨20121639199780664157482549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53657704532748437753286797 20121639199780664157482549)
            ·
              refine ⟨1886403674979437264763989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20121639199780664157482549 1886403674979437264763989)
              ·
                refine ⟨22106293066165280446453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1886403674979437264763989 22106293066165280446453)
                ·
                  rfl

theorem cell22_581200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 8].length) (baseStart_581200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581200 prefixEnd_581200 := by exact prefixLift 581200
  have htrace : WordTrace (prefixWord ++ tailWord_581200) baseStart_581200 baseEnd_581200 := by
    simpa [prefixWord, tailWord_581200, baseEnd_581200] using wordTrace_append hprefix tailTrace_581200
  have hstable : (prefixWord ++ tailWord_581200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581200).length < 2 ^ (prefixWord ++ tailWord_581200).sum := by decide
  have hdescent : baseEnd_581200 < baseStart_581200 := by decide
  rcases family_descends (prefixWord ++ tailWord_581200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581202 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_581202 : Nat := 118140960795 + 581202 * 2 ^ 59
def prefixEnd_581202 : Nat := 4983230072969 + 3 ^ 40 * 581202 * 2
def baseEnd_581202 : Nat := 198957322236360185468071

theorem tailTrace_581202 : CollatzResearch.WordTrace tailWord_581202 prefixEnd_581202 198957322236360185468071 := by
  unfold tailWord_581202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299544610102972561026465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14132118960274593496070573 5299544610102972561026465)
  ·
    refine ⟨3974658457577229420769849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5299544610102972561026465 3974658457577229420769849)
    ·
      refine ⟨2980993843182922065577387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3974658457577229420769849 2980993843182922065577387)
      ·
        refine ⟨4471490764774383098366081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2980993843182922065577387 4471490764774383098366081)
        ·
          refine ⟨3353618073580787323774561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4471490764774383098366081 3353618073580787323774561)
          ·
            refine ⟨2515213555185590492830921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3353618073580787323774561 2515213555185590492830921)
            ·
              refine ⟨1886410166389192869623191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2515213555185590492830921 1886410166389192869623191)
              ·
                refine ⟨2829615249583789304434787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886410166389192869623191 2829615249583789304434787)
                ·
                  refine ⟨4244422874375683956652181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829615249583789304434787 4244422874375683956652181)
                  ·
                    refine ⟨198957322236360185468071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4244422874375683956652181 198957322236360185468071)
                    ·
                      rfl

theorem cell22_581202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_581202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581202 prefixEnd_581202 := by exact prefixLift 581202
  have htrace : WordTrace (prefixWord ++ tailWord_581202) baseStart_581202 baseEnd_581202 := by
    simpa [prefixWord, tailWord_581202, baseEnd_581202] using wordTrace_append hprefix tailTrace_581202
  have hstable : (prefixWord ++ tailWord_581202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581202).length < 2 ^ (prefixWord ++ tailWord_581202).sum := by decide
  have hdescent : baseEnd_581202 < baseStart_581202 := by decide
  rcases family_descends (prefixWord ++ tailWord_581202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581238 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_581238 : Nat := 118140960795 + 581238 * 2 ^ 59
def prefixEnd_581238 : Nat := 4983230072969 + 3 ^ 40 * 581238 * 2
def baseEnd_581238 : Nat := 198969645772068091567961

theorem tailTrace_581238 : CollatzResearch.WordTrace tailWord_581238 prefixEnd_581238 198969645772068091567961 := by
  unfold tailWord_581238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1324968216767591774526023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14132994312187645594944245 1324968216767591774526023)
  ·
    refine ⟨1987452325151387661789035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1324968216767591774526023 1987452325151387661789035)
    ·
      refine ⟨2981178487727081492683553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1987452325151387661789035 2981178487727081492683553)
      ·
        refine ⟨2235883865795311119512665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2981178487727081492683553 2235883865795311119512665)
        ·
          refine ⟨1676912899346483339634499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2235883865795311119512665 1676912899346483339634499)
          ·
            refine ⟨2515369349019725009451749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676912899346483339634499 2515369349019725009451749)
            ·
              refine ⟨471631752941198439272203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2515369349019725009451749 471631752941198439272203)
              ·
                refine ⟨707447629411797658908305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471631752941198439272203 707447629411797658908305)
                ·
                  refine ⟨530585722058848244181229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707447629411797658908305 530585722058848244181229)
                  ·
                    refine ⟨198969645772068091567961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530585722058848244181229 198969645772068091567961)
                    ·
                      rfl

theorem cell22_581238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_581238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581238 prefixEnd_581238 := by exact prefixLift 581238
  have htrace : WordTrace (prefixWord ++ tailWord_581238) baseStart_581238 baseEnd_581238 := by
    simpa [prefixWord, tailWord_581238, baseEnd_581238] using wordTrace_append hprefix tailTrace_581238
  have hstable : (prefixWord ++ tailWord_581238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581238).length < 2 ^ (prefixWord ++ tailWord_581238).sum := by decide
  have hdescent : baseEnd_581238 < baseStart_581238 := by decide
  rcases family_descends (prefixWord ++ tailWord_581238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581277 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_581277 : Nat := 118140960795 + 581277 * 2 ^ 59
def prefixEnd_581277 : Nat := 4983230072969 + 3 ^ 40 * 581277 * 2
def baseEnd_581277 : Nat := 198982996269084989842841

theorem tailTrace_581277 : CollatzResearch.WordTrace tailWord_581277 prefixEnd_581277 198982996269084989842841 := by
  unfold tailWord_581277
  simp only [CollatzResearch.WordTrace]
  refine ⟨21200913915140178053086085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14133942610093452035390723 21200913915140178053086085)
  ·
    refine ⟨3975171359088783384953641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21200913915140178053086085 3975171359088783384953641)
    ·
      refine ⟨2981378519316587538715231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3975171359088783384953641 2981378519316587538715231)
      ·
        refine ⟨4472067778974881308072847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2981378519316587538715231 4472067778974881308072847)
        ·
          refine ⟨6708101668462321962109271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472067778974881308072847 6708101668462321962109271)
          ·
            refine ⟨10062152502693482943163907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6708101668462321962109271 10062152502693482943163907)
            ·
              refine ⟨15093228754040224414745861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10062152502693482943163907 15093228754040224414745861)
              ·
                refine ⟨2829980391382542077764849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15093228754040224414745861 2829980391382542077764849)
                ·
                  refine ⟨2122485293536906558323637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2829980391382542077764849 2122485293536906558323637)
                  ·
                    refine ⟨198982996269084989842841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2122485293536906558323637 198982996269084989842841)
                    ·
                      rfl

theorem cell22_581277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_581277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581277 prefixEnd_581277 := by exact prefixLift 581277
  have htrace : WordTrace (prefixWord ++ tailWord_581277) baseStart_581277 baseEnd_581277 := by
    simpa [prefixWord, tailWord_581277, baseEnd_581277] using wordTrace_append hprefix tailTrace_581277
  have hstable : (prefixWord ++ tailWord_581277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581277).length < 2 ^ (prefixWord ++ tailWord_581277).sum := by decide
  have hdescent : baseEnd_581277 < baseStart_581277 := by decide
  rcases family_descends (prefixWord ++ tailWord_581277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581309 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_581309 : Nat := 118140960795 + 581309 * 2 ^ 59
def prefixEnd_581309 : Nat := 4983230072969 + 3 ^ 40 * 581309 * 2
def baseEnd_581309 : Nat := 198993950523047573042743

theorem tailTrace_581309 : CollatzResearch.WordTrace tailWord_581309 prefixEnd_581309 198993950523047573042743 := by
  unfold tailWord_581309
  simp only [CollatzResearch.WordTrace]
  refine ⟨21202081051024247518250981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14134720700682831678833987 21202081051024247518250981)
  ·
    refine ⟨3975390197067046409672059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21202081051024247518250981 3975390197067046409672059)
    ·
      refine ⟨5963085295600569614508089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975390197067046409672059 5963085295600569614508089)
      ·
        refine ⟨4472313971700427210881067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5963085295600569614508089 4472313971700427210881067)
        ·
          refine ⟨6708470957550640816321601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472313971700427210881067 6708470957550640816321601)
          ·
            refine ⟨5031353218162980612241201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6708470957550640816321601 5031353218162980612241201)
            ·
              refine ⟨3773514913622235459180901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5031353218162980612241201 3773514913622235459180901)
              ·
                refine ⟨707534046304169148596419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3773514913622235459180901 707534046304169148596419)
                ·
                  refine ⟨1061301069456253722894629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707534046304169148596419 1061301069456253722894629)
                  ·
                    refine ⟨198993950523047573042743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1061301069456253722894629 198993950523047573042743)
                    ·
                      rfl

theorem cell22_581309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_581309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581309 prefixEnd_581309 := by exact prefixLift 581309
  have htrace : WordTrace (prefixWord ++ tailWord_581309) baseStart_581309 baseEnd_581309 := by
    simpa [prefixWord, tailWord_581309, baseEnd_581309] using wordTrace_append hprefix tailTrace_581309
  have hstable : (prefixWord ++ tailWord_581309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581309).length < 2 ^ (prefixWord ++ tailWord_581309).sum := by decide
  have hdescent : baseEnd_581309 < baseStart_581309 := by decide
  rcases family_descends (prefixWord ++ tailWord_581309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581452 : List Nat := [2, 2, 1, 3, 4, 2, 2, 2, 1, 3]
def baseStart_581452 : Nat := 118140960795 + 581452 * 2 ^ 59
def prefixEnd_581452 : Nat := 4983230072969 + 3 ^ 40 * 581452 * 2
def baseEnd_581452 : Nat := 199042902345442866717305

theorem tailTrace_581452 : CollatzResearch.WordTrace tailWord_581452 prefixEnd_581452 199042902345442866717305 := by
  unfold tailWord_581452
  simp only [CollatzResearch.WordTrace]
  refine ⟨10603648344753091470353305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14138197793004121960471073 10603648344753091470353305)
  ·
    refine ⟨7952736258564818602764979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10603648344753091470353305 7952736258564818602764979)
    ·
      refine ⟨11929104387847227904147469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7952736258564818602764979 11929104387847227904147469)
      ·
        refine ⟨4473414145442710464055301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11929104387847227904147469 4473414145442710464055301)
        ·
          refine ⟨838765152270508212010369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4473414145442710464055301 838765152270508212010369)
          ·
            refine ⟨629073864202881159007777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 838765152270508212010369 629073864202881159007777)
            ·
              refine ⟨471805398152160869255833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 629073864202881159007777 471805398152160869255833)
              ·
                refine ⟨353854048614120651941875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471805398152160869255833 353854048614120651941875)
                ·
                  refine ⟨530781072921180977912813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353854048614120651941875 530781072921180977912813)
                  ·
                    refine ⟨199042902345442866717305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530781072921180977912813 199042902345442866717305)
                    ·
                      rfl

theorem cell22_581452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_581452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581452 prefixEnd_581452 := by exact prefixLift 581452
  have htrace : WordTrace (prefixWord ++ tailWord_581452) baseStart_581452 baseEnd_581452 := by
    simpa [prefixWord, tailWord_581452, baseEnd_581452] using wordTrace_append hprefix tailTrace_581452
  have hstable : (prefixWord ++ tailWord_581452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581452).length < 2 ^ (prefixWord ++ tailWord_581452).sum := by decide
  have hdescent : baseEnd_581452 < baseStart_581452 := by decide
  rcases family_descends (prefixWord ++ tailWord_581452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581476 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 6]
def baseStart_581476 : Nat := 118140960795 + 581476 * 2 ^ 59
def prefixEnd_581476 : Nat := 4983230072969 + 3 ^ 40 * 581476 * 2
def baseEnd_581476 : Nat := 66350372678638268039077

theorem tailTrace_581476 : CollatzResearch.WordTrace tailWord_581476 prefixEnd_581476 66350372678638268039077 := by
  unfold tailWord_581476
  simp only [CollatzResearch.WordTrace]
  refine ⟨10604086020709617519790141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14138781360946156693053521 10604086020709617519790141)
  ·
    refine ⟨3976532257766106569921303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10604086020709617519790141 3976532257766106569921303)
    ·
      refine ⟨5964798386649159854881955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3976532257766106569921303 5964798386649159854881955)
      ·
        refine ⟨8947197579973739782322933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5964798386649159854881955 8947197579973739782322933)
        ·
          refine ⟨838799773122538104592775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8947197579973739782322933 838799773122538104592775)
          ·
            refine ⟨1258199659683807156889163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838799773122538104592775 1258199659683807156889163)
            ·
              refine ⟨1887299489525710735333745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258199659683807156889163 1887299489525710735333745)
              ·
                refine ⟨1415474617144283051500309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1887299489525710735333745 1415474617144283051500309)
                ·
                  refine ⟨66350372678638268039077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1415474617144283051500309 66350372678638268039077)
                  ·
                    rfl

theorem cell22_581476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_581476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581476 prefixEnd_581476 := by exact prefixLift 581476
  have htrace : WordTrace (prefixWord ++ tailWord_581476) baseStart_581476 baseEnd_581476 := by
    simpa [prefixWord, tailWord_581476, baseEnd_581476] using wordTrace_append hprefix tailTrace_581476
  have hstable : (prefixWord ++ tailWord_581476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581476).length < 2 ^ (prefixWord ++ tailWord_581476).sum := by decide
  have hdescent : baseEnd_581476 < baseStart_581476 := by decide
  rcases family_descends (prefixWord ++ tailWord_581476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581489 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_581489 : Nat := 118140960795 + 581489 * 2 ^ 59
def prefixEnd_581489 : Nat := 4983230072969 + 3 ^ 40 * 581489 * 2
def baseEnd_581489 : Nat := 199055568201587103542191

theorem tailTrace_581489 : CollatzResearch.WordTrace tailWord_581489 prefixEnd_581489 199055568201587103542191 := by
  unfold tailWord_581489
  simp only [CollatzResearch.WordTrace]
  refine ⟨21208646190372138259803521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14139097460248092173202347 21208646190372138259803521)
  ·
    refine ⟨15906484642779103694852641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21208646190372138259803521 15906484642779103694852641)
    ·
      refine ⟨11929863482084327771139481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15906484642779103694852641 11929863482084327771139481)
      ·
        refine ⟨8947397611563245828354611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11929863482084327771139481 8947397611563245828354611)
        ·
          refine ⟨13421096417344868742531917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8947397611563245828354611 13421096417344868742531917)
          ·
            refine ⟨5032911156504325778449469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13421096417344868742531917 5032911156504325778449469)
            ·
              refine ⟨1887341683689122166918551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5032911156504325778449469 1887341683689122166918551)
              ·
                refine ⟨2831012525533683250377827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887341683689122166918551 2831012525533683250377827)
                ·
                  refine ⟨4246518788300524875566741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831012525533683250377827 4246518788300524875566741)
                  ·
                    refine ⟨199055568201587103542191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4246518788300524875566741 199055568201587103542191)
                    ·
                      rfl

theorem cell22_581489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_581489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581489 prefixEnd_581489 := by exact prefixLift 581489
  have htrace : WordTrace (prefixWord ++ tailWord_581489) baseStart_581489 baseEnd_581489 := by
    simpa [prefixWord, tailWord_581489, baseEnd_581489] using wordTrace_append hprefix tailTrace_581489
  have hstable : (prefixWord ++ tailWord_581489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581489).length < 2 ^ (prefixWord ++ tailWord_581489).sum := by decide
  have hdescent : baseEnd_581489 < baseStart_581489 := by decide
  rcases family_descends (prefixWord ++ tailWord_581489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581493 : List Nat := [1, 3, 4, 1, 1, 1, 4, 3, 4]
def baseStart_581493 : Nat := 118140960795 + 581493 * 2 ^ 59
def prefixEnd_581493 : Nat := 4983230072969 + 3 ^ 40 * 581493 * 2
def baseEnd_581493 : Nat := 66352312494444142147393

theorem tailTrace_581493 : CollatzResearch.WordTrace tailWord_581493 prefixEnd_581493 66352312494444142147393 := by
  unfold tailWord_581493
  simp only [CollatzResearch.WordTrace]
  refine ⟨21208792082357646942949133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14139194721571764628632755 21208792082357646942949133)
  ·
    refine ⟨7953297030884117603605925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21208792082357646942949133 7953297030884117603605925)
    ·
      refine ⟨1491243193290772050676111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7953297030884117603605925 1491243193290772050676111)
      ·
        refine ⟨2236864789936158076014167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491243193290772050676111 2236864789936158076014167)
        ·
          refine ⟨3355297184904237114021251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2236864789936158076014167 3355297184904237114021251)
          ·
            refine ⟨5032945777356355671031877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3355297184904237114021251 5032945777356355671031877)
            ·
              refine ⟨943677333254316688318477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5032945777356355671031877 943677333254316688318477)
              ·
                refine ⟨353878999970368758119429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 943677333254316688318477 353878999970368758119429)
                ·
                  refine ⟨66352312494444142147393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 353878999970368758119429 66352312494444142147393)
                  ·
                    rfl

theorem cell22_581493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_581493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581493 prefixEnd_581493 := by exact prefixLift 581493
  have htrace : WordTrace (prefixWord ++ tailWord_581493) baseStart_581493 baseEnd_581493 := by
    simpa [prefixWord, tailWord_581493, baseEnd_581493] using wordTrace_append hprefix tailTrace_581493
  have hstable : (prefixWord ++ tailWord_581493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581493).length < 2 ^ (prefixWord ++ tailWord_581493).sum := by decide
  have hdescent : baseEnd_581493 < baseStart_581493 := by decide
  rcases family_descends (prefixWord ++ tailWord_581493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581508 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_581508 : Nat := 118140960795 + 581508 * 2 ^ 59
def prefixEnd_581508 : Nat := 4983230072969 + 3 ^ 40 * 581508 * 2
def baseEnd_581508 : Nat := 199062072289877387317133

theorem tailTrace_581508 : CollatzResearch.WordTrace tailWord_581508 prefixEnd_581508 199062072289877387317133 := by
  unfold tailWord_581508
  simp only [CollatzResearch.WordTrace]
  refine ⟨10604669588651652252372589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14139559451535536336496785 10604669588651652252372589)
  ·
    refine ⟨3976751095744369594639721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10604669588651652252372589 3976751095744369594639721)
    ·
      refine ⟨2982563321808277195979791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3976751095744369594639721 2982563321808277195979791)
      ·
        refine ⟨4473844982712415793969687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2982563321808277195979791 4473844982712415793969687)
        ·
          refine ⟨6710767474068623690954531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4473844982712415793969687 6710767474068623690954531)
          ·
            refine ⟨10066151211102935536431797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6710767474068623690954531 10066151211102935536431797)
            ·
              refine ⟨943701676040900206540481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10066151211102935536431797 943701676040900206540481)
              ·
                refine ⟨707776257030675154905361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943701676040900206540481 707776257030675154905361)
                ·
                  refine ⟨530832192773006366179021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707776257030675154905361 530832192773006366179021)
                  ·
                    refine ⟨199062072289877387317133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530832192773006366179021 199062072289877387317133)
                    ·
                      rfl

theorem cell22_581508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_581508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581508 prefixEnd_581508 := by exact prefixLift 581508
  have htrace : WordTrace (prefixWord ++ tailWord_581508) baseStart_581508 baseEnd_581508 := by
    simpa [prefixWord, tailWord_581508, baseEnd_581508] using wordTrace_append hprefix tailTrace_581508
  have hstable : (prefixWord ++ tailWord_581508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581508).length < 2 ^ (prefixWord ++ tailWord_581508).sum := by decide
  have hdescent : baseEnd_581508 < baseStart_581508 := by decide
  rcases family_descends (prefixWord ++ tailWord_581508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581544 : List Nat := [2, 1, 6, 2, 2, 1, 1, 3, 4]
def baseStart_581544 : Nat := 118140960795 + 581544 * 2 ^ 59
def prefixEnd_581544 : Nat := 4983230072969 + 3 ^ 40 * 581544 * 2
def baseEnd_581544 : Nat := 66358131941861764472341

theorem tailTrace_581544 : CollatzResearch.WordTrace tailWord_581544 prefixEnd_581544 66358131941861764472341 := by
  unfold tailWord_581544
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605326102586441326527843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14140434803448588435370457 10605326102586441326527843)
  ·
    refine ⟨15907989153879661989791765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10605326102586441326527843 15907989153879661989791765)
    ·
      refine ⟨745686991588109155771489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15907989153879661989791765 745686991588109155771489)
      ·
        refine ⟨559265243691081866828617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 745686991588109155771489 559265243691081866828617)
        ·
          refine ⟨419448932768311400121463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559265243691081866828617 419448932768311400121463)
          ·
            refine ⟨629173399152467100182195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419448932768311400121463 629173399152467100182195)
            ·
              refine ⟨943760098728700650273293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629173399152467100182195 943760098728700650273293)
              ·
                refine ⟨353910037023262743852485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 943760098728700650273293 353910037023262743852485)
                ·
                  refine ⟨66358131941861764472341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 353910037023262743852485 66358131941861764472341)
                  ·
                    rfl

theorem cell22_581544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 4].length) (baseStart_581544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581544 prefixEnd_581544 := by exact prefixLift 581544
  have htrace : WordTrace (prefixWord ++ tailWord_581544) baseStart_581544 baseEnd_581544 := by
    simpa [prefixWord, tailWord_581544, baseEnd_581544] using wordTrace_append hprefix tailTrace_581544
  have hstable : (prefixWord ++ tailWord_581544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581544).length < 2 ^ (prefixWord ++ tailWord_581544).sum := by decide
  have hdescent : baseEnd_581544 < baseStart_581544 := by decide
  rcases family_descends (prefixWord ++ tailWord_581544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581566 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_581566 : Nat := 118140960795 + 581566 * 2 ^ 59
def prefixEnd_581566 : Nat := 4983230072969 + 3 ^ 40 * 581566 * 2
def baseEnd_581566 : Nat := 66360642291728189788985

theorem tailTrace_581566 : CollatzResearch.WordTrace tailWord_581566 prefixEnd_581566 66360642291728189788985 := by
  unfold tailWord_581566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2651431826386647551294569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14140969740728786940237701 2651431826386647551294569)
  ·
    refine ⟨1988573869789985663470927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2651431826386647551294569 1988573869789985663470927)
    ·
      refine ⟨2982860804684978495206391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1988573869789985663470927 2982860804684978495206391)
      ·
        refine ⟨4474291207027467742809587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2982860804684978495206391 4474291207027467742809587)
        ·
          refine ⟨6711436810541201614214381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4474291207027467742809587 6711436810541201614214381)
          ·
            refine ⟨2516788803952950605330393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6711436810541201614214381 2516788803952950605330393)
            ·
              refine ⟨1887591602964712953997795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516788803952950605330393 1887591602964712953997795)
              ·
                refine ⟨2831387404447069430996693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887591602964712953997795 2831387404447069430996693)
                ·
                  refine ⟨66360642291728189788985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2831387404447069430996693 66360642291728189788985)
                  ·
                    rfl

theorem cell22_581566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_581566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581566 prefixEnd_581566 := by exact prefixLift 581566
  have htrace : WordTrace (prefixWord ++ tailWord_581566) baseStart_581566 baseEnd_581566 := by
    simpa [prefixWord, tailWord_581566, baseEnd_581566] using wordTrace_append hprefix tailTrace_581566
  have hstable : (prefixWord ++ tailWord_581566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581566).length < 2 ^ (prefixWord ++ tailWord_581566).sum := by decide
  have hdescent : baseEnd_581566 < baseStart_581566 := by decide
  rcases family_descends (prefixWord ++ tailWord_581566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581628 : List Nat := [2, 2, 2, 1, 2, 2, 3, 4, 4]
def baseStart_581628 : Nat := 118140960795 + 581628 * 2 ^ 59
def prefixEnd_581628 : Nat := 4983230072969 + 3 ^ 40 * 581628 * 2
def baseEnd_581628 : Nat := 66367716914079024772255

theorem tailTrace_581628 : CollatzResearch.WordTrace tailWord_581628 prefixEnd_581628 66367716914079024772255 := by
  unfold tailWord_581628
  simp only [CollatzResearch.WordTrace]
  refine ⟨10606857968434282499556769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14142477291245709999409025 10606857968434282499556769)
  ·
    refine ⟨7955143476325711874667577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10606857968434282499556769 7955143476325711874667577)
    ·
      refine ⟨5966357607244283906000683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7955143476325711874667577 5966357607244283906000683)
      ·
        refine ⟨8949536410866425859001025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5966357607244283906000683 8949536410866425859001025)
        ·
          refine ⟨6712152308149819394250769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8949536410866425859001025 6712152308149819394250769)
          ·
            refine ⟨5034114231112364545688077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6712152308149819394250769 5034114231112364545688077)
            ·
              refine ⟨1887792836667136704633029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5034114231112364545688077 1887792836667136704633029)
              ·
                refine ⟨353961156875088132118693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1887792836667136704633029 353961156875088132118693)
                ·
                  refine ⟨66367716914079024772255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 353961156875088132118693 66367716914079024772255)
                  ·
                    rfl

theorem cell22_581628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_581628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581628 prefixEnd_581628 := by exact prefixLift 581628
  have htrace : WordTrace (prefixWord ++ tailWord_581628) baseStart_581628 baseEnd_581628 := by
    simpa [prefixWord, tailWord_581628, baseEnd_581628] using wordTrace_append hprefix tailTrace_581628
  have hstable : (prefixWord ++ tailWord_581628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581628).length < 2 ^ (prefixWord ++ tailWord_581628).sum := by decide
  have hdescent : baseEnd_581628 < baseStart_581628 := by decide
  rcases family_descends (prefixWord ++ tailWord_581628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581643 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 2, 3]
def baseStart_581643 : Nat := 118140960795 + 581643 * 2 ^ 59
def prefixEnd_581643 : Nat := 4983230072969 + 3 ^ 40 * 581643 * 2
def baseEnd_581643 : Nat := 199108285548782035191719

theorem tailTrace_581643 : CollatzResearch.WordTrace tailWord_581643 prefixEnd_581643 199108285548782035191719 := by
  unfold tailWord_581643
  simp only [CollatzResearch.WordTrace]
  refine ⟨21214263031814222560909583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14142842021209481707273055 21214263031814222560909583)
  ·
    refine ⟨31821394547721333841364375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21214263031814222560909583 31821394547721333841364375)
    ·
      refine ⟨47732091821582000762046563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31821394547721333841364375 47732091821582000762046563)
      ·
        refine ⟨71598137732373001143069845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47732091821582000762046563 71598137732373001143069845)
        ·
          refine ⟨3356162706204984428581399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71598137732373001143069845 3356162706204984428581399)
          ·
            refine ⟨5034244059307476642872099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356162706204984428581399 5034244059307476642872099)
            ·
              refine ⟨7551366088961214964308149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5034244059307476642872099 7551366088961214964308149)
              ·
                refine ⟨707940570840113902903889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7551366088961214964308149 707940570840113902903889)
                ·
                  refine ⟨530955428130085427177917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707940570840113902903889 530955428130085427177917)
                  ·
                    refine ⟨199108285548782035191719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530955428130085427177917 199108285548782035191719)
                    ·
                      rfl

theorem cell22_581643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 3].length) (baseStart_581643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581643 prefixEnd_581643 := by exact prefixLift 581643
  have htrace : WordTrace (prefixWord ++ tailWord_581643) baseStart_581643 baseEnd_581643 := by
    simpa [prefixWord, tailWord_581643, baseEnd_581643] using wordTrace_append hprefix tailTrace_581643
  have hstable : (prefixWord ++ tailWord_581643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581643).length < 2 ^ (prefixWord ++ tailWord_581643).sum := by decide
  have hdescent : baseEnd_581643 < baseStart_581643 := by decide
  rcases family_descends (prefixWord ++ tailWord_581643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581658 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_581658 : Nat := 118140960795 + 581658 * 2 ^ 59
def prefixEnd_581658 : Nat := 4983230072969 + 3 ^ 40 * 581658 * 2
def baseEnd_581658 : Nat := 199113420355326996066673

theorem tailTrace_581658 : CollatzResearch.WordTrace tailWord_581658 prefixEnd_581658 199113420355326996066673 := by
  unfold tailWord_581658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5303702531689970030676407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14143206751173253415137085 5303702531689970030676407)
  ·
    refine ⟨7955553797534955046014611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5303702531689970030676407 7955553797534955046014611)
    ·
      refine ⟨11933330696302432569021917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7955553797534955046014611 11933330696302432569021917)
      ·
        refine ⟨4474999011113412213383219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11933330696302432569021917 4474999011113412213383219)
        ·
          refine ⟨6712498516670118320074829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4474999011113412213383219 6712498516670118320074829)
          ·
            refine ⟨2517186943751294370028061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6712498516670118320074829 2517186943751294370028061)
            ·
              refine ⟨943945103906735388760523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2517186943751294370028061 943945103906735388760523)
              ·
                refine ⟨1415917655860103083140785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943945103906735388760523 1415917655860103083140785)
                ·
                  refine ⟨1061938241895077312355589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1415917655860103083140785 1061938241895077312355589)
                  ·
                    refine ⟨199113420355326996066673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1061938241895077312355589 199113420355326996066673)
                    ·
                      rfl

theorem cell22_581658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_581658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581658 prefixEnd_581658 := by exact prefixLift 581658
  have htrace : WordTrace (prefixWord ++ tailWord_581658) baseStart_581658 baseEnd_581658 := by
    simpa [prefixWord, tailWord_581658, baseEnd_581658] using wordTrace_append hprefix tailTrace_581658
  have hstable : (prefixWord ++ tailWord_581658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581658).length < 2 ^ (prefixWord ++ tailWord_581658).sum := by decide
  have hdescent : baseEnd_581658 < baseStart_581658 := by decide
  rcases family_descends (prefixWord ++ tailWord_581658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581694 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_581694 : Nat := 118140960795 + 581694 * 2 ^ 59
def prefixEnd_581694 : Nat := 4983230072969 + 3 ^ 40 * 581694 * 2
def baseEnd_581694 : Nat := 199125743891034902166563

theorem tailTrace_581694 : CollatzResearch.WordTrace tailWord_581694 prefixEnd_581694 199125743891034902166563 := by
  unfold tailWord_581694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652015394328682283877017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14144082103086305514010757 2652015394328682283877017)
  ·
    refine ⟨1989011545746511712907763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2652015394328682283877017 1989011545746511712907763)
    ·
      refine ⟨2983517318619767569361645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989011545746511712907763 2983517318619767569361645)
      ·
        refine ⟨1118818994482412838510617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2983517318619767569361645 1118818994482412838510617)
        ·
          refine ⟨839114245861809628882963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1118818994482412838510617 839114245861809628882963)
          ·
            refine ⟨1258671368792714443324445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839114245861809628882963 1258671368792714443324445)
            ·
              refine ⟨472001763297267916246667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1258671368792714443324445 472001763297267916246667)
              ·
                refine ⟨708002644945901874370001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472001763297267916246667 708002644945901874370001)
                ·
                  refine ⟨531001983709426405777501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 708002644945901874370001 531001983709426405777501)
                  ·
                    refine ⟨199125743891034902166563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 531001983709426405777501 199125743891034902166563)
                    ·
                      rfl

theorem cell22_581694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_581694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581694 prefixEnd_581694 := by exact prefixLift 581694
  have htrace : WordTrace (prefixWord ++ tailWord_581694) baseStart_581694 baseEnd_581694 := by
    simpa [prefixWord, tailWord_581694, baseEnd_581694] using wordTrace_append hprefix tailTrace_581694
  have hstable : (prefixWord ++ tailWord_581694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581694).length < 2 ^ (prefixWord ++ tailWord_581694).sum := by decide
  have hdescent : baseEnd_581694 < baseStart_581694 := by decide
  rcases family_descends (prefixWord ++ tailWord_581694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581765 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_581765 : Nat := 118140960795 + 581765 * 2 ^ 59
def prefixEnd_581765 : Nat := 4983230072969 + 3 ^ 40 * 581765 * 2
def baseEnd_581765 : Nat := 199150048642014383641345

theorem tailTrace_581765 : CollatzResearch.WordTrace tailWord_581765 prefixEnd_581765 199150048642014383641345 := by
  unfold tailWord_581765
  simp only [CollatzResearch.WordTrace]
  refine ⟨21218712737372237396850749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14145808491581491597900499 21218712737372237396850749)
  ·
    refine ⟨7957017276514589023819031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21218712737372237396850749 7957017276514589023819031)
    ·
      refine ⟨11935525914771883535728547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7957017276514589023819031 11935525914771883535728547)
      ·
        refine ⟨17903288872157825303592821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11935525914771883535728547 17903288872157825303592821)
        ·
          refine ⟨1678433331764796122211827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17903288872157825303592821 1678433331764796122211827)
          ·
            refine ⟨2517649997647194183317741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678433331764796122211827 2517649997647194183317741)
            ·
              refine ⟨944118749117697818744153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2517649997647194183317741 944118749117697818744153)
              ·
                refine ⟨708089061838273364058115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944118749117697818744153 708089061838273364058115)
                ·
                  refine ⟨1062133592757410046087173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708089061838273364058115 1062133592757410046087173)
                  ·
                    refine ⟨199150048642014383641345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1062133592757410046087173 199150048642014383641345)
                    ·
                      rfl

theorem cell22_581765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_581765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581765 prefixEnd_581765 := by exact prefixLift 581765
  have htrace : WordTrace (prefixWord ++ tailWord_581765) baseStart_581765 baseEnd_581765 := by
    simpa [prefixWord, tailWord_581765, baseEnd_581765] using wordTrace_append hprefix tailTrace_581765
  have hstable : (prefixWord ++ tailWord_581765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581765).length < 2 ^ (prefixWord ++ tailWord_581765).sum := by decide
  have hdescent : baseEnd_581765 < baseStart_581765 := by decide
  rcases family_descends (prefixWord ++ tailWord_581765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581846 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_581846 : Nat := 118140960795 + 581846 * 2 ^ 59
def prefixEnd_581846 : Nat := 4983230072969 + 3 ^ 40 * 581846 * 2
def baseEnd_581846 : Nat := 199177776597357172366097

theorem tailTrace_581846 : CollatzResearch.WordTrace tailWord_581846 prefixEnd_581846 199177776597357172366097 := by
  unfold tailWord_581846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1326354190629924264409337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14147778033385858820366261 1326354190629924264409337)
  ·
    refine ⟨994765642972443198307003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1326354190629924264409337 994765642972443198307003)
    ·
      refine ⟨1492148464458664797460505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994765642972443198307003 1492148464458664797460505)
      ·
        refine ⟨1119111348343998598095379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1492148464458664797460505 1119111348343998598095379)
        ·
          refine ⟨1678667022515997897143069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119111348343998598095379 1678667022515997897143069)
          ·
            refine ⟨629500133443499211428651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1678667022515997897143069 629500133443499211428651)
            ·
              refine ⟨944250200165248817142977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629500133443499211428651 944250200165248817142977)
              ·
                refine ⟨708187650123936612857233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944250200165248817142977 708187650123936612857233)
                ·
                  refine ⟨531140737592952459642925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 708187650123936612857233 531140737592952459642925)
                  ·
                    refine ⟨199177776597357172366097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 531140737592952459642925 199177776597357172366097)
                    ·
                      rfl

theorem cell22_581846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_581846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581846 prefixEnd_581846 := by exact prefixLift 581846
  have htrace : WordTrace (prefixWord ++ tailWord_581846) baseStart_581846 baseEnd_581846 := by
    simpa [prefixWord, tailWord_581846, baseEnd_581846] using wordTrace_append hprefix tailTrace_581846
  have hstable : (prefixWord ++ tailWord_581846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581846).length < 2 ^ (prefixWord ++ tailWord_581846).sum := by decide
  have hdescent : baseEnd_581846 < baseStart_581846 := by decide
  rcases family_descends (prefixWord ++ tailWord_581846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581857 : List Nat := [1, 2, 3, 1, 3, 1, 1, 6, 1, 3]
def baseStart_581857 : Nat := 118140960795 + 581857 * 2 ^ 59
def prefixEnd_581857 : Nat := 4983230072969 + 3 ^ 40 * 581857 * 2
def baseEnd_581857 : Nat := 199181542122156810341063

theorem tailTrace_581857 : CollatzResearch.WordTrace tailWord_581857 prefixEnd_581857 199181542122156810341063 := by
  unfold tailWord_581857
  simp only [CollatzResearch.WordTrace]
  refine ⟨21222068253038937109199825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14148045502025958072799883 21222068253038937109199825)
  ·
    refine ⟨15916551189779202831899869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21222068253038937109199825 15916551189779202831899869)
    ·
      refine ⟨5968706696167201061962451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15916551189779202831899869 5968706696167201061962451)
      ·
        refine ⟨8953060044250801592943677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5968706696167201061962451 8953060044250801592943677)
        ·
          refine ⟨3357397516594050597353879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8953060044250801592943677 3357397516594050597353879)
          ·
            refine ⟨5036096274891075896030819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357397516594050597353879 5036096274891075896030819)
            ·
              refine ⟨7554144412336613844046229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5036096274891075896030819 7554144412336613844046229)
              ·
                refine ⟨354100519328278773939667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7554144412336613844046229 354100519328278773939667)
                ·
                  refine ⟨531150778992418160909501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354100519328278773939667 531150778992418160909501)
                  ·
                    refine ⟨199181542122156810341063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 531150778992418160909501 199181542122156810341063)
                    ·
                      rfl

theorem cell22_581857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_581857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581857 prefixEnd_581857 := by exact prefixLift 581857
  have htrace : WordTrace (prefixWord ++ tailWord_581857) baseStart_581857 baseEnd_581857 := by
    simpa [prefixWord, tailWord_581857, baseEnd_581857] using wordTrace_append hprefix tailTrace_581857
  have hstable : (prefixWord ++ tailWord_581857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581857).length < 2 ^ (prefixWord ++ tailWord_581857).sum := by decide
  have hdescent : baseEnd_581857 < baseStart_581857 := by decide
  rcases family_descends (prefixWord ++ tailWord_581857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581868 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_581868 : Nat := 118140960795 + 581868 * 2 ^ 59
def prefixEnd_581868 : Nat := 4983230072969 + 3 ^ 40 * 581868 * 2
def baseEnd_581868 : Nat := 199185307646956448316029

theorem tailTrace_581868 : CollatzResearch.WordTrace tailWord_581868 prefixEnd_581868 199185307646956448316029 := by
  unfold tailWord_581868
  simp only [CollatzResearch.WordTrace]
  refine ⟨10611234727999542993925129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14148312970666057325233505 10611234727999542993925129)
  ·
    refine ⟨7958426045999657245443847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10611234727999542993925129 7958426045999657245443847)
    ·
      refine ⟨11937639068999485868165771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7958426045999657245443847 11937639068999485868165771)
      ·
        refine ⟨17906458603499228802248657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11937639068999485868165771 17906458603499228802248657)
        ·
          refine ⟨13429843952624421601686493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17906458603499228802248657 13429843952624421601686493)
          ·
            refine ⟨5036191482234158100632435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13429843952624421601686493 5036191482234158100632435)
            ·
              refine ⟨7554287223351237150948653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5036191482234158100632435 7554287223351237150948653)
              ·
                refine ⟨2832857708756713931605745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7554287223351237150948653 2832857708756713931605745)
                ·
                  refine ⟨2124643281567535448704309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2832857708756713931605745 2124643281567535448704309)
                  ·
                    refine ⟨199185307646956448316029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2124643281567535448704309 199185307646956448316029)
                    ·
                      rfl

theorem cell22_581868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_581868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581868 prefixEnd_581868 := by exact prefixLift 581868
  have htrace : WordTrace (prefixWord ++ tailWord_581868) baseStart_581868 baseEnd_581868 := by
    simpa [prefixWord, tailWord_581868, baseEnd_581868] using wordTrace_append hprefix tailTrace_581868
  have hstable : (prefixWord ++ tailWord_581868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581868).length < 2 ^ (prefixWord ++ tailWord_581868).sum := by decide
  have hdescent : baseEnd_581868 < baseStart_581868 := by decide
  rcases family_descends (prefixWord ++ tailWord_581868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581898 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_581898 : Nat := 118140960795 + 581898 * 2 ^ 59
def prefixEnd_581898 : Nat := 4983230072969 + 3 ^ 40 * 581898 * 2
def baseEnd_581898 : Nat := 66398525753348790021979

theorem tailTrace_581898 : CollatzResearch.WordTrace tailWord_581898 prefixEnd_581898 66398525753348790021979 := by
  unfold tailWord_581898
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305890911472600277860587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14149042430593600740961565 5305890911472600277860587)
  ·
    refine ⟨7958836367208900416790881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5305890911472600277860587 7958836367208900416790881)
    ·
      refine ⟨5969127275406675312593161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7958836367208900416790881 5969127275406675312593161)
      ·
        refine ⟨4476845456555006484444871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5969127275406675312593161 4476845456555006484444871)
        ·
          refine ⟨6715268184832509726667307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4476845456555006484444871 6715268184832509726667307)
          ·
            refine ⟨10072902277248764590000961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6715268184832509726667307 10072902277248764590000961)
            ·
              refine ⟨7554676707936573442500721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10072902277248764590000961 7554676707936573442500721)
              ·
                refine ⟨5666007530952430081875541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7554676707936573442500721 5666007530952430081875541)
                ·
                  refine ⟨66398525753348790021979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5666007530952430081875541 66398525753348790021979)
                  ·
                    rfl

theorem cell22_581898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_581898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581898 prefixEnd_581898 := by exact prefixLift 581898
  have htrace : WordTrace (prefixWord ++ tailWord_581898) baseStart_581898 baseEnd_581898 := by
    simpa [prefixWord, tailWord_581898, baseEnd_581898] using wordTrace_append hprefix tailTrace_581898
  have hstable : (prefixWord ++ tailWord_581898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581898).length < 2 ^ (prefixWord ++ tailWord_581898).sum := by decide
  have hdescent : baseEnd_581898 < baseStart_581898 := by decide
  rcases family_descends (prefixWord ++ tailWord_581898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581900 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_581900 : Nat := 118140960795 + 581900 * 2 ^ 59
def prefixEnd_581900 : Nat := 4983230072969 + 3 ^ 40 * 581900 * 2
def baseEnd_581900 : Nat := 199196261900919031515931

theorem tailTrace_581900 : CollatzResearch.WordTrace tailWord_581900 prefixEnd_581900 199196261900919031515931 := by
  unfold tailWord_581900
  simp only [CollatzResearch.WordTrace]
  refine ⟨10611818295941577726507577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14149091061255436968676769 10611818295941577726507577)
  ·
    refine ⟨7958863721956183294880683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10611818295941577726507577 7958863721956183294880683)
    ·
      refine ⟨11938295582934274942321025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7958863721956183294880683 11938295582934274942321025)
      ·
        refine ⟨8953721687200706206740769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11938295582934274942321025 8953721687200706206740769)
        ·
          refine ⟨6715291265400529655055577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8953721687200706206740769 6715291265400529655055577)
          ·
            refine ⟨5036468449050397241291683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6715291265400529655055577 5036468449050397241291683)
            ·
              refine ⟨7554702673575595861937525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5036468449050397241291683 7554702673575595861937525)
              ·
                refine ⟨708253375647712112056643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7554702673575595861937525 708253375647712112056643)
                ·
                  refine ⟨1062380063471568168084965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708253375647712112056643 1062380063471568168084965)
                  ·
                    refine ⟨199196261900919031515931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1062380063471568168084965 199196261900919031515931)
                    ·
                      rfl

theorem cell22_581900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_581900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581900 prefixEnd_581900 := by exact prefixLift 581900
  have htrace : WordTrace (prefixWord ++ tailWord_581900) baseStart_581900 baseEnd_581900 := by
    simpa [prefixWord, tailWord_581900, baseEnd_581900] using wordTrace_append hprefix tailTrace_581900
  have hstable : (prefixWord ++ tailWord_581900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581900).length < 2 ^ (prefixWord ++ tailWord_581900).sum := by decide
  have hdescent : baseEnd_581900 < baseStart_581900 := by decide
  rcases family_descends (prefixWord ++ tailWord_581900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581915 : List Nat := [1, 1, 1, 1, 1, 1, 6, 6, 4]
def baseStart_581915 : Nat := 118140960795 + 581915 * 2 ^ 59
def prefixEnd_581915 : Nat := 4983230072969 + 3 ^ 40 * 581915 * 2
def baseEnd_581915 : Nat := 66400465569154664130295

theorem tailTrace_581915 : CollatzResearch.WordTrace tailWord_581915 prefixEnd_581915 66400465569154664130295 := by
  unfold tailWord_581915
  simp only [CollatzResearch.WordTrace]
  refine ⟨21224183686828813014811199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14149455791219208676540799 21224183686828813014811199)
  ·
    refine ⟨31836275530243219522216799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21224183686828813014811199 31836275530243219522216799)
    ·
      refine ⟨47754413295364829283325199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31836275530243219522216799 47754413295364829283325199)
      ·
        refine ⟨71631619943047243924987799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47754413295364829283325199 71631619943047243924987799)
        ·
          refine ⟨107447429914570865887481699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71631619943047243924987799 107447429914570865887481699)
          ·
            refine ⟨161171144871856298831222549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107447429914570865887481699 161171144871856298831222549)
            ·
              refine ⟨7554897415868264007713557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161171144871856298831222549 7554897415868264007713557)
              ·
                refine ⟨354135816368824875361573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7554897415868264007713557 354135816368824875361573)
                ·
                  refine ⟨66400465569154664130295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354135816368824875361573 66400465569154664130295)
                  ·
                    rfl

theorem cell22_581915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 4].length) (baseStart_581915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581915 prefixEnd_581915 := by exact prefixLift 581915
  have htrace : WordTrace (prefixWord ++ tailWord_581915) baseStart_581915 baseEnd_581915 := by
    simpa [prefixWord, tailWord_581915, baseEnd_581915] using wordTrace_append hprefix tailTrace_581915
  have hstable : (prefixWord ++ tailWord_581915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581915).length < 2 ^ (prefixWord ++ tailWord_581915).sum := by decide
  have hdescent : baseEnd_581915 < baseStart_581915 := by decide
  rcases family_descends (prefixWord ++ tailWord_581915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581934 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_581934 : Nat := 118140960795 + 581934 * 2 ^ 59
def prefixEnd_581934 : Nat := 4983230072969 + 3 ^ 40 * 581934 * 2
def baseEnd_581934 : Nat := 199207900795754276165827

theorem tailTrace_581934 : CollatzResearch.WordTrace tailWord_581934 prefixEnd_581934 199207900795754276165827 := by
  unfold tailWord_581934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653109584219997407469107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14149917782506652839835237 2653109584219997407469107)
  ·
    refine ⟨3979664376329996111203661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2653109584219997407469107 3979664376329996111203661)
    ·
      refine ⟨1492374141123748541701373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3979664376329996111203661 1492374141123748541701373)
      ·
        refine ⟨559640302921405703138015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1492374141123748541701373 559640302921405703138015)
        ·
          refine ⟨839460454382108554707023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559640302921405703138015 839460454382108554707023)
          ·
            refine ⟨1259190681573162832060535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839460454382108554707023 1259190681573162832060535)
            ·
              refine ⟨1888786022359744248090803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259190681573162832060535 1888786022359744248090803)
              ·
                refine ⟨2833179033539616372136205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1888786022359744248090803 2833179033539616372136205)
                ·
                  refine ⟨1062442137577356139551077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2833179033539616372136205 1062442137577356139551077)
                  ·
                    refine ⟨199207900795754276165827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1062442137577356139551077 199207900795754276165827)
                    ·
                      rfl

theorem cell22_581934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_581934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581934 prefixEnd_581934 := by exact prefixLift 581934
  have htrace : WordTrace (prefixWord ++ tailWord_581934) baseStart_581934 baseEnd_581934 := by
    simpa [prefixWord, tailWord_581934, baseEnd_581934] using wordTrace_append hprefix tailTrace_581934
  have hstable : (prefixWord ++ tailWord_581934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581934).length < 2 ^ (prefixWord ++ tailWord_581934).sum := by decide
  have hdescent : baseEnd_581934 < baseStart_581934 := by decide
  rcases family_descends (prefixWord ++ tailWord_581934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581992 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 5, 3]
def baseStart_581992 : Nat := 118140960795 + 581992 * 2 ^ 59
def prefixEnd_581992 : Nat := 4983230072969 + 3 ^ 40 * 581992 * 2
def baseEnd_581992 : Nat := 199227755381061458215649

theorem tailTrace_581992 : CollatzResearch.WordTrace tailWord_581992 prefixEnd_581992 199227755381061458215649 := by
  unfold tailWord_581992
  simp only [CollatzResearch.WordTrace]
  refine ⟨10613496053774927582682115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14151328071699903443576153 10613496053774927582682115)
  ·
    refine ⟨15920244080662391374023173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10613496053774927582682115 15920244080662391374023173)
    ·
      refine ⟨2985045765124198382629345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15920244080662391374023173 2985045765124198382629345)
      ·
        refine ⟨2238784323843148786972009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2985045765124198382629345 2238784323843148786972009)
        ·
          refine ⟨1679088242882361590229007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2238784323843148786972009 1679088242882361590229007)
          ·
            refine ⟨2518632364323542385343511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679088242882361590229007 2518632364323542385343511)
            ·
              refine ⟨3777948546485313578015267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518632364323542385343511 3777948546485313578015267)
              ·
                refine ⟨5666922819727970367022901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777948546485313578015267 5666922819727970367022901)
                ·
                  refine ⟨531274014349497221908397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5666922819727970367022901 531274014349497221908397)
                  ·
                    refine ⟨199227755381061458215649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 531274014349497221908397 199227755381061458215649)
                    ·
                      rfl

theorem cell22_581992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_581992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_581992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_581992 prefixEnd_581992 := by exact prefixLift 581992
  have htrace : WordTrace (prefixWord ++ tailWord_581992) baseStart_581992 baseEnd_581992 := by
    simpa [prefixWord, tailWord_581992, baseEnd_581992] using wordTrace_append hprefix tailTrace_581992
  have hstable : (prefixWord ++ tailWord_581992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581992).length < 2 ^ (prefixWord ++ tailWord_581992).sum := by decide
  have hdescent : baseEnd_581992 < baseStart_581992 := by decide
  rcases family_descends (prefixWord ++ tailWord_581992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582020 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_582020 : Nat := 118140960795 + 582020 * 2 ^ 59
def prefixEnd_582020 : Nat := 4983230072969 + 3 ^ 40 * 582020 * 2
def baseEnd_582020 : Nat := 199237340353278718515563

theorem tailTrace_582020 : CollatzResearch.WordTrace tailWord_582020 prefixEnd_582020 199237340353278718515563 := by
  unfold tailWord_582020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10614006675724207973691757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14152008900965610631589009 10614006675724207973691757)
  ·
    refine ⟨3980252503396577990134409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10614006675724207973691757 3980252503396577990134409)
    ·
      refine ⟨2985189377547433492600807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3980252503396577990134409 2985189377547433492600807)
      ·
        refine ⟨4477784066321150238901211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985189377547433492600807 4477784066321150238901211)
        ·
          refine ⟨6716676099481725358351817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4477784066321150238901211 6716676099481725358351817)
          ·
            refine ⟨5037507074611294018763863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6716676099481725358351817 5037507074611294018763863)
            ·
              refine ⟨7556260611916941028145795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5037507074611294018763863 7556260611916941028145795)
              ·
                refine ⟨11334390917875411542218693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7556260611916941028145795 11334390917875411542218693)
                ·
                  refine ⟨2125198297101639664166005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11334390917875411542218693 2125198297101639664166005)
                  ·
                    refine ⟨199237340353278718515563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2125198297101639664166005 199237340353278718515563)
                    ·
                      rfl

theorem cell22_582020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_582020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582020 prefixEnd_582020 := by exact prefixLift 582020
  have htrace : WordTrace (prefixWord ++ tailWord_582020) baseStart_582020 baseEnd_582020 := by
    simpa [prefixWord, tailWord_582020, baseEnd_582020] using wordTrace_append hprefix tailTrace_582020
  have hstable : (prefixWord ++ tailWord_582020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582020).length < 2 ^ (prefixWord ++ tailWord_582020).sum := by decide
  have hdescent : baseEnd_582020 < baseStart_582020 := by decide
  rcases family_descends (prefixWord ++ tailWord_582020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582026 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 3, 3]
def baseStart_582026 : Nat := 118140960795 + 582026 * 2 ^ 59
def prefixEnd_582026 : Nat := 4983230072969 + 3 ^ 40 * 582026 * 2
def baseEnd_582026 : Nat := 199239394275896702865545

theorem tailTrace_582026 : CollatzResearch.WordTrace tailWord_582026 prefixEnd_582026 199239394275896702865545 := by
  unfold tailWord_582026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5307058047356669743025483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14152154792951119314734621 5307058047356669743025483)
  ·
    refine ⟨7960587071035004614538225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5307058047356669743025483 7960587071035004614538225)
    ·
      refine ⟨5970440303276253460903669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7960587071035004614538225 5970440303276253460903669)
      ·
        refine ⟨559728778432148761959719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5970440303276253460903669 559728778432148761959719)
        ·
          refine ⟨839593167648223142939579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559728778432148761959719 839593167648223142939579)
          ·
            refine ⟨1259389751472334714409369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839593167648223142939579 1259389751472334714409369)
            ·
              refine ⟨944542313604251035807027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259389751472334714409369 944542313604251035807027)
              ·
                refine ⟨1416813470406376553710541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944542313604251035807027 1416813470406376553710541)
                ·
                  refine ⟨531305051402391207641453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1416813470406376553710541 531305051402391207641453)
                  ·
                    refine ⟨199239394275896702865545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 531305051402391207641453 199239394275896702865545)
                    ·
                      rfl

theorem cell22_582026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_582026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582026 prefixEnd_582026 := by exact prefixLift 582026
  have htrace : WordTrace (prefixWord ++ tailWord_582026) baseStart_582026 baseEnd_582026 := by
    simpa [prefixWord, tailWord_582026, baseEnd_582026] using wordTrace_append hprefix tailTrace_582026
  have hstable : (prefixWord ++ tailWord_582026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582026).length < 2 ^ (prefixWord ++ tailWord_582026).sum := by decide
  have hdescent : baseEnd_582026 < baseStart_582026 := by decide
  rcases family_descends (prefixWord ++ tailWord_582026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582052 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_582052 : Nat := 118140960795 + 582052 * 2 ^ 59
def prefixEnd_582052 : Nat := 4983230072969 + 3 ^ 40 * 582052 * 2
def baseEnd_582052 : Nat := 199248294607241301715465

theorem tailTrace_582052 : CollatzResearch.WordTrace tailWord_582052 prefixEnd_582052 199248294607241301715465 := by
  unfold tailWord_582052
  simp only [CollatzResearch.WordTrace]
  refine ⟨10614590243666242706274205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14152786991554990275032273 10614590243666242706274205)
  ·
    refine ⟨3980471341374841014852827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10614590243666242706274205 3980471341374841014852827)
    ·
      refine ⟨5970707012062261522279241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3980471341374841014852827 5970707012062261522279241)
      ·
        refine ⟨4478030259046696141709431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5970707012062261522279241 4478030259046696141709431)
        ·
          refine ⟨6717045388570044212564147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4478030259046696141709431 6717045388570044212564147)
          ·
            refine ⟨10075568082855066318846221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6717045388570044212564147 10075568082855066318846221)
            ·
              refine ⟨3778338031070649869567333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10075568082855066318846221 3778338031070649869567333)
              ·
                refine ⟨708438380825746850543875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3778338031070649869567333 708438380825746850543875)
                ·
                  refine ⟨1062657571238620275815813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708438380825746850543875 1062657571238620275815813)
                  ·
                    refine ⟨199248294607241301715465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1062657571238620275815813 199248294607241301715465)
                    ·
                      rfl

theorem cell22_582052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_582052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582052 prefixEnd_582052 := by exact prefixLift 582052
  have htrace : WordTrace (prefixWord ++ tailWord_582052) baseStart_582052 baseEnd_582052 := by
    simpa [prefixWord, tailWord_582052, baseEnd_582052] using wordTrace_append hprefix tailTrace_582052
  have hstable : (prefixWord ++ tailWord_582052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582052).length < 2 ^ (prefixWord ++ tailWord_582052).sum := by decide
  have hdescent : baseEnd_582052 < baseStart_582052 := by decide
  rcases family_descends (prefixWord ++ tailWord_582052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582133 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 2, 3]
def baseStart_582133 : Nat := 118140960795 + 582133 * 2 ^ 59
def prefixEnd_582133 : Nat := 4983230072969 + 3 ^ 40 * 582133 * 2
def baseEnd_582133 : Nat := 199276022562584090440217

theorem tailTrace_582133 : CollatzResearch.WordTrace tailWord_582133 prefixEnd_582133 199276022562584090440217 := by
  unfold tailWord_582133
  simp only [CollatzResearch.WordTrace]
  refine ⟨21232134800039036246247053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14154756533359357497498035 21232134800039036246247053)
  ·
    refine ⟨7962050550014638592342645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21232134800039036246247053 7962050550014638592342645)
    ·
      refine ⟨746442239063872368032123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7962050550014638592342645 746442239063872368032123)
      ·
        refine ⟨1119663358595808552048185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746442239063872368032123 1119663358595808552048185)
        ·
          refine ⟨839747518946856414036139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1119663358595808552048185 839747518946856414036139)
          ·
            refine ⟨1259621278420284621054209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839747518946856414036139 1259621278420284621054209)
            ·
              refine ⟨944715958815213465790657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259621278420284621054209 944715958815213465790657)
              ·
                refine ⟨708536969111410099342993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944715958815213465790657 708536969111410099342993)
                ·
                  refine ⟨531402726833557574507245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 708536969111410099342993 531402726833557574507245)
                  ·
                    refine ⟨199276022562584090440217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 531402726833557574507245 199276022562584090440217)
                    ·
                      rfl

theorem cell22_582133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_582133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582133 prefixEnd_582133 := by exact prefixLift 582133
  have htrace : WordTrace (prefixWord ++ tailWord_582133) baseStart_582133 baseEnd_582133 := by
    simpa [prefixWord, tailWord_582133, baseEnd_582133] using wordTrace_append hprefix tailTrace_582133
  have hstable : (prefixWord ++ tailWord_582133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582133).length < 2 ^ (prefixWord ++ tailWord_582133).sum := by decide
  have hdescent : baseEnd_582133 < baseStart_582133 := by decide
  rcases family_descends (prefixWord ++ tailWord_582133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582146 : List Nat := [3, 4, 1, 2, 2, 2, 1, 7]
def baseStart_582146 : Nat := 118140960795 + 582146 * 2 ^ 59
def prefixEnd_582146 : Nat := 4983230072969 + 3 ^ 40 * 582146 * 2
def baseEnd_582146 : Nat := 22142274747584043318353

theorem tailTrace_582146 : CollatzResearch.WordTrace tailWord_582146 prefixEnd_582146 22142274747584043318353 := by
  unfold tailWord_582146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5308152237247984866617573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14155072632661292977646861 5308152237247984866617573)
  ·
    refine ⟨995278544483997162490795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5308152237247984866617573 995278544483997162490795)
    ·
      refine ⟨1492917816725995743736193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 995278544483997162490795 1492917816725995743736193)
      ·
        refine ⟨1119688362544496807802145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1492917816725995743736193 1119688362544496807802145)
        ·
          refine ⟨839766271908372605851609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1119688362544496807802145 839766271908372605851609)
          ·
            refine ⟨629824703931279454388707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 839766271908372605851609 629824703931279454388707)
            ·
              refine ⟨944737055896919181583061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629824703931279454388707 944737055896919181583061)
              ·
                refine ⟨22142274747584043318353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 944737055896919181583061 22142274747584043318353)
                ·
                  rfl

theorem cell22_582146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_582146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582146 prefixEnd_582146 := by exact prefixLift 582146
  have htrace : WordTrace (prefixWord ++ tailWord_582146) baseStart_582146 baseEnd_582146 := by
    simpa [prefixWord, tailWord_582146, baseEnd_582146] using wordTrace_append hprefix tailTrace_582146
  have hstable : (prefixWord ++ tailWord_582146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582146).length < 2 ^ (prefixWord ++ tailWord_582146).sum := by decide
  have hdescent : baseEnd_582146 < baseStart_582146 := by decide
  rcases family_descends (prefixWord ++ tailWord_582146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582150 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_582150 : Nat := 118140960795 + 582150 * 2 ^ 59
def prefixEnd_582150 : Nat := 4983230072969 + 3 ^ 40 * 582150 * 2
def baseEnd_582150 : Nat := 199281842010001712765165

theorem tailTrace_582150 : CollatzResearch.WordTrace tailWord_582150 prefixEnd_582150 199281842010001712765165 := by
  unfold tailWord_582150
  simp only [CollatzResearch.WordTrace]
  refine ⟨663523588780545254675497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14155169893984965433077269 663523588780545254675497)
  ·
    refine ⟨497642691585408941006623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 663523588780545254675497 497642691585408941006623)
    ·
      refine ⟨746464037378113411509935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 497642691585408941006623 746464037378113411509935)
      ·
        refine ⟨1119696056067170117264903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746464037378113411509935 1119696056067170117264903)
        ·
          refine ⟨1679544084100755175897355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119696056067170117264903 1679544084100755175897355)
          ·
            refine ⟨2519316126151132763846033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679544084100755175897355 2519316126151132763846033)
            ·
              refine ⟨1889487094613349572884525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2519316126151132763846033 1889487094613349572884525)
              ·
                refine ⟨708557660480006089831697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1889487094613349572884525 708557660480006089831697)
                ·
                  refine ⟨531418245360004567373773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 708557660480006089831697 531418245360004567373773)
                  ·
                    refine ⟨199281842010001712765165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 531418245360004567373773 199281842010001712765165)
                    ·
                      rfl

theorem cell22_582150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_582150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582150 prefixEnd_582150 := by exact prefixLift 582150
  have htrace : WordTrace (prefixWord ++ tailWord_582150) baseStart_582150 baseEnd_582150 := by
    simpa [prefixWord, tailWord_582150, baseEnd_582150] using wordTrace_append hprefix tailTrace_582150
  have hstable : (prefixWord ++ tailWord_582150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582150).length < 2 ^ (prefixWord ++ tailWord_582150).sum := by decide
  have hdescent : baseEnd_582150 < baseStart_582150 := by decide
  rcases family_descends (prefixWord ++ tailWord_582150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582202 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_582202 : Nat := 118140960795 + 582202 * 2 ^ 59
def prefixEnd_582202 : Nat := 4983230072969 + 3 ^ 40 * 582202 * 2
def baseEnd_582202 : Nat := 66433214224230303488335

theorem tailTrace_582202 : CollatzResearch.WordTrace tailWord_582202 prefixEnd_582202 66433214224230303488335 := by
  unfold tailWord_582202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5308662859197265257627215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14156434291192707353672573 5308662859197265257627215)
  ·
    refine ⟨7962994288795897886440823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5308662859197265257627215 7962994288795897886440823)
    ·
      refine ⟨11944491433193846829661235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7962994288795897886440823 11944491433193846829661235)
      ·
        refine ⟨17916737149790770244491853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11944491433193846829661235 17916737149790770244491853)
        ·
          refine ⟨6718776431171538841684445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17916737149790770244491853 6718776431171538841684445)
          ·
            refine ⟨2519541161689327065631667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6718776431171538841684445 2519541161689327065631667)
            ·
              refine ⟨3779311742533990598447501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519541161689327065631667 3779311742533990598447501)
              ·
                refine ⟨1417241903450246474417813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3779311742533990598447501 1417241903450246474417813)
                ·
                  refine ⟨66433214224230303488335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1417241903450246474417813 66433214224230303488335)
                  ·
                    rfl

theorem cell22_582202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_582202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582202 prefixEnd_582202 := by exact prefixLift 582202
  have htrace : WordTrace (prefixWord ++ tailWord_582202) baseStart_582202 baseEnd_582202 := by
    simpa [prefixWord, tailWord_582202, baseEnd_582202] using wordTrace_append hprefix tailTrace_582202
  have hstable : (prefixWord ++ tailWord_582202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582202).length < 2 ^ (prefixWord ++ tailWord_582202).sum := by decide
  have hdescent : baseEnd_582202 < baseStart_582202 := by decide
  rcases family_descends (prefixWord ++ tailWord_582202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582221 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_582221 : Nat := 118140960795 + 582221 * 2 ^ 59
def prefixEnd_582221 : Nat := 4983230072969 + 3 ^ 40 * 582221 * 2
def baseEnd_582221 : Nat := 199306146760981194239947

theorem tailTrace_582221 : CollatzResearch.WordTrace tailWord_582221 prefixEnd_582221 199306146760981194239947 := by
  unfold tailWord_582221
  simp only [CollatzResearch.WordTrace]
  refine ⟨21235344423720227275450517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14156896282480151516967011 21235344423720227275450517)
  ·
    refine ⟨995406769861885653536743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21235344423720227275450517 995406769861885653536743)
    ·
      refine ⟨1493110154792828480305115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 995406769861885653536743 1493110154792828480305115)
      ·
        refine ⟨2239665232189242720457673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1493110154792828480305115 2239665232189242720457673)
        ·
          refine ⟨1679748924141932040343255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2239665232189242720457673 1679748924141932040343255)
          ·
            refine ⟨2519623386212898060514883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679748924141932040343255 2519623386212898060514883)
            ·
              refine ⟨3779435079319347090772325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519623386212898060514883 3779435079319347090772325)
              ·
                refine ⟨708644077372377579519811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3779435079319347090772325 708644077372377579519811)
                ·
                  refine ⟨1062966116058566369279717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708644077372377579519811 1062966116058566369279717)
                  ·
                    refine ⟨199306146760981194239947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1062966116058566369279717 199306146760981194239947)
                    ·
                      rfl

theorem cell22_582221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_582221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582221 prefixEnd_582221 := by exact prefixLift 582221
  have htrace : WordTrace (prefixWord ++ tailWord_582221) baseStart_582221 baseEnd_582221 := by
    simpa [prefixWord, tailWord_582221, baseEnd_582221] using wordTrace_append hprefix tailTrace_582221
  have hstable : (prefixWord ++ tailWord_582221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582221).length < 2 ^ (prefixWord ++ tailWord_582221).sum := by decide
  have hdescent : baseEnd_582221 < baseStart_582221 := by decide
  rcases family_descends (prefixWord ++ tailWord_582221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582232 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_582232 : Nat := 118140960795 + 582232 * 2 ^ 59
def prefixEnd_582232 : Nat := 4983230072969 + 3 ^ 40 * 582232 * 2
def baseEnd_582232 : Nat := 199309912285780832214913

theorem tailTrace_582232 : CollatzResearch.WordTrace tailWord_582232 prefixEnd_582232 199309912285780832214913 := by
  unfold tailWord_582232
  simp only [CollatzResearch.WordTrace]
  refine ⟨10617872813340188077050475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14157163751120250769400633 10617872813340188077050475)
  ·
    refine ⟨15926809220010282115575713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10617872813340188077050475 15926809220010282115575713)
    ·
      refine ⟨11945106915007711586681785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15926809220010282115575713 11945106915007711586681785)
      ·
        refine ⟨8958830186255783690011339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11945106915007711586681785 8958830186255783690011339)
        ·
          refine ⟨13438245279383675535017009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8958830186255783690011339 13438245279383675535017009)
          ·
            refine ⟨10078683959537756651262757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13438245279383675535017009 10078683959537756651262757)
            ·
              refine ⟨1889753242413329372111767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10078683959537756651262757 1889753242413329372111767)
              ·
                refine ⟨2834629863619994058167651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889753242413329372111767 2834629863619994058167651)
                ·
                  refine ⟨4251944795429991087251477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834629863619994058167651 4251944795429991087251477)
                  ·
                    refine ⟨199309912285780832214913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4251944795429991087251477 199309912285780832214913)
                    ·
                      rfl

theorem cell22_582232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_582232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582232 prefixEnd_582232 := by exact prefixLift 582232
  have htrace : WordTrace (prefixWord ++ tailWord_582232) baseStart_582232 baseEnd_582232 := by
    simpa [prefixWord, tailWord_582232, baseEnd_582232] using wordTrace_append hprefix tailTrace_582232
  have hstable : (prefixWord ++ tailWord_582232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582232).length < 2 ^ (prefixWord ++ tailWord_582232).sum := by decide
  have hdescent : baseEnd_582232 < baseStart_582232 := by decide
  rcases family_descends (prefixWord ++ tailWord_582232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582253 : List Nat := [1, 5, 1, 1, 3, 2, 3, 2, 4]
def baseStart_582253 : Nat := 118140960795 + 582253 * 2 ^ 59
def prefixEnd_582253 : Nat := 4983230072969 + 3 ^ 40 * 582253 * 2
def baseEnd_582253 : Nat := 66439033671647925813283

theorem tailTrace_582253 : CollatzResearch.WordTrace tailWord_582253 prefixEnd_582253 66439033671647925813283 := by
  unfold tailWord_582253
  simp only [CollatzResearch.WordTrace]
  refine ⟨21236511559604296740615413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14157674373069531160410275 21236511559604296740615413)
  ·
    refine ⟨1990922958712902819432695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21236511559604296740615413 1990922958712902819432695)
    ·
      refine ⟨2986384438069354229149043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1990922958712902819432695 2986384438069354229149043)
      ·
        refine ⟨4479576657104031343723565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2986384438069354229149043 4479576657104031343723565)
        ·
          refine ⟨1679841246414011753896337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4479576657104031343723565 1679841246414011753896337)
          ·
            refine ⟨1259880934810508815422253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1679841246414011753896337 1259880934810508815422253)
            ·
              refine ⟨472455350553940805783345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1259880934810508815422253 472455350553940805783345)
              ·
                refine ⟨354341512915455604337509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472455350553940805783345 354341512915455604337509)
                ·
                  refine ⟨66439033671647925813283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354341512915455604337509 66439033671647925813283)
                  ·
                    rfl

theorem cell22_582253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_582253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582253 prefixEnd_582253 := by exact prefixLift 582253
  have htrace : WordTrace (prefixWord ++ tailWord_582253) baseStart_582253 baseEnd_582253 := by
    simpa [prefixWord, tailWord_582253, baseEnd_582253] using wordTrace_append hprefix tailTrace_582253
  have hstable : (prefixWord ++ tailWord_582253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582253).length < 2 ^ (prefixWord ++ tailWord_582253).sum := by decide
  have hdescent : baseEnd_582253 < baseStart_582253 := by decide
  rcases family_descends (prefixWord ++ tailWord_582253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582279 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 5, 3]
def baseStart_582279 : Nat := 118140960795 + 582279 * 2 ^ 59
def prefixEnd_582279 : Nat := 4983230072969 + 3 ^ 40 * 582279 * 2
def baseEnd_582279 : Nat := 199326001346288376289769

theorem tailTrace_582279 : CollatzResearch.WordTrace tailWord_582279 prefixEnd_582279 199326001346288376289769 := by
  unfold tailWord_582279
  simp only [CollatzResearch.WordTrace]
  refine ⟨21237459857510103181061891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14158306571673402120707927 21237459857510103181061891)
  ·
    refine ⟨31856189786265154771592837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21237459857510103181061891 31856189786265154771592837)
    ·
      refine ⟨5973035584924716519673657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31856189786265154771592837 5973035584924716519673657)
      ·
        refine ⟨4479776688693537389755243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5973035584924716519673657 4479776688693537389755243)
        ·
          refine ⟨6719665033040306084632865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4479776688693537389755243 6719665033040306084632865)
          ·
            refine ⟨5039748774780229563474649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6719665033040306084632865 5039748774780229563474649)
            ·
              refine ⟨3779811581085172172605987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5039748774780229563474649 3779811581085172172605987)
              ·
                refine ⟨5669717371627758258908981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3779811581085172172605987 5669717371627758258908981)
                ·
                  refine ⟨531536003590102336772717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5669717371627758258908981 531536003590102336772717)
                  ·
                    refine ⟨199326001346288376289769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 531536003590102336772717 199326001346288376289769)
                    ·
                      rfl

theorem cell22_582279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_582279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582279 prefixEnd_582279 := by exact prefixLift 582279
  have htrace : WordTrace (prefixWord ++ tailWord_582279) baseStart_582279 baseEnd_582279 := by
    simpa [prefixWord, tailWord_582279, baseEnd_582279] using wordTrace_append hprefix tailTrace_582279
  have hstable : (prefixWord ++ tailWord_582279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582279).length < 2 ^ (prefixWord ++ tailWord_582279).sum := by decide
  have hdescent : baseEnd_582279 < baseStart_582279 := by decide
  rcases family_descends (prefixWord ++ tailWord_582279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582352 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_582352 : Nat := 118140960795 + 582352 * 2 ^ 59
def prefixEnd_582352 : Nat := 4983230072969 + 3 ^ 40 * 582352 * 2
def baseEnd_582352 : Nat := 199350990738140519214545

theorem tailTrace_582352 : CollatzResearch.WordTrace tailWord_582352 prefixEnd_582352 199350990738140519214545 := by
  unfold tailWord_582352
  simp only [CollatzResearch.WordTrace]
  refine ⟨10620061193122818324234655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14160081590830424432312873 10620061193122818324234655)
  ·
    refine ⟨15930091789684227486351983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10620061193122818324234655 15930091789684227486351983)
    ·
      refine ⟨23895137684526341229527975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15930091789684227486351983 23895137684526341229527975)
      ·
        refine ⟨35842706526789511844291963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23895137684526341229527975 35842706526789511844291963)
        ·
          refine ⟨53764059790184267766437945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35842706526789511844291963 53764059790184267766437945)
          ·
            refine ⟨40323044842638200824828459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53764059790184267766437945 40323044842638200824828459)
            ·
              refine ⟨60484567263957301237242689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40323044842638200824828459 60484567263957301237242689)
              ·
                refine ⟨45363425447967975927932017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60484567263957301237242689 45363425447967975927932017)
                ·
                  refine ⟨34022569085975981945949013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45363425447967975927932017 34022569085975981945949013)
                  ·
                    refine ⟨199350990738140519214545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 34022569085975981945949013 199350990738140519214545)
                    ·
                      rfl

theorem cell22_582352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_582352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582352 prefixEnd_582352 := by exact prefixLift 582352
  have htrace : WordTrace (prefixWord ++ tailWord_582352) baseStart_582352 baseEnd_582352 := by
    simpa [prefixWord, tailWord_582352, baseEnd_582352] using wordTrace_append hprefix tailTrace_582352
  have hstable : (prefixWord ++ tailWord_582352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582352).length < 2 ^ (prefixWord ++ tailWord_582352).sum := by decide
  have hdescent : baseEnd_582352 < baseStart_582352 := by decide
  rcases family_descends (prefixWord ++ tailWord_582352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582371 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 6]
def baseStart_582371 : Nat := 118140960795 + 582371 * 2 ^ 59
def prefixEnd_582371 : Nat := 4983230072969 + 3 ^ 40 * 582371 * 2
def baseEnd_582371 : Nat := 66452498275476934329829

theorem tailTrace_582371 : CollatzResearch.WordTrace tailWord_582371 prefixEnd_582371 66452498275476934329829 := by
  unfold tailWord_582371
  simp only [CollatzResearch.WordTrace]
  refine ⟨21240815373176802893410967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14160543582117868595607311 21240815373176802893410967)
  ·
    refine ⟨31861223059765204340116451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21240815373176802893410967 31861223059765204340116451)
    ·
      refine ⟨47791834589647806510174677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31861223059765204340116451 47791834589647806510174677)
      ·
        refine ⟨1120121123194870465082219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 47791834589647806510174677 1120121123194870465082219)
        ·
          refine ⟨1680181684792305697623329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1120121123194870465082219 1680181684792305697623329)
          ·
            refine ⟨1260136263594229273217497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1680181684792305697623329 1260136263594229273217497)
            ·
              refine ⟨945102197695671954913123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1260136263594229273217497 945102197695671954913123)
              ·
                refine ⟨1417653296543507932369685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945102197695671954913123 1417653296543507932369685)
                ·
                  refine ⟨66452498275476934329829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1417653296543507932369685 66452498275476934329829)
                  ·
                    rfl

theorem cell22_582371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 6].length) (baseStart_582371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582371 prefixEnd_582371 := by exact prefixLift 582371
  have htrace : WordTrace (prefixWord ++ tailWord_582371) baseStart_582371 baseEnd_582371 := by
    simpa [prefixWord, tailWord_582371, baseEnd_582371] using wordTrace_append hprefix tailTrace_582371
  have hstable : (prefixWord ++ tailWord_582371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582371).length < 2 ^ (prefixWord ++ tailWord_582371).sum := by decide
  have hdescent : baseEnd_582371 < baseStart_582371 := by decide
  rcases family_descends (prefixWord ++ tailWord_582371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582386 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_582386 : Nat := 118140960795 + 582386 * 2 ^ 59
def prefixEnd_582386 : Nat := 4983230072969 + 3 ^ 40 * 582386 * 2
def baseEnd_582386 : Nat := 199362629632975763864441

theorem tailTrace_582386 : CollatzResearch.WordTrace tailWord_582386 prefixEnd_582386 199362629632975763864441 := by
  unfold tailWord_582386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5310340617030615113801753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14160908312081640303471341 5310340617030615113801753)
  ·
    refine ⟨3982755462772961335351315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5310340617030615113801753 3982755462772961335351315)
    ·
      refine ⟨5974133194159442003026973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3982755462772961335351315 5974133194159442003026973)
      ·
        refine ⟨2240299947809790751135115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5974133194159442003026973 2240299947809790751135115)
        ·
          refine ⟨3360449921714686126702673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240299947809790751135115 3360449921714686126702673)
          ·
            refine ⟨2520337441286014595027005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3360449921714686126702673 2520337441286014595027005)
            ·
              refine ⟨945126540482255473135127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2520337441286014595027005 945126540482255473135127)
              ·
                refine ⟨1417689810723383209702691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945126540482255473135127 1417689810723383209702691)
                ·
                  refine ⟨2126534716085074814554037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417689810723383209702691 2126534716085074814554037)
                  ·
                    refine ⟨199362629632975763864441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2126534716085074814554037 199362629632975763864441)
                    ·
                      rfl

theorem cell22_582386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_582386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582386 prefixEnd_582386 := by exact prefixLift 582386
  have htrace : WordTrace (prefixWord ++ tailWord_582386) baseStart_582386 baseEnd_582386 := by
    simpa [prefixWord, tailWord_582386, baseEnd_582386] using wordTrace_append hprefix tailTrace_582386
  have hstable : (prefixWord ++ tailWord_582386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582386).length < 2 ^ (prefixWord ++ tailWord_582386).sum := by decide
  have hdescent : baseEnd_582386 < baseStart_582386 := by decide
  rcases family_descends (prefixWord ++ tailWord_582386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582521 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_582521 : Nat := 118140960795 + 582521 * 2 ^ 59
def prefixEnd_582521 : Nat := 4983230072969 + 3 ^ 40 * 582521 * 2
def baseEnd_582521 : Nat := 199408842891880411739027

theorem tailTrace_582521 : CollatzResearch.WordTrace tailWord_582521 prefixEnd_582521 199408842891880411739027 := by
  unfold tailWord_582521
  simp only [CollatzResearch.WordTrace]
  refine ⟨21246286322633378511371417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14164190881755585674247611 21246286322633378511371417)
  ·
    refine ⟨15934714741975033883528563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21246286322633378511371417 15934714741975033883528563)
    ·
      refine ⟨23902072112962550825292845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15934714741975033883528563 23902072112962550825292845)
      ·
        refine ⟨8963277042360956559484817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23902072112962550825292845 8963277042360956559484817)
        ·
          refine ⟨6722457781770717419613613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8963277042360956559484817 6722457781770717419613613)
          ·
            refine ⟨2520921668164019032355105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6722457781770717419613613 2520921668164019032355105)
            ·
              refine ⟨1890691251123014274266329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2520921668164019032355105 1890691251123014274266329)
              ·
                refine ⟨1418018438342260705699747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890691251123014274266329 1418018438342260705699747)
                ·
                  refine ⟨2127027657513391058549621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418018438342260705699747 2127027657513391058549621)
                  ·
                    refine ⟨199408842891880411739027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2127027657513391058549621 199408842891880411739027)
                    ·
                      rfl

theorem cell22_582521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_582521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582521 prefixEnd_582521 := by exact prefixLift 582521
  have htrace : WordTrace (prefixWord ++ tailWord_582521) baseStart_582521 baseEnd_582521 := by
    simpa [prefixWord, tailWord_582521, baseEnd_582521] using wordTrace_append hprefix tailTrace_582521
  have hstable : (prefixWord ++ tailWord_582521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582521).length < 2 ^ (prefixWord ++ tailWord_582521).sum := by decide
  have hdescent : baseEnd_582521 < baseStart_582521 := by decide
  rcases family_descends (prefixWord ++ tailWord_582521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582692 : List Nat := [2, 3, 1, 4, 1, 2, 2, 3, 4]
def baseStart_582692 : Nat := 118140960795 + 582692 * 2 ^ 59
def prefixEnd_582692 : Nat := 4983230072969 + 3 ^ 40 * 582692 * 2
def baseEnd_582692 : Nat := 66489126562164321904501

theorem tailTrace_582692 : CollatzResearch.WordTrace tailWord_582692 prefixEnd_582692 66489126562164321904501 := by
  unfold tailWord_582692
  simp only [CollatzResearch.WordTrace]
  refine ⟨10626261602506937357923165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14168348803342583143897553 10626261602506937357923165)
  ·
    refine ⟨3984848100940101509221187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10626261602506937357923165 3984848100940101509221187)
    ·
      refine ⟨5977272151410152263831781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3984848100940101509221187 5977272151410152263831781)
      ·
        refine ⟨1120738528389403549468459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5977272151410152263831781 1120738528389403549468459)
        ·
          refine ⟨1681107792584105324202689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1120738528389403549468459 1681107792584105324202689)
          ·
            refine ⟨1260830844438078993152017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1681107792584105324202689 1260830844438078993152017)
            ·
              refine ⟨945623133328559244864013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1260830844438078993152017 945623133328559244864013)
              ·
                refine ⟨354608674998209716824005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 945623133328559244864013 354608674998209716824005)
                ·
                  refine ⟨66489126562164321904501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354608674998209716824005 66489126562164321904501)
                  ·
                    rfl

theorem cell22_582692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_582692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582692 prefixEnd_582692 := by exact prefixLift 582692
  have htrace : WordTrace (prefixWord ++ tailWord_582692) baseStart_582692 baseEnd_582692 := by
    simpa [prefixWord, tailWord_582692, baseEnd_582692] using wordTrace_append hprefix tailTrace_582692
  have hstable : (prefixWord ++ tailWord_582692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582692).length < 2 ^ (prefixWord ++ tailWord_582692).sum := by decide
  have hdescent : baseEnd_582692 < baseStart_582692 := by decide
  rcases family_descends (prefixWord ++ tailWord_582692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582731 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 11]
def baseStart_582731 : Nat := 118140960795 + 582731 * 2 ^ 59
def prefixEnd_582731 : Nat := 4983230072969 + 3 ^ 40 * 582731 * 2
def baseEnd_582731 : Nat := 66493576727836621329461

theorem tailTrace_582731 : CollatzResearch.WordTrace tailWord_582731 prefixEnd_582731 66493576727836621329461 := by
  unfold tailWord_582731
  simp only [CollatzResearch.WordTrace]
  refine ⟨21253945651872584376516047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14169297101248389584344031 21253945651872584376516047)
  ·
    refine ⟨31880918477808876564774071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21253945651872584376516047 31880918477808876564774071)
    ·
      refine ⟨47821377716713314847161107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31880918477808876564774071 47821377716713314847161107)
      ·
        refine ⟨71732066575069972270741661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47821377716713314847161107 71732066575069972270741661)
        ·
          refine ⟨26899524965651239601528123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71732066575069972270741661 26899524965651239601528123)
          ·
            refine ⟨40349287448476859402292185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26899524965651239601528123 40349287448476859402292185)
            ·
              refine ⟨30261965586357644551719139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40349287448476859402292185 30261965586357644551719139)
              ·
                refine ⟨45392948379536466827578709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30261965586357644551719139 45392948379536466827578709)
                ·
                  refine ⟨66493576727836621329461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 45392948379536466827578709 66493576727836621329461)
                  ·
                    rfl

theorem cell22_582731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 11].length) (baseStart_582731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582731 prefixEnd_582731 := by exact prefixLift 582731
  have htrace : WordTrace (prefixWord ++ tailWord_582731) baseStart_582731 baseEnd_582731 := by
    simpa [prefixWord, tailWord_582731, baseEnd_582731] using wordTrace_append hprefix tailTrace_582731
  have hstable : (prefixWord ++ tailWord_582731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582731).length < 2 ^ (prefixWord ++ tailWord_582731).sum := by decide
  have hdescent : baseEnd_582731 < baseStart_582731 := by decide
  rcases family_descends (prefixWord ++ tailWord_582731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582748 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 9]
def baseStart_582748 : Nat := 118140960795 + 582748 * 2 ^ 59
def prefixEnd_582748 : Nat := 4983230072969 + 3 ^ 40 * 582748 * 2
def baseEnd_582748 : Nat := 66495516543642495437777

theorem tailTrace_582748 : CollatzResearch.WordTrace tailWord_582748 prefixEnd_582748 66495516543642495437777 := by
  unfold tailWord_582748
  simp only [CollatzResearch.WordTrace]
  refine ⟨10627282846405498139942449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14169710461873997519923265 10627282846405498139942449)
  ·
    refine ⟨7970462134804123604956837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10627282846405498139942449 7970462134804123604956837)
    ·
      refine ⟨1494461650275773175929407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7970462134804123604956837 1494461650275773175929407)
      ·
        refine ⟨2241692475413659763894111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494461650275773175929407 2241692475413659763894111)
        ·
          refine ⟨3362538713120489645841167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2241692475413659763894111 3362538713120489645841167)
          ·
            refine ⟨5043808069680734468761751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362538713120489645841167 5043808069680734468761751)
            ·
              refine ⟨7565712104521101703142627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5043808069680734468761751 7565712104521101703142627)
              ·
                refine ⟨11348568156781652554713941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7565712104521101703142627 11348568156781652554713941)
                ·
                  refine ⟨66495516543642495437777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11348568156781652554713941 66495516543642495437777)
                  ·
                    rfl

theorem cell22_582748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_582748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582748 prefixEnd_582748 := by exact prefixLift 582748
  have htrace : WordTrace (prefixWord ++ tailWord_582748) baseStart_582748 baseEnd_582748 := by
    simpa [prefixWord, tailWord_582748, baseEnd_582748] using wordTrace_append hprefix tailTrace_582748
  have hstable : (prefixWord ++ tailWord_582748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582748).length < 2 ^ (prefixWord ++ tailWord_582748).sum := by decide
  have hdescent : baseEnd_582748 < baseStart_582748 := by decide
  rcases family_descends (prefixWord ++ tailWord_582748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582960 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_582960 : Nat := 118140960795 + 582960 * 2 ^ 59
def prefixEnd_582960 : Nat := 4983230072969 + 3 ^ 40 * 582960 * 2
def baseEnd_582960 : Nat := 199559121563429600012681

theorem tailTrace_582960 : CollatzResearch.WordTrace tailWord_582960 prefixEnd_582960 199559121563429600012681 := by
  unfold tailWord_582960
  simp only [CollatzResearch.WordTrace]
  refine ⟨10631148984021478243301167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14174865312028637657734889 10631148984021478243301167)
  ·
    refine ⟨15946723476032217364951751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10631148984021478243301167 15946723476032217364951751)
    ·
      refine ⟨23920085214048326047427627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15946723476032217364951751 23920085214048326047427627)
      ·
        refine ⟨35880127821072489071141441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23920085214048326047427627 35880127821072489071141441)
        ·
          refine ⟨26910095865804366803356081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35880127821072489071141441 26910095865804366803356081)
          ·
            refine ⟨20182571899353275102517061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26910095865804366803356081 20182571899353275102517061)
            ·
              refine ⟨3784232231128739081721949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20182571899353275102517061 3784232231128739081721949)
              ·
                refine ⟨1419087086673277155645731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3784232231128739081721949 1419087086673277155645731)
                ·
                  refine ⟨2128630630009915733468597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419087086673277155645731 2128630630009915733468597)
                  ·
                    refine ⟨199559121563429600012681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2128630630009915733468597 199559121563429600012681)
                    ·
                      rfl

theorem cell22_582960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_582960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582960 prefixEnd_582960 := by exact prefixLift 582960
  have htrace : WordTrace (prefixWord ++ tailWord_582960) baseStart_582960 baseEnd_582960 := by
    simpa [prefixWord, tailWord_582960, baseEnd_582960] using wordTrace_append hprefix tailTrace_582960
  have hstable : (prefixWord ++ tailWord_582960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582960).length < 2 ^ (prefixWord ++ tailWord_582960).sum := by decide
  have hdescent : baseEnd_582960 < baseStart_582960 := by decide
  rcases family_descends (prefixWord ++ tailWord_582960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582977 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_582977 : Nat := 118140960795 + 582977 * 2 ^ 59
def prefixEnd_582977 : Nat := 4983230072969 + 3 ^ 40 * 582977 * 2
def baseEnd_582977 : Nat := 199564941010847222337629

theorem tailTrace_582977 : CollatzResearch.WordTrace tailWord_582977 prefixEnd_582977 199564941010847222337629 := by
  unfold tailWord_582977
  simp only [CollatzResearch.WordTrace]
  refine ⟨21262918008981368389971185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14175278672654245593314123 21262918008981368389971185)
  ·
    refine ⟨15947188506736026292478389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21262918008981368389971185 15947188506736026292478389)
    ·
      refine ⟨1495048922506502464919849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15947188506736026292478389 1495048922506502464919849)
      ·
        refine ⟨1121286691879876848689887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1495048922506502464919849 1121286691879876848689887)
        ·
          refine ⟨1681930037819815273034831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1121286691879876848689887 1681930037819815273034831)
          ·
            refine ⟨2522895056729722909552247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681930037819815273034831 2522895056729722909552247)
            ·
              refine ⟨3784342585094584364328371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2522895056729722909552247 3784342585094584364328371)
              ·
                refine ⟨5676513877641876546492557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784342585094584364328371 5676513877641876546492557)
                ·
                  refine ⟨2128692704115703704934709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5676513877641876546492557 2128692704115703704934709)
                  ·
                    refine ⟨199564941010847222337629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2128692704115703704934709 199564941010847222337629)
                    ·
                      rfl

theorem cell22_582977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_582977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_582977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_582977 prefixEnd_582977 := by exact prefixLift 582977
  have htrace : WordTrace (prefixWord ++ tailWord_582977) baseStart_582977 baseEnd_582977 := by
    simpa [prefixWord, tailWord_582977, baseEnd_582977] using wordTrace_append hprefix tailTrace_582977
  have hstable : (prefixWord ++ tailWord_582977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582977).length < 2 ^ (prefixWord ++ tailWord_582977).sum := by decide
  have hdescent : baseEnd_582977 < baseStart_582977 := by decide
  rcases family_descends (prefixWord ++ tailWord_582977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583035 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 7]
def baseStart_583035 : Nat := 118140960795 + 583035 * 2 ^ 59
def prefixEnd_583035 : Nat := 4983230072969 + 3 ^ 40 * 583035 * 2
def baseEnd_583035 : Nat := 66528265198718134795817

theorem tailTrace_583035 : CollatzResearch.WordTrace tailWord_583035 prefixEnd_583035 66528265198718134795817 := by
  unfold tailWord_583035
  simp only [CollatzResearch.WordTrace]
  refine ⟨21265033442771244295582559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14176688961847496197055039 21265033442771244295582559)
  ·
    refine ⟨31897550164156866443373839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21265033442771244295582559 31897550164156866443373839)
    ·
      refine ⟨47846325246235299665060759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31897550164156866443373839 47846325246235299665060759)
      ·
        refine ⟨71769487869352949497591139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47846325246235299665060759 71769487869352949497591139)
        ·
          refine ⟨107654231804029424246386709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71769487869352949497591139 107654231804029424246386709)
          ·
            refine ⟨5046292115813879261549377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107654231804029424246386709 5046292115813879261549377)
            ·
              refine ⟨3784719086860409446162033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5046292115813879261549377 3784719086860409446162033)
              ·
                refine ⟨2838539315145307084621525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3784719086860409446162033 2838539315145307084621525)
                ·
                  refine ⟨66528265198718134795817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2838539315145307084621525 66528265198718134795817)
                  ·
                    rfl

theorem cell22_583035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 7].length) (baseStart_583035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583035 prefixEnd_583035 := by exact prefixLift 583035
  have htrace : WordTrace (prefixWord ++ tailWord_583035) baseStart_583035 baseEnd_583035 := by
    simpa [prefixWord, tailWord_583035, baseEnd_583035] using wordTrace_append hprefix tailTrace_583035
  have hstable : (prefixWord ++ tailWord_583035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583035).length < 2 ^ (prefixWord ++ tailWord_583035).sum := by decide
  have hdescent : baseEnd_583035 < baseStart_583035 := by decide
  rcases family_descends (prefixWord ++ tailWord_583035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583114 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_583114 : Nat := 118140960795 + 583114 * 2 ^ 59
def prefixEnd_583114 : Nat := 4983230072969 + 3 ^ 40 * 583114 * 2
def baseEnd_583114 : Nat := 66537279636874843887403

theorem tailTrace_583114 : CollatzResearch.WordTrace tailWord_583114 prefixEnd_583114 66537279636874843887403 := by
  unfold tailWord_583114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5316978702371260196927099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14178609872990027191805597 5316978702371260196927099)
  ·
    refine ⟨7975468053556890295390649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5316978702371260196927099 7975468053556890295390649)
    ·
      refine ⟨5981601040167667721542987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7975468053556890295390649 5981601040167667721542987)
      ·
        refine ⟨8972401560251501582314481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5981601040167667721542987 8972401560251501582314481)
        ·
          refine ⟨6729301170188626186735861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8972401560251501582314481 6729301170188626186735861)
          ·
            refine ⟨630871984705183705006487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6729301170188626186735861 630871984705183705006487)
            ·
              refine ⟨946307977057775557509731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630871984705183705006487 946307977057775557509731)
              ·
                refine ⟨1419461965586663336264597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946307977057775557509731 1419461965586663336264597)
                ·
                  refine ⟨66537279636874843887403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1419461965586663336264597 66537279636874843887403)
                  ·
                    rfl

theorem cell22_583114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_583114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583114 prefixEnd_583114 := by exact prefixLift 583114
  have htrace : WordTrace (prefixWord ++ tailWord_583114) baseStart_583114 baseEnd_583114 := by
    simpa [prefixWord, tailWord_583114, baseEnd_583114] using wordTrace_append hprefix tailTrace_583114
  have hstable : (prefixWord ++ tailWord_583114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583114).length < 2 ^ (prefixWord ++ tailWord_583114).sum := by decide
  have hdescent : baseEnd_583114 < baseStart_583114 := by decide
  rcases family_descends (prefixWord ++ tailWord_583114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583144 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 2, 4]
def baseStart_583144 : Nat := 118140960795 + 583144 * 2 ^ 59
def prefixEnd_583144 : Nat := 4983230072969 + 3 ^ 40 * 583144 * 2
def baseEnd_583144 : Nat := 199622108523714453412117

theorem tailTrace_583144 : CollatzResearch.WordTrace tailWord_583144 prefixEnd_583144 199622108523714453412117 := by
  unfold tailWord_583144
  simp only [CollatzResearch.WordTrace]
  refine ⟨10634504499688177955650243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14179339332917570607533657 10634504499688177955650243)
  ·
    refine ⟨15951756749532266933475365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10634504499688177955650243 15951756749532266933475365)
    ·
      refine ⟨2990954390537300050026631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15951756749532266933475365 2990954390537300050026631)
      ·
        refine ⟨4486431585805950075039947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2990954390537300050026631 4486431585805950075039947)
        ·
          refine ⟨6729647378708925112559921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4486431585805950075039947 6729647378708925112559921)
          ·
            refine ⟨5047235534031693834419941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6729647378708925112559921 5047235534031693834419941)
            ·
              refine ⟨946356662630942593953739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5047235534031693834419941 946356662630942593953739)
              ·
                refine ⟨1419534993946413890930609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946356662630942593953739 1419534993946413890930609)
                ·
                  refine ⟨1064651245459810418197957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1419534993946413890930609 1064651245459810418197957)
                  ·
                    refine ⟨199622108523714453412117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1064651245459810418197957 199622108523714453412117)
                    ·
                      rfl

theorem cell22_583144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_583144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583144 prefixEnd_583144 := by exact prefixLift 583144
  have htrace : WordTrace (prefixWord ++ tailWord_583144) baseStart_583144 baseEnd_583144 := by
    simpa [prefixWord, tailWord_583144, baseEnd_583144] using wordTrace_append hprefix tailTrace_583144
  have hstable : (prefixWord ++ tailWord_583144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583144).length < 2 ^ (prefixWord ++ tailWord_583144).sum := by decide
  have hdescent : baseEnd_583144 < baseStart_583144 := by decide
  rcases family_descends (prefixWord ++ tailWord_583144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583221 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 5]
def baseStart_583221 : Nat := 118140960795 + 583221 * 2 ^ 59
def prefixEnd_583221 : Nat := 4983230072969 + 3 ^ 40 * 583221 * 2
def baseEnd_583221 : Nat := 66549489065770639745627

theorem tailTrace_583221 : CollatzResearch.WordTrace tailWord_583221 prefixEnd_583221 66549489065770639745627 := by
  unfold tailWord_583221
  simp only [CollatzResearch.WordTrace]
  refine ⟨21271817420097398061853517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14181211613398265374569011 21271817420097398061853517)
  ·
    refine ⟨7976931532536524273195069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21271817420097398061853517 7976931532536524273195069)
    ·
      refine ⟨2991349324701196602448151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7976931532536524273195069 2991349324701196602448151)
      ·
        refine ⟨4487023987051794903672227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2991349324701196602448151 4487023987051794903672227)
        ·
          refine ⟨6730535980577692355508341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4487023987051794903672227 6730535980577692355508341)
          ·
            refine ⟨630987748179158658328907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6730535980577692355508341 630987748179158658328907)
            ·
              refine ⟨946481622268737987493361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630987748179158658328907 946481622268737987493361)
              ·
                refine ⟨709861216701553490620021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946481622268737987493361 709861216701553490620021)
                ·
                  refine ⟨66549489065770639745627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 709861216701553490620021 66549489065770639745627)
                  ·
                    rfl

theorem cell22_583221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_583221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583221 prefixEnd_583221 := by exact prefixLift 583221
  have htrace : WordTrace (prefixWord ++ tailWord_583221) baseStart_583221 baseEnd_583221 := by
    simpa [prefixWord, tailWord_583221, baseEnd_583221] using wordTrace_append hprefix tailTrace_583221
  have hstable : (prefixWord ++ tailWord_583221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583221).length < 2 ^ (prefixWord ++ tailWord_583221).sum := by decide
  have hdescent : baseEnd_583221 < baseStart_583221 := by decide
  rcases family_descends (prefixWord ++ tailWord_583221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583343 : List Nat := [1, 1, 2, 1, 2, 4, 3, 4, 1, 3]
def baseStart_583343 : Nat := 118140960795 + 583343 * 2 ^ 59
def prefixEnd_583343 : Nat := 4983230072969 + 3 ^ 40 * 583343 * 2
def baseEnd_583343 : Nat := 199690230290544267686507

theorem tailTrace_583343 : CollatzResearch.WordTrace tailWord_583343 prefixEnd_583343 199690230290544267686507 := by
  unfold tailWord_583343
  simp only [CollatzResearch.WordTrace]
  refine ⟨21276267125655412897794683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14184178083770275265196455 21276267125655412897794683)
  ·
    refine ⟨31914400688483119346692025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21276267125655412897794683 31914400688483119346692025)
    ·
      refine ⟨23935800516362339510019019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31914400688483119346692025 23935800516362339510019019)
      ·
        refine ⟨35903700774543509265028529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23935800516362339510019019 35903700774543509265028529)
        ·
          refine ⟨26927775580907631948771397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35903700774543509265028529 26927775580907631948771397)
          ·
            refine ⟨5048957921420180990394637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26927775580907631948771397 5048957921420180990394637)
            ·
              refine ⟨1893359220532567871397989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5048957921420180990394637 1893359220532567871397989)
              ·
                refine ⟨355004853849856475887123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1893359220532567871397989 355004853849856475887123)
                ·
                  refine ⟨532507280774784713830685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355004853849856475887123 532507280774784713830685)
                  ·
                    refine ⟨199690230290544267686507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 532507280774784713830685 199690230290544267686507)
                    ·
                      rfl

theorem cell22_583343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 1, 3].length) (baseStart_583343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583343 prefixEnd_583343 := by exact prefixLift 583343
  have htrace : WordTrace (prefixWord ++ tailWord_583343) baseStart_583343 baseEnd_583343 := by
    simpa [prefixWord, tailWord_583343, baseEnd_583343] using wordTrace_append hprefix tailTrace_583343
  have hstable : (prefixWord ++ tailWord_583343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583343).length < 2 ^ (prefixWord ++ tailWord_583343).sum := by decide
  have hdescent : baseEnd_583343 < baseStart_583343 := by decide
  rcases family_descends (prefixWord ++ tailWord_583343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583354 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_583354 : Nat := 118140960795 + 583354 * 2 ^ 59
def prefixEnd_583354 : Nat := 4983230072969 + 3 ^ 40 * 583354 * 2
def baseEnd_583354 : Nat := 199693995815343905661473

theorem tailTrace_583354 : CollatzResearch.WordTrace tailWord_583354 prefixEnd_583354 199693995815343905661473 := by
  unfold tailWord_583354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5319167082153890444111279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14184445552410374517630077 5319167082153890444111279)
  ·
    refine ⟨7978750623230835666166919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5319167082153890444111279 7978750623230835666166919)
    ·
      refine ⟨11968125934846253499250379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7978750623230835666166919 11968125934846253499250379)
      ·
        refine ⟨17952188902269380248875569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11968125934846253499250379 17952188902269380248875569)
        ·
          refine ⟨13464141676702035186656677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17952188902269380248875569 13464141676702035186656677)
          ·
            refine ⟨2524526564381631597498127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13464141676702035186656677 2524526564381631597498127)
            ·
              refine ⟨3786789846572447396247191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2524526564381631597498127 3786789846572447396247191)
              ·
                refine ⟨5680184769858671094370787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3786789846572447396247191 5680184769858671094370787)
                ·
                  refine ⟨8520277154788006641556181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5680184769858671094370787 8520277154788006641556181)
                  ·
                    refine ⟨199693995815343905661473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8520277154788006641556181 199693995815343905661473)
                    ·
                      rfl

theorem cell22_583354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_583354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583354 prefixEnd_583354 := by exact prefixLift 583354
  have htrace : WordTrace (prefixWord ++ tailWord_583354) baseStart_583354 baseEnd_583354 := by
    simpa [prefixWord, tailWord_583354, baseEnd_583354] using wordTrace_append hprefix tailTrace_583354
  have hstable : (prefixWord ++ tailWord_583354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583354).length < 2 ^ (prefixWord ++ tailWord_583354).sum := by decide
  have hdescent : baseEnd_583354 < baseStart_583354 := by decide
  rcases family_descends (prefixWord ++ tailWord_583354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583356 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 5]
def baseStart_583356 : Nat := 118140960795 + 583356 * 2 ^ 59
def prefixEnd_583356 : Nat := 4983230072969 + 3 ^ 40 * 583356 * 2
def baseEnd_583356 : Nat := 66564893485405522370489

theorem tailTrace_583356 : CollatzResearch.WordTrace tailWord_583356 prefixEnd_583356 66564893485405522370489 := by
  unfold tailWord_583356
  simp only [CollatzResearch.WordTrace]
  refine ⟨10638370637304158059008961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14184494183072210745345281 10638370637304158059008961)
  ·
    refine ⟨7978777977978118544256721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10638370637304158059008961 7978777977978118544256721)
    ·
      refine ⟨5984083483483588908192541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7978777977978118544256721 5984083483483588908192541)
      ·
        refine ⟨2244031306306345840572203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5984083483483588908192541 2244031306306345840572203)
        ·
          refine ⟨3366046959459518760858305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2244031306306345840572203 3366046959459518760858305)
          ·
            refine ⟨2524535219594639070643729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3366046959459518760858305 2524535219594639070643729)
            ·
              refine ⟨1893401414695979302982797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2524535219594639070643729 1893401414695979302982797)
              ·
                refine ⟨710025530510992238618549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1893401414695979302982797 710025530510992238618549)
                ·
                  refine ⟨66564893485405522370489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 710025530510992238618549 66564893485405522370489)
                  ·
                    rfl

theorem cell22_583356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_583356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583356 prefixEnd_583356 := by exact prefixLift 583356
  have htrace : WordTrace (prefixWord ++ tailWord_583356) baseStart_583356 baseEnd_583356 := by
    simpa [prefixWord, tailWord_583356, baseEnd_583356] using wordTrace_append hprefix tailTrace_583356
  have hstable : (prefixWord ++ tailWord_583356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583356).length < 2 ^ (prefixWord ++ tailWord_583356).sum := by decide
  have hdescent : baseEnd_583356 < baseStart_583356 := by decide
  rcases family_descends (prefixWord ++ tailWord_583356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583362 : List Nat := [3, 5, 1, 2, 1, 1, 3, 6]
def baseStart_583362 : Nat := 118140960795 + 583362 * 2 ^ 59
def prefixEnd_583362 : Nat := 4983230072969 + 3 ^ 40 * 583362 * 2
def baseEnd_583362 : Nat := 22188526042092727940161

theorem tailTrace_583362 : CollatzResearch.WordTrace tailWord_583362 prefixEnd_583362 22188526042092727940161 := by
  unfold tailWord_583362
  simp only [CollatzResearch.WordTrace]
  refine ⟨5319240028146644785684085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14184640075057719428490893 5319240028146644785684085)
  ·
    refine ⟨498678752638747948657883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5319240028146644785684085 498678752638747948657883)
    ·
      refine ⟨748018128958121922986825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 498678752638747948657883 748018128958121922986825)
      ·
        refine ⟨561013596718591442240119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 748018128958121922986825 561013596718591442240119)
        ·
          refine ⟨841520395077887163360179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561013596718591442240119 841520395077887163360179)
          ·
            refine ⟨1262280592616830745040269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841520395077887163360179 1262280592616830745040269)
            ·
              refine ⟨473355222231311529390101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1262280592616830745040269 473355222231311529390101)
              ·
                refine ⟨22188526042092727940161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 473355222231311529390101 22188526042092727940161)
                ·
                  rfl

theorem cell22_583362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_583362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583362 prefixEnd_583362 := by exact prefixLift 583362
  have htrace : WordTrace (prefixWord ++ tailWord_583362) baseStart_583362 baseEnd_583362 := by
    simpa [prefixWord, tailWord_583362, baseEnd_583362] using wordTrace_append hprefix tailTrace_583362
  have hstable : (prefixWord ++ tailWord_583362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583362).length < 2 ^ (prefixWord ++ tailWord_583362).sum := by decide
  have hdescent : baseEnd_583362 < baseStart_583362 := by decide
  rcases family_descends (prefixWord ++ tailWord_583362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583384 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 8]
def baseStart_583384 : Nat := 118140960795 + 583384 * 2 ^ 59
def prefixEnd_583384 : Nat := 4983230072969 + 3 ^ 40 * 583384 * 2
def baseEnd_583384 : Nat := 66568088476144609137127

theorem tailTrace_583384 : CollatzResearch.WordTrace tailWord_583384 prefixEnd_583384 66568088476144609137127 := by
  unfold tailWord_583384
  simp only [CollatzResearch.WordTrace]
  refine ⟨10638881259253438450018603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14185175012337917933358137 10638881259253438450018603)
  ·
    refine ⟨15958321888880157675027905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10638881259253438450018603 15958321888880157675027905)
    ·
      refine ⟨11968741416660118256270929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15958321888880157675027905 11968741416660118256270929)
      ·
        refine ⟨8976556062495088692203197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11968741416660118256270929 8976556062495088692203197)
        ·
          refine ⟨3366208523435658259576199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8976556062495088692203197 3366208523435658259576199)
          ·
            refine ⟨5049312785153487389364299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3366208523435658259576199 5049312785153487389364299)
            ·
              refine ⟨7573969177730231084046449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049312785153487389364299 7573969177730231084046449)
              ·
                refine ⟨5680476883297673313034837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7573969177730231084046449 5680476883297673313034837)
                ·
                  refine ⟨66568088476144609137127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5680476883297673313034837 66568088476144609137127)
                  ·
                    rfl

theorem cell22_583384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_583384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583384 prefixEnd_583384 := by exact prefixLift 583384
  have htrace : WordTrace (prefixWord ++ tailWord_583384) baseStart_583384 baseEnd_583384 := by
    simpa [prefixWord, tailWord_583384, baseEnd_583384] using wordTrace_append hprefix tailTrace_583384
  have hstable : (prefixWord ++ tailWord_583384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583384).length < 2 ^ (prefixWord ++ tailWord_583384).sum := by decide
  have hdescent : baseEnd_583384 < baseStart_583384 := by decide
  rcases family_descends (prefixWord ++ tailWord_583384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583508 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 5]
def baseStart_583508 : Nat := 118140960795 + 583508 * 2 ^ 59
def prefixEnd_583508 : Nat := 4983230072969 + 3 ^ 40 * 583508 * 2
def baseEnd_583508 : Nat := 66582237720846279103667

theorem tailTrace_583508 : CollatzResearch.WordTrace tailWord_583508 prefixEnd_583508 66582237720846279103667 := by
  unfold tailWord_583508
  simp only [CollatzResearch.WordTrace]
  refine ⟨10641142585028823038775589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14188190113371764051700785 10641142585028823038775589)
  ·
    refine ⟨1995214234692904319770423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10641142585028823038775589 1995214234692904319770423)
    ·
      refine ⟨2992821352039356479655635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1995214234692904319770423 2992821352039356479655635)
      ·
        refine ⟨4489232028059034719483453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2992821352039356479655635 4489232028059034719483453)
        ·
          refine ⟨1683462010522138019806295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4489232028059034719483453 1683462010522138019806295)
          ·
            refine ⟨2525193015783207029709443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683462010522138019806295 2525193015783207029709443)
            ·
              refine ⟨3787789523674810544564165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525193015783207029709443 3787789523674810544564165)
              ·
                refine ⟨710210535689026977105781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3787789523674810544564165 710210535689026977105781)
                ·
                  refine ⟨66582237720846279103667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 710210535689026977105781 66582237720846279103667)
                  ·
                    rfl

theorem cell22_583508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_583508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583508 prefixEnd_583508 := by exact prefixLift 583508
  have htrace : WordTrace (prefixWord ++ tailWord_583508) baseStart_583508 baseEnd_583508 := by
    simpa [prefixWord, tailWord_583508, baseEnd_583508] using wordTrace_append hprefix tailTrace_583508
  have hstable : (prefixWord ++ tailWord_583508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583508).length < 2 ^ (prefixWord ++ tailWord_583508).sum := by decide
  have hdescent : baseEnd_583508 < baseStart_583508 := by decide
  rcases family_descends (prefixWord ++ tailWord_583508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583521 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_583521 : Nat := 118140960795 + 583521 * 2 ^ 59
def prefixEnd_583521 : Nat := 4983230072969 + 3 ^ 40 * 583521 * 2
def baseEnd_583521 : Nat := 199751163328211136735961

theorem tailTrace_583521 : CollatzResearch.WordTrace tailWord_583521 prefixEnd_583521 199751163328211136735961 := by
  unfold tailWord_583521
  simp only [CollatzResearch.WordTrace]
  refine ⟨21282759319010549297774417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14188506212673699531849611 21282759319010549297774417)
  ·
    refine ⟨15962069489257911973330813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21282759319010549297774417 15962069489257911973330813)
    ·
      refine ⟨5985776058471716989999055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15962069489257911973330813 5985776058471716989999055)
      ·
        refine ⟨8978664087707575484998583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5985776058471716989999055 8978664087707575484998583)
        ·
          refine ⟨13467996131561363227497875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8978664087707575484998583 13467996131561363227497875)
          ·
            refine ⟨20201994197342044841246813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13467996131561363227497875 20201994197342044841246813)
            ·
              refine ⟨7575747824003266815467555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20201994197342044841246813 7575747824003266815467555)
              ·
                refine ⟨11363621736004900223201333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7575747824003266815467555 11363621736004900223201333)
                ·
                  refine ⟨1065339537750459395925125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11363621736004900223201333 1065339537750459395925125)
                  ·
                    refine ⟨199751163328211136735961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1065339537750459395925125 199751163328211136735961)
                    ·
                      rfl

theorem cell22_583521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_583521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583521 prefixEnd_583521 := by exact prefixLift 583521
  have htrace : WordTrace (prefixWord ++ tailWord_583521) baseStart_583521 baseEnd_583521 := by
    simpa [prefixWord, tailWord_583521, baseEnd_583521] using wordTrace_append hprefix tailTrace_583521
  have hstable : (prefixWord ++ tailWord_583521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583521).length < 2 ^ (prefixWord ++ tailWord_583521).sum := by decide
  have hdescent : baseEnd_583521 < baseStart_583521 := by decide
  rcases family_descends (prefixWord ++ tailWord_583521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583523 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 2, 5]
def baseStart_583523 : Nat := 118140960795 + 583523 * 2 ^ 59
def prefixEnd_583523 : Nat := 4983230072969 + 3 ^ 40 * 583523 * 2
def baseEnd_583523 : Nat := 199751847969083798185955

theorem tailTrace_583523 : CollatzResearch.WordTrace tailWord_583523 prefixEnd_583523 199751847969083798185955 := by
  unfold tailWord_583523
  simp only [CollatzResearch.WordTrace]
  refine ⟨21282832265003303639347223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14188554843335535759564815 21282832265003303639347223)
  ·
    refine ⟨31924248397504955459020835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21282832265003303639347223 31924248397504955459020835)
    ·
      refine ⟨47886372596257433188531253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31924248397504955459020835 47886372596257433188531253)
      ·
        refine ⟨4489347430899134361424805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47886372596257433188531253 4489347430899134361424805)
        ·
          refine ⟨841752643293587692767151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4489347430899134361424805 841752643293587692767151)
          ·
            refine ⟨1262628964940381539150727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841752643293587692767151 1262628964940381539150727)
            ·
              refine ⟨1893943447410572308726091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262628964940381539150727 1893943447410572308726091)
              ·
                refine ⟨2840915171115858463089137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1893943447410572308726091 2840915171115858463089137)
                ·
                  refine ⟨2130686378336893847316853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2840915171115858463089137 2130686378336893847316853)
                  ·
                    refine ⟨199751847969083798185955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2130686378336893847316853 199751847969083798185955)
                    ·
                      rfl

theorem cell22_583523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 5].length) (baseStart_583523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583523 prefixEnd_583523 := by exact prefixLift 583523
  have htrace : WordTrace (prefixWord ++ tailWord_583523) baseStart_583523 baseEnd_583523 := by
    simpa [prefixWord, tailWord_583523, baseEnd_583523] using wordTrace_append hprefix tailTrace_583523
  have hstable : (prefixWord ++ tailWord_583523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583523).length < 2 ^ (prefixWord ++ tailWord_583523).sum := by decide
  have hdescent : baseEnd_583523 < baseStart_583523 := by decide
  rcases family_descends (prefixWord ++ tailWord_583523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583538 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_583538 : Nat := 118140960795 + 583538 * 2 ^ 59
def prefixEnd_583538 : Nat := 4983230072969 + 3 ^ 40 * 583538 * 2
def baseEnd_583538 : Nat := 199756982775628759060909

theorem tailTrace_583538 : CollatzResearch.WordTrace tailWord_583538 prefixEnd_583538 199756982775628759060909 := by
  unfold tailWord_583538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5320844839987240300285817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14188919573299307467428845 5320844839987240300285817)
  ·
    refine ⟨3990633629990430225214363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5320844839987240300285817 3990633629990430225214363)
    ·
      refine ⟨5985950444985645337821545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3990633629990430225214363 5985950444985645337821545)
      ·
        refine ⟨4489462833739234003366159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5985950444985645337821545 4489462833739234003366159)
        ·
          refine ⟨6734194250608851005049239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4489462833739234003366159 6734194250608851005049239)
          ·
            refine ⟨10101291375913276507573859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6734194250608851005049239 10101291375913276507573859)
            ·
              refine ⟨15151937063869914761360789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10101291375913276507573859 15151937063869914761360789)
              ·
                refine ⟨710247049868902254438787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15151937063869914761360789 710247049868902254438787)
                ·
                  refine ⟨1065370574803353381658181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710247049868902254438787 1065370574803353381658181)
                  ·
                    refine ⟨199756982775628759060909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1065370574803353381658181 199756982775628759060909)
                    ·
                      rfl

theorem cell22_583538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_583538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583538 prefixEnd_583538 := by exact prefixLift 583538
  have htrace : WordTrace (prefixWord ++ tailWord_583538) baseStart_583538 baseEnd_583538 := by
    simpa [prefixWord, tailWord_583538, baseEnd_583538] using wordTrace_append hprefix tailTrace_583538
  have hstable : (prefixWord ++ tailWord_583538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583538).length < 2 ^ (prefixWord ++ tailWord_583538).sum := by decide
  have hdescent : baseEnd_583538 < baseStart_583538 := by decide
  rcases family_descends (prefixWord ++ tailWord_583538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583555 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 1, 4]
def baseStart_583555 : Nat := 118140960795 + 583555 * 2 ^ 59
def prefixEnd_583555 : Nat := 4983230072969 + 3 ^ 40 * 583555 * 2
def baseEnd_583555 : Nat := 199762802223046381385857

theorem tailTrace_583555 : CollatzResearch.WordTrace tailWord_583555 prefixEnd_583555 199762802223046381385857 := by
  unfold tailWord_583555
  simp only [CollatzResearch.WordTrace]
  refine ⟨21283999400887373104512119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14189332933924915403008079 21283999400887373104512119)
  ·
    refine ⟨31925999101331059656768179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21283999400887373104512119 31925999101331059656768179)
    ·
      refine ⟨47888998651996589485152269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31925999101331059656768179 47888998651996589485152269)
      ·
        refine ⟨17958374494498721056932101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47888998651996589485152269 17958374494498721056932101)
        ·
          refine ⟨3367195217718510198174769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17958374494498721056932101 3367195217718510198174769)
          ·
            refine ⟨2525396413288882648631077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3367195217718510198174769 2525396413288882648631077)
            ·
              refine ⟨473511827491665496618327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2525396413288882648631077 473511827491665496618327)
              ·
                refine ⟨710267741237498244927491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473511827491665496618327 710267741237498244927491)
                ·
                  refine ⟨1065401611856247367391237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710267741237498244927491 1065401611856247367391237)
                  ·
                    refine ⟨199762802223046381385857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1065401611856247367391237 199762802223046381385857)
                    ·
                      rfl

theorem cell22_583555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 4].length) (baseStart_583555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583555 prefixEnd_583555 := by exact prefixLift 583555
  have htrace : WordTrace (prefixWord ++ tailWord_583555) baseStart_583555 baseEnd_583555 := by
    simpa [prefixWord, tailWord_583555, baseEnd_583555] using wordTrace_append hprefix tailTrace_583555
  have hstable : (prefixWord ++ tailWord_583555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583555).length < 2 ^ (prefixWord ++ tailWord_583555).sum := by decide
  have hdescent : baseEnd_583555 < baseStart_583555 := by decide
  rcases family_descends (prefixWord ++ tailWord_583555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583570 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_583570 : Nat := 118140960795 + 583570 * 2 ^ 59
def prefixEnd_583570 : Nat := 4983230072969 + 3 ^ 40 * 583570 * 2
def baseEnd_583570 : Nat := 66589312343197114086937

theorem tailTrace_583570 : CollatzResearch.WordTrace tailWord_583570 prefixEnd_583570 66589312343197114086937 := by
  unfold tailWord_583570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5321136623958257666577041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14189697663888687110872109 5321136623958257666577041)
  ·
    refine ⟨3990852467968693249932781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5321136623958257666577041 3990852467968693249932781)
    ·
      refine ⟨1496569675488259968724793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3990852467968693249932781 1496569675488259968724793)
      ·
        refine ⟨1122427256616194976543595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1496569675488259968724793 1122427256616194976543595)
        ·
          refine ⟨1683640884924292464815393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1122427256616194976543595 1683640884924292464815393)
          ·
            refine ⟨1262730663693219348611545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1683640884924292464815393 1262730663693219348611545)
            ·
              refine ⟨947047997769914511458659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1262730663693219348611545 947047997769914511458659)
              ·
                refine ⟨1420571996654871767187989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947047997769914511458659 1420571996654871767187989)
                ·
                  refine ⟨66589312343197114086937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1420571996654871767187989 66589312343197114086937)
                  ·
                    rfl

theorem cell22_583570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_583570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583570 prefixEnd_583570 := by exact prefixLift 583570
  have htrace : WordTrace (prefixWord ++ tailWord_583570) baseStart_583570 baseEnd_583570 := by
    simpa [prefixWord, tailWord_583570, baseEnd_583570] using wordTrace_append hprefix tailTrace_583570
  have hstable : (prefixWord ++ tailWord_583570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583570).length < 2 ^ (prefixWord ++ tailWord_583570).sum := by decide
  have hdescent : baseEnd_583570 < baseStart_583570 := by decide
  rcases family_descends (prefixWord ++ tailWord_583570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583688 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 6]
def baseStart_583688 : Nat := 118140960795 + 583688 * 2 ^ 59
def prefixEnd_583688 : Nat := 4983230072969 + 3 ^ 40 * 583688 * 2
def baseEnd_583688 : Nat := 66602776947026122603483

theorem tailTrace_583688 : CollatzResearch.WordTrace tailWord_583688 prefixEnd_583688 66602776947026122603483 := by
  unfold tailWord_583688
  simp only [CollatzResearch.WordTrace]
  refine ⟨10644425154702768409551859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14192566872937024546069145 10644425154702768409551859)
  ·
    refine ⟨15966637732054152614327789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10644425154702768409551859 15966637732054152614327789)
    ·
      refine ⟨5987489149520307230372921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15966637732054152614327789 5987489149520307230372921)
      ·
        refine ⟨4490616862140230422779691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5987489149520307230372921 4490616862140230422779691)
        ·
          refine ⟨6735925293210345634169537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4490616862140230422779691 6735925293210345634169537)
          ·
            refine ⟨5051943969907759225627153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6735925293210345634169537 5051943969907759225627153)
            ·
              refine ⟨3788957977430819419220365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5051943969907759225627153 3788957977430819419220365)
              ·
                refine ⟨1420859241536557282207637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3788957977430819419220365 1420859241536557282207637)
                ·
                  refine ⟨66602776947026122603483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1420859241536557282207637 66602776947026122603483)
                  ·
                    rfl

theorem cell22_583688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_583688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583688 prefixEnd_583688 := by exact prefixLift 583688
  have htrace : WordTrace (prefixWord ++ tailWord_583688) baseStart_583688 baseEnd_583688 := by
    simpa [prefixWord, tailWord_583688, baseEnd_583688] using wordTrace_append hprefix tailTrace_583688
  have hstable : (prefixWord ++ tailWord_583688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583688).length < 2 ^ (prefixWord ++ tailWord_583688).sum := by decide
  have hdescent : baseEnd_583688 < baseStart_583688 := by decide
  rcases family_descends (prefixWord ++ tailWord_583688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583722 : List Nat := [3, 1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_583722 : Nat := 118140960795 + 583722 * 2 ^ 59
def prefixEnd_583722 : Nat := 4983230072969 + 3 ^ 40 * 583722 * 2
def baseEnd_583722 : Nat := 66606656578637870820115

theorem tailTrace_583722 : CollatzResearch.WordTrace tailWord_583722 prefixEnd_583722 66606656578637870820115 := by
  unfold tailWord_583722
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322522597820590156460355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14193393594188240417227613 5322522597820590156460355)
  ·
    refine ⟨7983783896730885234690533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5322522597820590156460355 7983783896730885234690533)
    ·
      refine ⟨1496959480637040981504475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7983783896730885234690533 1496959480637040981504475)
      ·
        refine ⟨2245439220955561472256713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496959480637040981504475 2245439220955561472256713)
        ·
          refine ⟨1684079415716671104192535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2245439220955561472256713 1684079415716671104192535)
          ·
            refine ⟨2526119123575006656288803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684079415716671104192535 2526119123575006656288803)
            ·
              refine ⟨3789178685362509984433205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526119123575006656288803 3789178685362509984433205)
              ·
                refine ⟨355235501752735311040613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3789178685362509984433205 355235501752735311040613)
                ·
                  refine ⟨66606656578637870820115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355235501752735311040613 66606656578637870820115)
                  ·
                    rfl

theorem cell22_583722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_583722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583722 prefixEnd_583722 := by exact prefixLift 583722
  have htrace : WordTrace (prefixWord ++ tailWord_583722) baseStart_583722 baseEnd_583722 := by
    simpa [prefixWord, tailWord_583722, baseEnd_583722] using wordTrace_append hprefix tailTrace_583722
  have hstable : (prefixWord ++ tailWord_583722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583722).length < 2 ^ (prefixWord ++ tailWord_583722).sum := by decide
  have hdescent : baseEnd_583722 < baseStart_583722 := by decide
  rcases family_descends (prefixWord ++ tailWord_583722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583737 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 4, 3]
def baseStart_583737 : Nat := 118140960795 + 583737 * 2 ^ 59
def prefixEnd_583737 : Nat := 4983230072969 + 3 ^ 40 * 583737 * 2
def baseEnd_583737 : Nat := 199825104542458573335299

theorem tailTrace_583737 : CollatzResearch.WordTrace tailWord_583737 prefixEnd_583737 199825104542458573335299 := by
  unfold tailWord_583737
  simp only [CollatzResearch.WordTrace]
  refine ⟨21290637486228018187637465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14193758324152012125091643 21290637486228018187637465)
  ·
    refine ⟨15967978114671013640728099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21290637486228018187637465 15967978114671013640728099)
    ·
      refine ⟨23951967172006520461092149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15967978114671013640728099 23951967172006520461092149)
      ·
        refine ⟨2245496922375611293227389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23951967172006520461092149 2245496922375611293227389)
        ·
          refine ⟨842061345890854234960271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2245496922375611293227389 842061345890854234960271)
          ·
            refine ⟨1263092018836281352440407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842061345890854234960271 1263092018836281352440407)
            ·
              refine ⟨1894638028254422028660611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263092018836281352440407 1894638028254422028660611)
              ·
                refine ⟨2841957042381633042990917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894638028254422028660611 2841957042381633042990917)
                ·
                  refine ⟨532866945446556195560797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2841957042381633042990917 532866945446556195560797)
                  ·
                    refine ⟨199825104542458573335299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 532866945446556195560797 199825104542458573335299)
                    ·
                      rfl

theorem cell22_583737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 3].length) (baseStart_583737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583737 prefixEnd_583737 := by exact prefixLift 583737
  have htrace : WordTrace (prefixWord ++ tailWord_583737) baseStart_583737 baseEnd_583737 := by
    simpa [prefixWord, tailWord_583737, baseEnd_583737] using wordTrace_append hprefix tailTrace_583737
  have hstable : (prefixWord ++ tailWord_583737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583737).length < 2 ^ (prefixWord ++ tailWord_583737).sum := by decide
  have hdescent : baseEnd_583737 < baseStart_583737 := by decide
  rcases family_descends (prefixWord ++ tailWord_583737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583808 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_583808 : Nat := 118140960795 + 583808 * 2 ^ 59
def prefixEnd_583808 : Nat := 4983230072969 + 3 ^ 40 * 583808 * 2
def baseEnd_583808 : Nat := 199849409293438054810081

theorem tailTrace_583808 : CollatzResearch.WordTrace tailWord_583808 prefixEnd_583808 199849409293438054810081 := by
  unfold tailWord_583808
  simp only [CollatzResearch.WordTrace]
  refine ⟨10646613534485398656736039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14195484712647198208981385 10646613534485398656736039)
  ·
    refine ⟨15969920301728097985104059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10646613534485398656736039 15969920301728097985104059)
    ·
      refine ⟨23954880452592146977656089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15969920301728097985104059 23954880452592146977656089)
      ·
        refine ⟨17966160339444110233242067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23954880452592146977656089 17966160339444110233242067)
        ·
          refine ⟨26949240509166165349863101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17966160339444110233242067 26949240509166165349863101)
          ·
            refine ⟨10105965190937312006198663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26949240509166165349863101 10105965190937312006198663)
            ·
              refine ⟨15158947786405968009297995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10105965190937312006198663 15158947786405968009297995)
              ·
                refine ⟨22738421679608952013946993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15158947786405968009297995 22738421679608952013946993)
                ·
                  refine ⟨17053816259706714010460245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22738421679608952013946993 17053816259706714010460245)
                  ·
                    refine ⟨199849409293438054810081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17053816259706714010460245 199849409293438054810081)
                    ·
                      rfl

theorem cell22_583808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_583808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583808 prefixEnd_583808 := by exact prefixLift 583808
  have htrace : WordTrace (prefixWord ++ tailWord_583808) baseStart_583808 baseEnd_583808 := by
    simpa [prefixWord, tailWord_583808, baseEnd_583808] using wordTrace_append hprefix tailTrace_583808
  have hstable : (prefixWord ++ tailWord_583808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583808).length < 2 ^ (prefixWord ++ tailWord_583808).sum := by decide
  have hdescent : baseEnd_583808 < baseStart_583808 := by decide
  rcases family_descends (prefixWord ++ tailWord_583808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583850 : List Nat := [3, 1, 5, 1, 2, 2, 2, 2, 1, 3]
def baseStart_583850 : Nat := 118140960795 + 583850 * 2 ^ 59
def prefixEnd_583850 : Nat := 4983230072969 + 3 ^ 40 * 583850 * 2
def baseEnd_583850 : Nat := 199863786751763945259953

theorem tailTrace_583850 : CollatzResearch.WordTrace tailWord_583850 prefixEnd_583850 199863786751763945259953 := by
  unfold tailWord_583850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5323689733704659621625251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14196505956545758991000669 5323689733704659621625251)
  ·
    refine ⟨7985534600556989432437877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5323689733704659621625251 7985534600556989432437877)
    ·
      refine ⟨748643868802217759291051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7985534600556989432437877 748643868802217759291051)
      ·
        refine ⟨1122965803203326638936577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748643868802217759291051 1122965803203326638936577)
        ·
          refine ⟨842224352402494979202433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1122965803203326638936577 842224352402494979202433)
          ·
            refine ⟨631668264301871234401825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842224352402494979202433 631668264301871234401825)
            ·
              refine ⟨473751198226403425801369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631668264301871234401825 473751198226403425801369)
              ·
                refine ⟨355313398669802569351027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473751198226403425801369 355313398669802569351027)
                ·
                  refine ⟨532970098004703854026541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355313398669802569351027 532970098004703854026541)
                  ·
                    refine ⟨199863786751763945259953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 532970098004703854026541 199863786751763945259953)
                    ·
                      rfl

theorem cell22_583850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_583850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583850 prefixEnd_583850 := by exact prefixLift 583850
  have htrace : WordTrace (prefixWord ++ tailWord_583850) baseStart_583850 baseEnd_583850 := by
    simpa [prefixWord, tailWord_583850, baseEnd_583850] using wordTrace_append hprefix tailTrace_583850
  have hstable : (prefixWord ++ tailWord_583850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583850).length < 2 ^ (prefixWord ++ tailWord_583850).sum := by decide
  have hdescent : baseEnd_583850 < baseStart_583850 := by decide
  rcases family_descends (prefixWord ++ tailWord_583850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583872 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 1, 5]
def baseStart_583872 : Nat := 118140960795 + 583872 * 2 ^ 59
def prefixEnd_583872 : Nat := 4983230072969 + 3 ^ 40 * 583872 * 2
def baseEnd_583872 : Nat := 199871317801363221209885

theorem tailTrace_583872 : CollatzResearch.WordTrace tailWord_583872 prefixEnd_583872 199871317801363221209885 := by
  unfold tailWord_583872
  simp only [CollatzResearch.WordTrace]
  refine ⟨10647780670369468121900935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14197040893825957495867913 10647780670369468121900935)
  ·
    refine ⟨15971671005554202182851403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10647780670369468121900935 15971671005554202182851403)
    ·
      refine ⟨23957506508331303274277105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15971671005554202182851403 23957506508331303274277105)
      ·
        refine ⟨17968129881248477455707829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23957506508331303274277105 17968129881248477455707829)
        ·
          refine ⟨1684512176367044761472609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17968129881248477455707829 1684512176367044761472609)
          ·
            refine ⟨1263384132275283571104457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1684512176367044761472609 1263384132275283571104457)
            ·
              refine ⟨947538099206462678328343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263384132275283571104457 947538099206462678328343)
              ·
                refine ⟨1421307148809694017492515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947538099206462678328343 1421307148809694017492515)
                ·
                  refine ⟨2131960723214541026238773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421307148809694017492515 2131960723214541026238773)
                  ·
                    refine ⟨199871317801363221209885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2131960723214541026238773 199871317801363221209885)
                    ·
                      rfl

theorem cell22_583872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_583872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583872 prefixEnd_583872 := by exact prefixLift 583872
  have htrace : WordTrace (prefixWord ++ tailWord_583872) baseStart_583872 baseEnd_583872 := by
    simpa [prefixWord, tailWord_583872, baseEnd_583872] using wordTrace_append hprefix tailTrace_583872
  have hstable : (prefixWord ++ tailWord_583872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583872).length < 2 ^ (prefixWord ++ tailWord_583872).sum := by decide
  have hdescent : baseEnd_583872 < baseStart_583872 := by decide
  rcases family_descends (prefixWord ++ tailWord_583872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583874 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_583874 : Nat := 118140960795 + 583874 * 2 ^ 59
def prefixEnd_583874 : Nat := 4983230072969 + 3 ^ 40 * 583874 * 2
def baseEnd_583874 : Nat := 66624000814078627553293

theorem tailTrace_583874 : CollatzResearch.WordTrace tailWord_583874 prefixEnd_583874 66624000814078627553293 := by
  unfold tailWord_583874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5323908571682922646343669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14197089524487793723583117 5323908571682922646343669)
  ·
    refine ⟨499116428595273998094719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5323908571682922646343669 499116428595273998094719)
    ·
      refine ⟨748674642892910997142079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499116428595273998094719 748674642892910997142079)
      ·
        refine ⟨1123011964339366495713119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748674642892910997142079 1123011964339366495713119)
        ·
          refine ⟨1684517946509049743569679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123011964339366495713119 1684517946509049743569679)
          ·
            refine ⟨2526776919763574615354519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684517946509049743569679 2526776919763574615354519)
            ·
              refine ⟨3790165379645361923031779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526776919763574615354519 3790165379645361923031779)
              ·
                refine ⟨5685248069468042884547669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3790165379645361923031779 5685248069468042884547669)
                ·
                  refine ⟨66624000814078627553293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5685248069468042884547669 66624000814078627553293)
                  ·
                    rfl

theorem cell22_583874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_583874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583874 prefixEnd_583874 := by exact prefixLift 583874
  have htrace : WordTrace (prefixWord ++ tailWord_583874) baseStart_583874 baseEnd_583874 := by
    simpa [prefixWord, tailWord_583874, baseEnd_583874] using wordTrace_append hprefix tailTrace_583874
  have hstable : (prefixWord ++ tailWord_583874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583874).length < 2 ^ (prefixWord ++ tailWord_583874).sum := by decide
  have hdescent : baseEnd_583874 < baseStart_583874 := by decide
  rcases family_descends (prefixWord ++ tailWord_583874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583893 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 1, 4]
def baseStart_583893 : Nat := 118140960795 + 583893 * 2 ^ 59
def prefixEnd_583893 : Nat := 4983230072969 + 3 ^ 40 * 583893 * 2
def baseEnd_583893 : Nat := 199878506530526166434821

theorem tailTrace_583893 : CollatzResearch.WordTrace tailWord_583893 prefixEnd_583893 199878506530526166434821 := by
  unfold tailWord_583893
  simp only [CollatzResearch.WordTrace]
  refine ⟨21296327273662856830316333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14197551515775237886877555 21296327273662856830316333)
  ·
    refine ⟨7986122727623571311368625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21296327273662856830316333 7986122727623571311368625)
    ·
      refine ⟨5989592045717678483526469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7986122727623571311368625 5989592045717678483526469)
      ·
        refine ⟨1123048508572064715661213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5989592045717678483526469 1123048508572064715661213)
        ·
          refine ⟨421143190714524268372955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1123048508572064715661213 421143190714524268372955)
          ·
            refine ⟨631714786071786402559433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421143190714524268372955 631714786071786402559433)
            ·
              refine ⟨473786089553839801919575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631714786071786402559433 473786089553839801919575)
              ·
                refine ⟨710679134330759702879363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473786089553839801919575 710679134330759702879363)
                ·
                  refine ⟨1066018701496139554319045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710679134330759702879363 1066018701496139554319045)
                  ·
                    refine ⟨199878506530526166434821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1066018701496139554319045 199878506530526166434821)
                    ·
                      rfl

theorem cell22_583893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_583893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583893 prefixEnd_583893 := by exact prefixLift 583893
  have htrace : WordTrace (prefixWord ++ tailWord_583893) baseStart_583893 baseEnd_583893 := by
    simpa [prefixWord, tailWord_583893, baseEnd_583893] using wordTrace_append hprefix tailTrace_583893
  have hstable : (prefixWord ++ tailWord_583893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583893).length < 2 ^ (prefixWord ++ tailWord_583893).sum := by decide
  have hdescent : baseEnd_583893 < baseStart_583893 := by decide
  rcases family_descends (prefixWord ++ tailWord_583893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583934 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_583934 : Nat := 118140960795 + 583934 * 2 ^ 59
def prefixEnd_583934 : Nat := 4983230072969 + 3 ^ 40 * 583934 * 2
def baseEnd_583934 : Nat := 199892541668415726159695

theorem tailTrace_583934 : CollatzResearch.WordTrace tailWord_583934 prefixEnd_583934 199892541668415726159695 := by
  unfold tailWord_583934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662227833314290104069857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14198548444342880555039237 2662227833314290104069857)
  ·
    refine ⟨1996670874985717578052393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2662227833314290104069857 1996670874985717578052393)
    ·
      refine ⟨1497503156239288183539295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1996670874985717578052393 1497503156239288183539295)
      ·
        refine ⟨2246254734358932275308943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497503156239288183539295 2246254734358932275308943)
        ·
          refine ⟨3369382101538398412963415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2246254734358932275308943 3369382101538398412963415)
          ·
            refine ⟨5054073152307597619445123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369382101538398412963415 5054073152307597619445123)
            ·
              refine ⟨7581109728461396429167685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054073152307597619445123 7581109728461396429167685)
              ·
                refine ⟨1421458074086511830468941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7581109728461396429167685 1421458074086511830468941)
                ·
                  refine ⟨533046777782441936425853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1421458074086511830468941 533046777782441936425853)
                  ·
                    refine ⟨199892541668415726159695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 533046777782441936425853 199892541668415726159695)
                    ·
                      rfl

theorem cell22_583934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_583934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583934 prefixEnd_583934 := by exact prefixLift 583934
  have htrace : WordTrace (prefixWord ++ tailWord_583934) baseStart_583934 baseEnd_583934 := by
    simpa [prefixWord, tailWord_583934, baseEnd_583934] using wordTrace_append hprefix tailTrace_583934
  have hstable : (prefixWord ++ tailWord_583934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583934).length < 2 ^ (prefixWord ++ tailWord_583934).sum := by decide
  have hdescent : baseEnd_583934 < baseStart_583934 := by decide
  rcases family_descends (prefixWord ++ tailWord_583934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583968 : List Nat := [2, 1, 1, 5, 2, 2, 3, 2, 1, 3]
def baseStart_583968 : Nat := 118140960795 + 583968 * 2 ^ 59
def prefixEnd_583968 : Nat := 4983230072969 + 3 ^ 40 * 583968 * 2
def baseEnd_583968 : Nat := 199904180563250970809591

theorem tailTrace_583968 : CollatzResearch.WordTrace tailWord_583968 prefixEnd_583968 199904180563250970809591 := by
  unfold tailWord_583968
  simp only [CollatzResearch.WordTrace]
  refine ⟨10649531374195572319648279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14199375165594096426197705 10649531374195572319648279)
  ·
    refine ⟨15974297061293358479472419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10649531374195572319648279 15974297061293358479472419)
    ·
      refine ⟨23961445591940037719208629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15974297061293358479472419 23961445591940037719208629)
      ·
        refine ⟨2246385524244378536175809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23961445591940037719208629 2246385524244378536175809)
        ·
          refine ⟨1684789143183283902131857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2246385524244378536175809 1684789143183283902131857)
          ·
            refine ⟨1263591857387462926598893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1684789143183283902131857 1263591857387462926598893)
            ·
              refine ⟨473846946520298597474585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1263591857387462926598893 473846946520298597474585)
              ·
                refine ⟨355385209890223948105939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473846946520298597474585 355385209890223948105939)
                ·
                  refine ⟨533077814835335922158909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355385209890223948105939 533077814835335922158909)
                  ·
                    refine ⟨199904180563250970809591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 533077814835335922158909 199904180563250970809591)
                    ·
                      rfl

theorem cell22_583968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 1, 3].length) (baseStart_583968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583968 prefixEnd_583968 := by exact prefixLift 583968
  have htrace : WordTrace (prefixWord ++ tailWord_583968) baseStart_583968 baseEnd_583968 := by
    simpa [prefixWord, tailWord_583968, baseEnd_583968] using wordTrace_append hprefix tailTrace_583968
  have hstable : (prefixWord ++ tailWord_583968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583968).length < 2 ^ (prefixWord ++ tailWord_583968).sum := by decide
  have hdescent : baseEnd_583968 < baseStart_583968 := by decide
  rcases family_descends (prefixWord ++ tailWord_583968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583981 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 5]
def baseStart_583981 : Nat := 118140960795 + 583981 * 2 ^ 59
def prefixEnd_583981 : Nat := 4983230072969 + 3 ^ 40 * 583981 * 2
def baseEnd_583981 : Nat := 66636210242974423411517

theorem tailTrace_583981 : CollatzResearch.WordTrace tailWord_583981 prefixEnd_583981 66636210242974423411517 := by
  unfold tailWord_583981
  simp only [CollatzResearch.WordTrace]
  refine ⟨21299536897344047859519797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14199691264896031906346531 21299536897344047859519797)
  ·
    refine ⟨1996831584126004486829981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21299536897344047859519797 1996831584126004486829981)
    ·
      refine ⟨748811844047251682561243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1996831584126004486829981 748811844047251682561243)
      ·
        refine ⟨1123217766070877523841865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748811844047251682561243 1123217766070877523841865)
        ·
          refine ⟨842413324553158142881399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1123217766070877523841865 842413324553158142881399)
          ·
            refine ⟨1263619986829737214322099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842413324553158142881399 1263619986829737214322099)
            ·
              refine ⟨1895429980244605821483149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263619986829737214322099 1895429980244605821483149)
              ·
                refine ⟨710786242591727183056181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1895429980244605821483149 710786242591727183056181)
                ·
                  refine ⟨66636210242974423411517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 710786242591727183056181 66636210242974423411517)
                  ·
                    rfl

theorem cell22_583981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_583981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583981 prefixEnd_583981 := by exact prefixLift 583981
  have htrace : WordTrace (prefixWord ++ tailWord_583981) baseStart_583981 baseEnd_583981 := by
    simpa [prefixWord, tailWord_583981, baseEnd_583981] using wordTrace_append hprefix tailTrace_583981
  have hstable : (prefixWord ++ tailWord_583981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583981).length < 2 ^ (prefixWord ++ tailWord_583981).sum := by decide
  have hdescent : baseEnd_583981 < baseStart_583981 := by decide
  rcases family_descends (prefixWord ++ tailWord_583981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583994 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_583994 : Nat := 118140960795 + 583994 * 2 ^ 59
def prefixEnd_583994 : Nat := 4983230072969 + 3 ^ 40 * 583994 * 2
def baseEnd_583994 : Nat := 199913080894595569659511

theorem tailTrace_583994 : CollatzResearch.WordTrace tailWord_583994 prefixEnd_583994 199913080894595569659511 := by
  unfold tailWord_583994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5325002761574237769935759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14200007364197967386495357 5325002761574237769935759)
  ·
    refine ⟨7987504142361356654903639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5325002761574237769935759 7987504142361356654903639)
    ·
      refine ⟨11981256213542034982355459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7987504142361356654903639 11981256213542034982355459)
      ·
        refine ⟨17971884320313052473533189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11981256213542034982355459 17971884320313052473533189)
        ·
          refine ⟨3369728310058697338787473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17971884320313052473533189 3369728310058697338787473)
          ·
            refine ⟨2527296232544023004090605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3369728310058697338787473 2527296232544023004090605)
            ·
              refine ⟨947736087204008626533977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2527296232544023004090605 947736087204008626533977)
              ·
                refine ⟨710802065403006469900483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947736087204008626533977 710802065403006469900483)
                ·
                  refine ⟨1066203098104509704850725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710802065403006469900483 1066203098104509704850725)
                  ·
                    refine ⟨199913080894595569659511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1066203098104509704850725 199913080894595569659511)
                    ·
                      rfl

theorem cell22_583994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_583994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_583994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_583994 prefixEnd_583994 := by exact prefixLift 583994
  have htrace : WordTrace (prefixWord ++ tailWord_583994) baseStart_583994 baseEnd_583994 := by
    simpa [prefixWord, tailWord_583994, baseEnd_583994] using wordTrace_append hprefix tailTrace_583994
  have hstable : (prefixWord ++ tailWord_583994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583994).length < 2 ^ (prefixWord ++ tailWord_583994).sum := by decide
  have hdescent : baseEnd_583994 < baseStart_583994 := by decide
  rcases family_descends (prefixWord ++ tailWord_583994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584007 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 1, 5]
def baseStart_584007 : Nat := 118140960795 + 584007 * 2 ^ 59
def prefixEnd_584007 : Nat := 4983230072969 + 3 ^ 40 * 584007 * 2
def baseEnd_584007 : Nat := 199917531060267869084471

theorem tailTrace_584007 : CollatzResearch.WordTrace tailWord_584007 prefixEnd_584007 199917531060267869084471 := by
  unfold tailWord_584007
  simp only [CollatzResearch.WordTrace]
  refine ⟨21300485195249854299966275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14200323463499902866644183 21300485195249854299966275)
  ·
    refine ⟨31950727792874781449949413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21300485195249854299966275 31950727792874781449949413)
    ·
      refine ⟨5990761461164021521865515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31950727792874781449949413 5990761461164021521865515)
      ·
        refine ⟨8986142191746032282798273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5990761461164021521865515 8986142191746032282798273)
        ·
          refine ⟨6739606643809524212098705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8986142191746032282798273 6739606643809524212098705)
          ·
            refine ⟨5054704982857143159074029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6739606643809524212098705 5054704982857143159074029)
            ·
              refine ⟨1895514368571428684652761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5054704982857143159074029 1895514368571428684652761)
              ·
                refine ⟨1421635776428571513489571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1895514368571428684652761 1421635776428571513489571)
                ·
                  refine ⟨2132453664642857270234357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421635776428571513489571 2132453664642857270234357)
                  ·
                    refine ⟨199917531060267869084471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2132453664642857270234357 199917531060267869084471)
                    ·
                      rfl

theorem cell22_584007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_584007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584007 prefixEnd_584007 := by exact prefixLift 584007
  have htrace : WordTrace (prefixWord ++ tailWord_584007) baseStart_584007 baseEnd_584007 := by
    simpa [prefixWord, tailWord_584007, baseEnd_584007] using wordTrace_append hprefix tailTrace_584007
  have hstable : (prefixWord ++ tailWord_584007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584007).length < 2 ^ (prefixWord ++ tailWord_584007).sum := by decide
  have hdescent : baseEnd_584007 < baseStart_584007 := by decide
  rcases family_descends (prefixWord ++ tailWord_584007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584030 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_584030 : Nat := 118140960795 + 584030 * 2 ^ 59
def prefixEnd_584030 : Nat := 4983230072969 + 3 ^ 40 * 584030 * 2
def baseEnd_584030 : Nat := 199925404430303475759401

theorem tailTrace_584030 : CollatzResearch.WordTrace tailWord_584030 prefixEnd_584030 199925404430303475759401 := by
  unfold tailWord_584030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662665509270816153506693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14200882716111019485369029 2662665509270816153506693)
  ·
    refine ⟨499249782988278028782505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2662665509270816153506693 499249782988278028782505)
    ·
      refine ⟨374437337241208521586879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 499249782988278028782505 374437337241208521586879)
      ·
        refine ⟨561656005861812782380319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374437337241208521586879 561656005861812782380319)
        ·
          refine ⟨842484008792719173570479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561656005861812782380319 842484008792719173570479)
          ·
            refine ⟨1263726013189078760355719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842484008792719173570479 1263726013189078760355719)
            ·
              refine ⟨1895589019783618140533579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263726013189078760355719 1895589019783618140533579)
              ·
                refine ⟨2843383529675427210800369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895589019783618140533579 2843383529675427210800369)
                ·
                  refine ⟨2132537647256570408100277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2843383529675427210800369 2132537647256570408100277)
                  ·
                    refine ⟨199925404430303475759401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2132537647256570408100277 199925404430303475759401)
                    ·
                      rfl

theorem cell22_584030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_584030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584030 prefixEnd_584030 := by exact prefixLift 584030
  have htrace : WordTrace (prefixWord ++ tailWord_584030) baseStart_584030 baseEnd_584030 := by
    simpa [prefixWord, tailWord_584030, baseEnd_584030] using wordTrace_append hprefix tailTrace_584030
  have hstable : (prefixWord ++ tailWord_584030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584030).length < 2 ^ (prefixWord ++ tailWord_584030).sum := by decide
  have hdescent : baseEnd_584030 < baseStart_584030 := by decide
  rcases family_descends (prefixWord ++ tailWord_584030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584037 : List Nat := [1, 3, 1, 3, 1, 3, 3, 7]
def baseStart_584037 : Nat := 118140960795 + 584037 * 2 ^ 59
def prefixEnd_584037 : Nat := 4983230072969 + 3 ^ 40 * 584037 * 2
def baseEnd_584037 : Nat := 22214200074817532314931

theorem tailTrace_584037 : CollatzResearch.WordTrace tailWord_584037 prefixEnd_584037 22214200074817532314931 := by
  unfold tailWord_584037
  simp only [CollatzResearch.WordTrace]
  refine ⟨21301579385141169423558365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14201052923427446282372243 21301579385141169423558365)
  ·
    refine ⟨7988092269427938533834387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21301579385141169423558365 7988092269427938533834387)
    ·
      refine ⟨11982138404141907800751581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7988092269427938533834387 11982138404141907800751581)
      ·
        refine ⟨4493301901553215425281843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11982138404141907800751581 4493301901553215425281843)
        ·
          refine ⟨6739952852329823137922765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493301901553215425281843 6739952852329823137922765)
          ·
            refine ⟨2527482319623683676721037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6739952852329823137922765 2527482319623683676721037)
            ·
              refine ⟨947805869858881378770389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2527482319623683676721037 947805869858881378770389)
              ·
                refine ⟨22214200074817532314931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 947805869858881378770389 22214200074817532314931)
                ·
                  rfl

theorem cell22_584037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 7].length) (baseStart_584037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584037 prefixEnd_584037 := by exact prefixLift 584037
  have htrace : WordTrace (prefixWord ++ tailWord_584037) baseStart_584037 baseEnd_584037 := by
    simpa [prefixWord, tailWord_584037, baseEnd_584037] using wordTrace_append hprefix tailTrace_584037
  have hstable : (prefixWord ++ tailWord_584037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584037).length < 2 ^ (prefixWord ++ tailWord_584037).sum := by decide
  have hdescent : baseEnd_584037 < baseStart_584037 := by decide
  rcases family_descends (prefixWord ++ tailWord_584037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584112 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_584112 : Nat := 118140960795 + 584112 * 2 ^ 59
def prefixEnd_584112 : Nat := 4983230072969 + 3 ^ 40 * 584112 * 2
def baseEnd_584112 : Nat := 199953474706082595209149

theorem tailTrace_584112 : CollatzResearch.WordTrace tailWord_584112 prefixEnd_584112 199953474706082595209149 := by
  unfold tailWord_584112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10652157429934728616269295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14202876573246304821692393 10652157429934728616269295)
  ·
    refine ⟨15978236144902092924403943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10652157429934728616269295 15978236144902092924403943)
    ·
      refine ⟨23967354217353139386605915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15978236144902092924403943 23967354217353139386605915)
      ·
        refine ⟨35951031326029709079908873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23967354217353139386605915 35951031326029709079908873)
        ·
          refine ⟨26963273494522281809931655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35951031326029709079908873 26963273494522281809931655)
          ·
            refine ⟨40444910241783422714897483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26963273494522281809931655 40444910241783422714897483)
            ·
              refine ⟨60667365362675134072346225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40444910241783422714897483 60667365362675134072346225)
              ·
                refine ⟨45500524022006350554259669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60667365362675134072346225 45500524022006350554259669)
                ·
                  refine ⟨1066418531765773841115461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 45500524022006350554259669 1066418531765773841115461)
                  ·
                    refine ⟨199953474706082595209149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1066418531765773841115461 199953474706082595209149)
                    ·
                      rfl

theorem cell22_584112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_584112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584112 prefixEnd_584112 := by exact prefixLift 584112
  have htrace : WordTrace (prefixWord ++ tailWord_584112) baseStart_584112 baseEnd_584112 := by
    simpa [prefixWord, tailWord_584112, baseEnd_584112] using wordTrace_append hprefix tailTrace_584112
  have hstable : (prefixWord ++ tailWord_584112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584112).length < 2 ^ (prefixWord ++ tailWord_584112).sum := by decide
  have hdescent : baseEnd_584112 < baseStart_584112 := by decide
  rcases family_descends (prefixWord ++ tailWord_584112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584163 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 1, 4]
def baseStart_584163 : Nat := 118140960795 + 584163 * 2 ^ 59
def prefixEnd_584163 : Nat := 4983230072969 + 3 ^ 40 * 584163 * 2
def baseEnd_584163 : Nat := 199970933048335462183993

theorem tailTrace_584163 : CollatzResearch.WordTrace tailWord_584163 prefixEnd_584163 199970933048335462183993 := by
  unfold tailWord_584163
  simp only [CollatzResearch.WordTrace]
  refine ⟨21306174982684692942645143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14204116655123128628430095 21306174982684692942645143)
  ·
    refine ⟨31959262474027039413967715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21306174982684692942645143 31959262474027039413967715)
    ·
      refine ⟨47938893711040559120951573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31959262474027039413967715 47938893711040559120951573)
      ·
        refine ⟨2247135642705026208794605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47938893711040559120951573 2247135642705026208794605)
        ·
          refine ⟨842675866014384828297977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2247135642705026208794605 842675866014384828297977)
          ·
            refine ⟨632006899510788621223483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842675866014384828297977 632006899510788621223483)
            ·
              refine ⟨948010349266182931835225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632006899510788621223483 948010349266182931835225)
              ·
                refine ⟨711007761949637198876419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948010349266182931835225 711007761949637198876419)
                ·
                  refine ⟨1066511642924455798314629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711007761949637198876419 1066511642924455798314629)
                  ·
                    refine ⟨199970933048335462183993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1066511642924455798314629 199970933048335462183993)
                    ·
                      rfl

theorem cell22_584163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 4].length) (baseStart_584163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584163 prefixEnd_584163 := by exact prefixLift 584163
  have htrace : WordTrace (prefixWord ++ tailWord_584163) baseStart_584163 baseEnd_584163 := by
    simpa [prefixWord, tailWord_584163, baseEnd_584163] using wordTrace_append hprefix tailTrace_584163
  have hstable : (prefixWord ++ tailWord_584163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584163).length < 2 ^ (prefixWord ++ tailWord_584163).sum := by decide
  have hdescent : baseEnd_584163 < baseStart_584163 := by decide
  rcases family_descends (prefixWord ++ tailWord_584163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584172 : List Nat := [2, 2, 1, 1, 2, 1, 3, 10]
def baseStart_584172 : Nat := 118140960795 + 584172 * 2 ^ 59
def prefixEnd_584172 : Nat := 4983230072969 + 3 ^ 40 * 584172 * 2
def baseEnd_584172 : Nat := 22219334881362493189885

theorem tailTrace_584172 : CollatzResearch.WordTrace tailWord_584172 prefixEnd_584172 22219334881362493189885 := by
  unfold tailWord_584172
  simp only [CollatzResearch.WordTrace]
  refine ⟨10653251619826043739861385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14204335493101391653148513 10653251619826043739861385)
  ·
    refine ⟨7989938714869532804896039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10653251619826043739861385 7989938714869532804896039)
    ·
      refine ⟨11984908072304299207344059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7989938714869532804896039 11984908072304299207344059)
      ·
        refine ⟨17977362108456448811016089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11984908072304299207344059 17977362108456448811016089)
        ·
          refine ⟨13483021581342336608262067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17977362108456448811016089 13483021581342336608262067)
          ·
            refine ⟨20224532372013504912393101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13483021581342336608262067 20224532372013504912393101)
            ·
              refine ⟨7584199639505064342147413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20224532372013504912393101 7584199639505064342147413)
              ·
                refine ⟨22219334881362493189885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7584199639505064342147413 22219334881362493189885)
                ·
                  rfl

theorem cell22_584172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 10].length) (baseStart_584172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584172 prefixEnd_584172 := by exact prefixLift 584172
  have htrace : WordTrace (prefixWord ++ tailWord_584172) baseStart_584172 baseEnd_584172 := by
    simpa [prefixWord, tailWord_584172, baseEnd_584172] using wordTrace_append hprefix tailTrace_584172
  have hstable : (prefixWord ++ tailWord_584172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584172).length < 2 ^ (prefixWord ++ tailWord_584172).sum := by decide
  have hdescent : baseEnd_584172 < baseStart_584172 := by decide
  rcases family_descends (prefixWord ++ tailWord_584172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584193 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 2, 3]
def baseStart_584193 : Nat := 118140960795 + 584193 * 2 ^ 59
def prefixEnd_584193 : Nat := 4983230072969 + 3 ^ 40 * 584193 * 2
def baseEnd_584193 : Nat := 199981202661425383933901

theorem tailTrace_584193 : CollatzResearch.WordTrace tailWord_584193 prefixEnd_584193 199981202661425383933901 := by
  unfold tailWord_584193
  simp only [CollatzResearch.WordTrace]
  refine ⟨21307269172576008066237233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14204846115050672044158155 21307269172576008066237233)
  ·
    refine ⟨15980451879432006049677925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21307269172576008066237233 15980451879432006049677925)
    ·
      refine ⟨2996334727393501134314611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15980451879432006049677925 2996334727393501134314611)
      ·
        refine ⟨4494502091090251701471917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2996334727393501134314611 4494502091090251701471917)
        ·
          refine ⟨1685438284158844388051969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4494502091090251701471917 1685438284158844388051969)
          ·
            refine ⟨1264078713119133291038977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1685438284158844388051969 1264078713119133291038977)
            ·
              refine ⟨948059034839349968279233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264078713119133291038977 948059034839349968279233)
              ·
                refine ⟨711044276129512476209425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948059034839349968279233 711044276129512476209425)
                ·
                  refine ⟨533283207097134357157069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 711044276129512476209425 533283207097134357157069)
                  ·
                    refine ⟨199981202661425383933901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 533283207097134357157069 199981202661425383933901)
                    ·
                      rfl

theorem cell22_584193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_584193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584193 prefixEnd_584193 := by exact prefixLift 584193
  have htrace : WordTrace (prefixWord ++ tailWord_584193) baseStart_584193 baseEnd_584193 := by
    simpa [prefixWord, tailWord_584193, baseEnd_584193] using wordTrace_append hprefix tailTrace_584193
  have hstable : (prefixWord ++ tailWord_584193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584193).length < 2 ^ (prefixWord ++ tailWord_584193).sum := by decide
  have hdescent : baseEnd_584193 < baseStart_584193 := by decide
  rcases family_descends (prefixWord ++ tailWord_584193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584206 : List Nat := [4, 1, 1, 2, 3, 3, 1, 7]
def baseStart_584206 : Nat := 118140960795 + 584206 * 2 ^ 59
def prefixEnd_584206 : Nat := 4983230072969 + 3 ^ 40 * 584206 * 2
def baseEnd_584206 : Nat := 22220628091899742595429

theorem tailTrace_584206 : CollatzResearch.WordTrace tailWord_584206 prefixEnd_584206 22220628091899742595429 := by
  unfold tailWord_584206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663467915191113910807559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14205162214352607524306981 2663467915191113910807559)
  ·
    refine ⟨3995201872786670866211339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2663467915191113910807559 3995201872786670866211339)
    ·
      refine ⟨5992802809180006299317009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3995201872786670866211339 5992802809180006299317009)
      ·
        refine ⟨4494602106885004724487757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5992802809180006299317009 4494602106885004724487757)
        ·
          refine ⟨1685475790081876771682909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4494602106885004724487757 1685475790081876771682909)
          ·
            refine ⟨632053421280703789381091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1685475790081876771682909 632053421280703789381091)
            ·
              refine ⟨948080131921055684071637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632053421280703789381091 948080131921055684071637)
              ·
                refine ⟨22220628091899742595429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 948080131921055684071637 22220628091899742595429)
                ·
                  rfl

theorem cell22_584206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_584206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584206 prefixEnd_584206 := by exact prefixLift 584206
  have htrace : WordTrace (prefixWord ++ tailWord_584206) baseStart_584206 baseEnd_584206 := by
    simpa [prefixWord, tailWord_584206, baseEnd_584206] using wordTrace_append hprefix tailTrace_584206
  have hstable : (prefixWord ++ tailWord_584206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584206).length < 2 ^ (prefixWord ++ tailWord_584206).sum := by decide
  have hdescent : baseEnd_584206 < baseStart_584206 := by decide
  rcases family_descends (prefixWord ++ tailWord_584206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584221 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_584221 : Nat := 118140960795 + 584221 * 2 ^ 59
def prefixEnd_584221 : Nat := 4983230072969 + 3 ^ 40 * 584221 * 2
def baseEnd_584221 : Nat := 199990787633642644233815

theorem tailTrace_584221 : CollatzResearch.WordTrace tailWord_584221 prefixEnd_584221 199990787633642644233815 := by
  unfold tailWord_584221
  simp only [CollatzResearch.WordTrace]
  refine ⟨21308290416474568848256517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14205526944316379232171011 21308290416474568848256517)
  ·
    refine ⟨3995304453088981659048097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21308290416474568848256517 3995304453088981659048097)
    ·
      refine ⟨2996478339816736244286073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3995304453088981659048097 2996478339816736244286073)
      ·
        refine ⟨2247358754862552183214555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2996478339816736244286073 2247358754862552183214555)
        ·
          refine ⟨3371038132293828274821833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247358754862552183214555 3371038132293828274821833)
          ·
            refine ⟨2528278599220371206116375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3371038132293828274821833 2528278599220371206116375)
            ·
              refine ⟨3792417898830556809174563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2528278599220371206116375 3792417898830556809174563)
              ·
                refine ⟨5688626848245835213761845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3792417898830556809174563 5688626848245835213761845)
                ·
                  refine ⟨533308767023047051290173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5688626848245835213761845 533308767023047051290173)
                  ·
                    refine ⟨199990787633642644233815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 533308767023047051290173 199990787633642644233815)
                    ·
                      rfl

theorem cell22_584221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_584221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584221 prefixEnd_584221 := by exact prefixLift 584221
  have htrace : WordTrace (prefixWord ++ tailWord_584221) baseStart_584221 baseEnd_584221 := by
    simpa [prefixWord, tailWord_584221, baseEnd_584221] using wordTrace_append hprefix tailTrace_584221
  have hstable : (prefixWord ++ tailWord_584221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584221).length < 2 ^ (prefixWord ++ tailWord_584221).sum := by decide
  have hdescent : baseEnd_584221 < baseStart_584221 := by decide
  rcases family_descends (prefixWord ++ tailWord_584221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584244 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_584244 : Nat := 118140960795 + 584244 * 2 ^ 59
def prefixEnd_584244 : Nat := 4983230072969 + 3 ^ 40 * 584244 * 2
def baseEnd_584244 : Nat := 199998661003678250908745

theorem tailTrace_584244 : CollatzResearch.WordTrace tailWord_584244 prefixEnd_584244 199998661003678250908745 := by
  unfold tailWord_584244
  simp only [CollatzResearch.WordTrace]
  refine ⟨10654564647695621888171893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14206086196927495850895857 10654564647695621888171893)
  ·
    refine ⟨998865435721464552016115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10654564647695621888171893 998865435721464552016115)
    ·
      refine ⟨1498298153582196828024173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998865435721464552016115 1498298153582196828024173)
      ·
        refine ⟨561861807593323810509065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1498298153582196828024173 561861807593323810509065)
        ·
          refine ⟨421396355694992857881799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561861807593323810509065 421396355694992857881799)
          ·
            refine ⟨632094533542489286822699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421396355694992857881799 632094533542489286822699)
            ·
              refine ⟨948141800313733930234049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632094533542489286822699 948141800313733930234049)
              ·
                refine ⟨711106350235300447675537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948141800313733930234049 711106350235300447675537)
                ·
                  refine ⟨533329762676475335756653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 711106350235300447675537 533329762676475335756653)
                  ·
                    refine ⟨199998661003678250908745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 533329762676475335756653 199998661003678250908745)
                    ·
                      rfl

theorem cell22_584244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_584244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584244 prefixEnd_584244 := by exact prefixLift 584244
  have htrace : WordTrace (prefixWord ++ tailWord_584244) baseStart_584244 baseEnd_584244 := by
    simpa [prefixWord, tailWord_584244, baseEnd_584244] using wordTrace_append hprefix tailTrace_584244
  have hstable : (prefixWord ++ tailWord_584244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584244).length < 2 ^ (prefixWord ++ tailWord_584244).sum := by decide
  have hdescent : baseEnd_584244 < baseStart_584244 := by decide
  rcases family_descends (prefixWord ++ tailWord_584244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584249 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_584249 : Nat := 118140960795 + 584249 * 2 ^ 59
def prefixEnd_584249 : Nat := 4983230072969 + 3 ^ 40 * 584249 * 2
def baseEnd_584249 : Nat := 200000372605859904533729

theorem tailTrace_584249 : CollatzResearch.WordTrace tailWord_584249 prefixEnd_584249 200000372605859904533729 := by
  unfold tailWord_584249
  simp only [CollatzResearch.WordTrace]
  refine ⟨21309311660373129630275801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14206207773582086420183867 21309311660373129630275801)
  ·
    refine ⟨15981983745279847222706851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21309311660373129630275801 15981983745279847222706851)
    ·
      refine ⟨23972975617919770834060277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15981983745279847222706851 23972975617919770834060277)
      ·
        refine ⟨2247466464179978515693151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23972975617919770834060277 2247466464179978515693151)
        ·
          refine ⟨3371199696269967773539727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247466464179978515693151 3371199696269967773539727)
          ·
            refine ⟨5056799544404951660309591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371199696269967773539727 5056799544404951660309591)
            ·
              refine ⟨7585199316607427490464387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5056799544404951660309591 7585199316607427490464387)
              ·
                refine ⟨11377798974911141235696581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7585199316607427490464387 11377798974911141235696581)
                ·
                  refine ⟨2133337307795838981693109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11377798974911141235696581 2133337307795838981693109)
                  ·
                    refine ⟨200000372605859904533729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2133337307795838981693109 200000372605859904533729)
                    ·
                      rfl

theorem cell22_584249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_584249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584249 prefixEnd_584249 := by exact prefixLift 584249
  have htrace : WordTrace (prefixWord ++ tailWord_584249) baseStart_584249 baseEnd_584249 := by
    simpa [prefixWord, tailWord_584249, baseEnd_584249] using wordTrace_append hprefix tailTrace_584249
  have hstable : (prefixWord ++ tailWord_584249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584249).length < 2 ^ (prefixWord ++ tailWord_584249).sum := by decide
  have hdescent : baseEnd_584249 < baseStart_584249 := by decide
  rcases family_descends (prefixWord ++ tailWord_584249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584264 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_584264 : Nat := 118140960795 + 584264 * 2 ^ 59
def prefixEnd_584264 : Nat := 4983230072969 + 3 ^ 40 * 584264 * 2
def baseEnd_584264 : Nat := 200005507412404865408683

theorem tailTrace_584264 : CollatzResearch.WordTrace tailWord_584264 prefixEnd_584264 200005507412404865408683 := by
  unfold tailWord_584264
  simp only [CollatzResearch.WordTrace]
  refine ⟨10654929377659393596035923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14206572503545858128047897 10654929377659393596035923)
  ·
    refine ⟨15982394066489090394053885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10654929377659393596035923 15982394066489090394053885)
    ·
      refine ⟨5993397774933408897770207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15982394066489090394053885 5993397774933408897770207)
      ·
        refine ⟨8990096662400113346655311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5993397774933408897770207 8990096662400113346655311)
        ·
          refine ⟨13485144993600170019982967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8990096662400113346655311 13485144993600170019982967)
          ·
            refine ⟨20227717490400255029974451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13485144993600170019982967 20227717490400255029974451)
            ·
              refine ⟨30341576235600382544961677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20227717490400255029974451 30341576235600382544961677)
              ·
                refine ⟨11378091088350143454360629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30341576235600382544961677 11378091088350143454360629)
                ·
                  refine ⟨1066696039532825948846309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11378091088350143454360629 1066696039532825948846309)
                  ·
                    refine ⟨200005507412404865408683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1066696039532825948846309 200005507412404865408683)
                    ·
                      rfl

theorem cell22_584264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_584264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584264 prefixEnd_584264 := by exact prefixLift 584264
  have htrace : WordTrace (prefixWord ++ tailWord_584264) baseStart_584264 baseEnd_584264 := by
    simpa [prefixWord, tailWord_584264, baseEnd_584264] using wordTrace_append hprefix tailTrace_584264
  have hstable : (prefixWord ++ tailWord_584264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584264).length < 2 ^ (prefixWord ++ tailWord_584264).sum := by decide
  have hdescent : baseEnd_584264 < baseStart_584264 := by decide
  rcases family_descends (prefixWord ++ tailWord_584264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584279 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 6]
def baseStart_584279 : Nat := 118140960795 + 584279 * 2 ^ 59
def prefixEnd_584279 : Nat := 4983230072969 + 3 ^ 40 * 584279 * 2
def baseEnd_584279 : Nat := 66670214072983275427879

theorem tailTrace_584279 : CollatzResearch.WordTrace tailWord_584279 prefixEnd_584279 66670214072983275427879 := by
  unfold tailWord_584279
  simp only [CollatzResearch.WordTrace]
  refine ⟨21310405850264444753867891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14206937233509629835911927 21310405850264444753867891)
  ·
    refine ⟨31965608775396667130801837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21310405850264444753867891 31965608775396667130801837)
    ·
      refine ⟨11987103290773750174050689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31965608775396667130801837 11987103290773750174050689)
      ·
        refine ⟨8990327468080312630538017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11987103290773750174050689 8990327468080312630538017)
        ·
          refine ⟨6742745601060234472903513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8990327468080312630538017 6742745601060234472903513)
          ·
            refine ⟨5057059200795175854677635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6742745601060234472903513 5057059200795175854677635)
            ·
              refine ⟨7585588801192763782016453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057059200795175854677635 7585588801192763782016453)
              ·
                refine ⟨1422297900223643209128085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7585588801192763782016453 1422297900223643209128085)
                ·
                  refine ⟨66670214072983275427879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1422297900223643209128085 66670214072983275427879)
                  ·
                    rfl

theorem cell22_584279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 6].length) (baseStart_584279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584279 prefixEnd_584279 := by exact prefixLift 584279
  have htrace : WordTrace (prefixWord ++ tailWord_584279) baseStart_584279 baseEnd_584279 := by
    simpa [prefixWord, tailWord_584279, baseEnd_584279] using wordTrace_append hprefix tailTrace_584279
  have hstable : (prefixWord ++ tailWord_584279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584279).length < 2 ^ (prefixWord ++ tailWord_584279).sum := by decide
  have hdescent : baseEnd_584279 < baseStart_584279 := by decide
  rcases family_descends (prefixWord ++ tailWord_584279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584311 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 4, 3]
def baseStart_584311 : Nat := 118140960795 + 584311 * 2 ^ 59
def prefixEnd_584311 : Nat := 4983230072969 + 3 ^ 40 * 584311 * 2
def baseEnd_584311 : Nat := 200021596472912409483539

theorem tailTrace_584311 : CollatzResearch.WordTrace tailWord_584311 prefixEnd_584311 200021596472912409483539 := by
  unfold tailWord_584311
  simp only [CollatzResearch.WordTrace]
  refine ⟨21311572986148514219032787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14207715324099009479355191 21311572986148514219032787)
  ·
    refine ⟨31967359479222771328549181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21311572986148514219032787 31967359479222771328549181)
    ·
      refine ⟨11987759804708539248205943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31967359479222771328549181 11987759804708539248205943)
      ·
        refine ⟨17981639707062808872308915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11987759804708539248205943 17981639707062808872308915)
        ·
          refine ⟨26972459560594213308463373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17981639707062808872308915 26972459560594213308463373)
          ·
            refine ⟨10114672335222829990673765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26972459560594213308463373 10114672335222829990673765)
            ·
              refine ⟨1896501062854280623251331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10114672335222829990673765 1896501062854280623251331)
              ·
                refine ⟨2844751594281420934876997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896501062854280623251331 2844751594281420934876997)
                ·
                  refine ⟨533390923927766425289437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2844751594281420934876997 533390923927766425289437)
                  ·
                    refine ⟨200021596472912409483539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 533390923927766425289437 200021596472912409483539)
                    ·
                      rfl

theorem cell22_584311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_584311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584311 prefixEnd_584311 := by exact prefixLift 584311
  have htrace : WordTrace (prefixWord ++ tailWord_584311) baseStart_584311 baseEnd_584311 := by
    simpa [prefixWord, tailWord_584311, baseEnd_584311] using wordTrace_append hprefix tailTrace_584311
  have hstable : (prefixWord ++ tailWord_584311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584311).length < 2 ^ (prefixWord ++ tailWord_584311).sum := by decide
  have hdescent : baseEnd_584311 < baseStart_584311 := by decide
  rcases family_descends (prefixWord ++ tailWord_584311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584431 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 6]
def baseStart_584431 : Nat := 118140960795 + 584431 * 2 ^ 59
def prefixEnd_584431 : Nat := 4983230072969 + 3 ^ 40 * 584431 * 2
def baseEnd_584431 : Nat := 66687558308424032161057

theorem tailTrace_584431 : CollatzResearch.WordTrace tailWord_584431 prefixEnd_584431 66687558308424032161057 := by
  unfold tailWord_584431
  simp only [CollatzResearch.WordTrace]
  refine ⟨21315949745713774713401147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14210633163809183142267431 21315949745713774713401147)
  ·
    refine ⟨31973924618570662070101721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21315949745713774713401147 31973924618570662070101721)
    ·
      refine ⟨23980443463927996552576291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31973924618570662070101721 23980443463927996552576291)
      ·
        refine ⟨35970665195891994828864437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23980443463927996552576291 35970665195891994828864437)
        ·
          refine ⟨3372249862114874515206041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35970665195891994828864437 3372249862114874515206041)
          ·
            refine ⟨2529187396586155886404531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3372249862114874515206041 2529187396586155886404531)
            ·
              refine ⟨3793781094879233829606797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529187396586155886404531 3793781094879233829606797)
              ·
                refine ⟨1422667910579712686102549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3793781094879233829606797 1422667910579712686102549)
                ·
                  refine ⟨66687558308424032161057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1422667910579712686102549 66687558308424032161057)
                  ·
                    rfl

theorem cell22_584431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 6].length) (baseStart_584431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584431 prefixEnd_584431 := by exact prefixLift 584431
  have htrace : WordTrace (prefixWord ++ tailWord_584431) baseStart_584431 baseEnd_584431 := by
    simpa [prefixWord, tailWord_584431, baseEnd_584431] using wordTrace_append hprefix tailTrace_584431
  have hstable : (prefixWord ++ tailWord_584431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584431).length < 2 ^ (prefixWord ++ tailWord_584431).sum := by decide
  have hdescent : baseEnd_584431 < baseStart_584431 := by decide
  rcases family_descends (prefixWord ++ tailWord_584431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584450 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_584450 : Nat := 118140960795 + 584450 * 2 ^ 59
def prefixEnd_584450 : Nat := 4983230072969 + 3 ^ 40 * 584450 * 2
def baseEnd_584450 : Nat := 200069179013562380258113

theorem tailTrace_584450 : CollatzResearch.WordTrace tailWord_584450 prefixEnd_584450 200069179013562380258113 := by
  unfold tailWord_584450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5329160683161235239585701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14211095155096627305561869 5329160683161235239585701)
  ·
    refine ⟨999217628092731607422319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5329160683161235239585701 999217628092731607422319)
    ·
      refine ⟨1498826442139097411133479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 999217628092731607422319 1498826442139097411133479)
      ·
        refine ⟨2248239663208646116700219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498826442139097411133479 2248239663208646116700219)
        ·
          refine ⟨3372359494812969175050329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248239663208646116700219 3372359494812969175050329)
          ·
            refine ⟨2529269621109726881287747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3372359494812969175050329 2529269621109726881287747)
            ·
              refine ⟨3793904431664590321931621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529269621109726881287747 3793904431664590321931621)
              ·
                refine ⟨711357080937110685362179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3793904431664590321931621 711357080937110685362179)
                ·
                  refine ⟨1067035621405666028043269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711357080937110685362179 1067035621405666028043269)
                  ·
                    refine ⟨200069179013562380258113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1067035621405666028043269 200069179013562380258113)
                    ·
                      rfl

theorem cell22_584450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_584450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584450 prefixEnd_584450 := by exact prefixLift 584450
  have htrace : WordTrace (prefixWord ++ tailWord_584450) baseStart_584450 baseEnd_584450 := by
    simpa [prefixWord, tailWord_584450, baseEnd_584450] using wordTrace_append hprefix tailTrace_584450
  have hstable : (prefixWord ++ tailWord_584450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584450).length < 2 ^ (prefixWord ++ tailWord_584450).sum := by decide
  have hdescent : baseEnd_584450 < baseStart_584450 := by decide
  rcases family_descends (prefixWord ++ tailWord_584450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584476 : List Nat := [2, 2, 3, 1, 1, 3, 10]
def baseStart_584476 : Nat := 118140960795 + 584476 * 2 ^ 59
def prefixEnd_584476 : Nat := 4983230072969 + 3 ^ 40 * 584476 * 2
def baseEnd_584476 : Nat := 7410299234996554781779

theorem tailTrace_584476 : CollatzResearch.WordTrace tailWord_584476 prefixEnd_584476 7410299234996554781779 := by
  unfold tailWord_584476
  simp only [CollatzResearch.WordTrace]
  refine ⟨10658795515275373699394641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14211727353700498265859521 10658795515275373699394641)
  ·
    refine ⟨7994096636456530274545981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10658795515275373699394641 7994096636456530274545981)
    ·
      refine ⟨2997786238671198852954743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7994096636456530274545981 2997786238671198852954743)
      ·
        refine ⟨4496679358006798279432115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2997786238671198852954743 4496679358006798279432115)
        ·
          refine ⟨6745019037010197419148173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4496679358006798279432115 6745019037010197419148173)
          ·
            refine ⟨2529382138878824032180565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6745019037010197419148173 2529382138878824032180565)
            ·
              refine ⟨7410299234996554781779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2529382138878824032180565 7410299234996554781779)
              ·
                rfl

theorem cell22_584476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 10].length) (baseStart_584476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584476 prefixEnd_584476 := by exact prefixLift 584476
  have htrace : WordTrace (prefixWord ++ tailWord_584476) baseStart_584476 baseEnd_584476 := by
    simpa [prefixWord, tailWord_584476, baseEnd_584476] using wordTrace_append hprefix tailTrace_584476
  have hstable : (prefixWord ++ tailWord_584476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584476).length < 2 ^ (prefixWord ++ tailWord_584476).sum := by decide
  have hdescent : baseEnd_584476 < baseStart_584476 := by decide
  rcases family_descends (prefixWord ++ tailWord_584476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584482 : List Nat := [3, 3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_584482 : Nat := 118140960795 + 584482 * 2 ^ 59
def prefixEnd_584482 : Nat := 4983230072969 + 3 ^ 40 * 584482 * 2
def baseEnd_584482 : Nat := 66693377755841654486005

theorem tailTrace_584482 : CollatzResearch.WordTrace tailWord_584482 prefixEnd_584482 66693377755841654486005 := by
  unfold tailWord_584482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5329452467132252605876925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14211873245686006949005133 5329452467132252605876925)
  ·
    refine ⟨1998544675174594727203847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5329452467132252605876925 1998544675174594727203847)
    ·
      refine ⟨2997817012761892090805771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1998544675174594727203847 2997817012761892090805771)
      ·
        refine ⟨4496725519142838136208657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2997817012761892090805771 4496725519142838136208657)
        ·
          refine ⟨3372544139357128602156493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4496725519142838136208657 3372544139357128602156493)
          ·
            refine ⟨1264704052258923225808685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3372544139357128602156493 1264704052258923225808685)
            ·
              refine ⟨474264019597096209678257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1264704052258923225808685 474264019597096209678257)
              ·
                refine ⟨355698014697822157258693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474264019597096209678257 355698014697822157258693)
                ·
                  refine ⟨66693377755841654486005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355698014697822157258693 66693377755841654486005)
                  ·
                    rfl

theorem cell22_584482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_584482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584482 prefixEnd_584482 := by exact prefixLift 584482
  have htrace : WordTrace (prefixWord ++ tailWord_584482) baseStart_584482 baseEnd_584482 := by
    simpa [prefixWord, tailWord_584482, baseEnd_584482] using wordTrace_append hprefix tailTrace_584482
  have hstable : (prefixWord ++ tailWord_584482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584482).length < 2 ^ (prefixWord ++ tailWord_584482).sum := by decide
  have hdescent : baseEnd_584482 < baseStart_584482 := by decide
  rcases family_descends (prefixWord ++ tailWord_584482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584508 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 5, 3]
def baseStart_584508 : Nat := 118140960795 + 584508 * 2 ^ 59
def prefixEnd_584508 : Nat := 4983230072969 + 3 ^ 40 * 584508 * 2
def baseEnd_584508 : Nat := 200089033598869562307935

theorem tailTrace_584508 : CollatzResearch.WordTrace tailWord_584508 prefixEnd_584508 200089033598869562307935 := by
  unfold tailWord_584508
  simp only [CollatzResearch.WordTrace]
  refine ⟨10659379083217408431977089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14212505444289877909302785 10659379083217408431977089)
  ·
    refine ⟨7994534312413056323982817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10659379083217408431977089 7994534312413056323982817)
    ·
      refine ⟨5995900734309792242987113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7994534312413056323982817 5995900734309792242987113)
      ·
        refine ⟨4496925550732344182240335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5995900734309792242987113 4496925550732344182240335)
        ·
          refine ⟨6745388326098516273360503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4496925550732344182240335 6745388326098516273360503)
          ·
            refine ⟨10118082489147774410040755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6745388326098516273360503 10118082489147774410040755)
            ·
              refine ⟨15177123733721661615061133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10118082489147774410040755 15177123733721661615061133)
              ·
                refine ⟨5691421400145623105647925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15177123733721661615061133 5691421400145623105647925)
                ·
                  refine ⟨533570756263652166154493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5691421400145623105647925 533570756263652166154493)
                  ·
                    refine ⟨200089033598869562307935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 533570756263652166154493 200089033598869562307935)
                    ·
                      rfl

theorem cell22_584508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_584508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584508 prefixEnd_584508 := by exact prefixLift 584508
  have htrace : WordTrace (prefixWord ++ tailWord_584508) baseStart_584508 baseEnd_584508 := by
    simpa [prefixWord, tailWord_584508, baseEnd_584508] using wordTrace_append hprefix tailTrace_584508
  have hstable : (prefixWord ++ tailWord_584508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584508).length < 2 ^ (prefixWord ++ tailWord_584508).sum := by decide
  have hdescent : baseEnd_584508 < baseStart_584508 := by decide
  rcases family_descends (prefixWord ++ tailWord_584508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584536 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_584536 : Nat := 118140960795 + 584536 * 2 ^ 59
def prefixEnd_584536 : Nat := 4983230072969 + 3 ^ 40 * 584536 * 2
def baseEnd_584536 : Nat := 200098618571086822607849

theorem tailTrace_584536 : CollatzResearch.WordTrace tailWord_584536 prefixEnd_584536 200098618571086822607849 := by
  unfold tailWord_584536
  simp only [CollatzResearch.WordTrace]
  refine ⟨10659889705166688822986731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14213186273555585097315641 10659889705166688822986731)
  ·
    refine ⟨15989834557750033234480097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10659889705166688822986731 15989834557750033234480097)
    ·
      refine ⟨11992375918312524925860073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15989834557750033234480097 11992375918312524925860073)
      ·
        refine ⟨8994281938734393694395055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11992375918312524925860073 8994281938734393694395055)
        ·
          refine ⟨13491422908101590541592583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8994281938734393694395055 13491422908101590541592583)
          ·
            refine ⟨20237134362152385812388875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13491422908101590541592583 20237134362152385812388875)
            ·
              refine ⟨30355701543228578718583313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20237134362152385812388875 30355701543228578718583313)
              ·
                refine ⟨22766776157421434038937485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30355701543228578718583313 22766776157421434038937485)
                ·
                  refine ⟨8537541059033037764601557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22766776157421434038937485 8537541059033037764601557)
                  ·
                    refine ⟨200098618571086822607849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8537541059033037764601557 200098618571086822607849)
                    ·
                      rfl

theorem cell22_584536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_584536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584536 prefixEnd_584536 := by exact prefixLift 584536
  have htrace : WordTrace (prefixWord ++ tailWord_584536) baseStart_584536 baseEnd_584536 := by
    simpa [prefixWord, tailWord_584536, baseEnd_584536] using wordTrace_append hprefix tailTrace_584536
  have hstable : (prefixWord ++ tailWord_584536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584536).length < 2 ^ (prefixWord ++ tailWord_584536).sum := by decide
  have hdescent : baseEnd_584536 < baseStart_584536 := by decide
  rcases family_descends (prefixWord ++ tailWord_584536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584538 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_584538 : Nat := 118140960795 + 584538 * 2 ^ 59
def prefixEnd_584538 : Nat := 4983230072969 + 3 ^ 40 * 584538 * 2
def baseEnd_584538 : Nat := 66699767737319828019281

theorem tailTrace_584538 : CollatzResearch.WordTrace tailWord_584538 prefixEnd_584538 66699767737319828019281 := by
  unfold tailWord_584538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5329963089081532996886567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14213234904217421325030845 5329963089081532996886567)
  ·
    refine ⟨7994944633622299495329851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5329963089081532996886567 7994944633622299495329851)
    ·
      refine ⟨11992416950433449242994777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7994944633622299495329851 11992416950433449242994777)
      ·
        refine ⟨8994312712825086932246083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11992416950433449242994777 8994312712825086932246083)
        ·
          refine ⟨13491469069237630398369125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8994312712825086932246083 13491469069237630398369125)
          ·
            refine ⟨2529650450482055699694211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13491469069237630398369125 2529650450482055699694211)
            ·
              refine ⟨3794475675723083549541317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529650450482055699694211 3794475675723083549541317)
              ·
                refine ⟨711464189198078165538997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3794475675723083549541317 711464189198078165538997)
                ·
                  refine ⟨66699767737319828019281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 711464189198078165538997 66699767737319828019281)
                  ·
                    rfl

theorem cell22_584538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_584538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584538 prefixEnd_584538 := by exact prefixLift 584538
  have htrace : WordTrace (prefixWord ++ tailWord_584538) baseStart_584538 baseEnd_584538 := by
    simpa [prefixWord, tailWord_584538, baseEnd_584538] using wordTrace_append hprefix tailTrace_584538
  have hstable : (prefixWord ++ tailWord_584538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584538).length < 2 ^ (prefixWord ++ tailWord_584538).sum := by decide
  have hdescent : baseEnd_584538 < baseStart_584538 := by decide
  rcases family_descends (prefixWord ++ tailWord_584538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584585 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 1, 4]
def baseStart_584585 : Nat := 118140960795 + 584585 * 2 ^ 59
def prefixEnd_584585 : Nat := 4983230072969 + 3 ^ 40 * 584585 * 2
def baseEnd_584585 : Nat := 200115392272467028132699

theorem tailTrace_584585 : CollatzResearch.WordTrace tailWord_584585 prefixEnd_584585 200115392272467028132699 := by
  unfold tailWord_584585
  simp only [CollatzResearch.WordTrace]
  refine ⟨21321566587155859014507209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14214377724770572676338139 21321566587155859014507209)
  ·
    refine ⟨15991174940366894260880407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21321566587155859014507209 15991174940366894260880407)
    ·
      refine ⟨23986762410550341391320611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15991174940366894260880407 23986762410550341391320611)
      ·
        refine ⟨35980143615825512086980917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23986762410550341391320611 35980143615825512086980917)
        ·
          refine ⟨3373138463983641758154461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35980143615825512086980917 3373138463983641758154461)
          ·
            refine ⟨1264926923993865659307923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3373138463983641758154461 1264926923993865659307923)
            ·
              refine ⟨1897390385990798488961885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264926923993865659307923 1897390385990798488961885)
              ·
                refine ⟨711521394746549433360707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1897390385990798488961885 711521394746549433360707)
                ·
                  refine ⟨1067282092119824150041061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711521394746549433360707 1067282092119824150041061)
                  ·
                    refine ⟨200115392272467028132699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1067282092119824150041061 200115392272467028132699)
                    ·
                      rfl

theorem cell22_584585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_584585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584585 prefixEnd_584585 := by exact prefixLift 584585
  have htrace : WordTrace (prefixWord ++ tailWord_584585) baseStart_584585 baseEnd_584585 := by
    simpa [prefixWord, tailWord_584585, baseEnd_584585] using wordTrace_append hprefix tailTrace_584585
  have hstable : (prefixWord ++ tailWord_584585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584585).length < 2 ^ (prefixWord ++ tailWord_584585).sum := by decide
  have hdescent : baseEnd_584585 < baseStart_584585 := by decide
  rcases family_descends (prefixWord ++ tailWord_584585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584662 : List Nat := [5, 2, 1, 1, 2, 2, 2, 7]
def baseStart_584662 : Nat := 118140960795 + 584662 * 2 ^ 59
def prefixEnd_584662 : Nat := 4983230072969 + 3 ^ 40 * 584662 * 2
def baseEnd_584662 : Nat := 22237972327340499328607

theorem tailTrace_584662 : CollatzResearch.WordTrace tailWord_584662 prefixEnd_584662 22237972327340499328607 := by
  unfold tailWord_584662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1332773437992306322816265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14216250005251267443373493 1332773437992306322816265)
  ·
    refine ⟨999580078494229742112199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1332773437992306322816265 999580078494229742112199)
    ·
      refine ⟨1499370117741344613168299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 999580078494229742112199 1499370117741344613168299)
      ·
        refine ⟨2249055176612016919752449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1499370117741344613168299 2249055176612016919752449)
        ·
          refine ⟨1686791382459012689814337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2249055176612016919752449 1686791382459012689814337)
          ·
            refine ⟨1265093536844259517360753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686791382459012689814337 1265093536844259517360753)
            ·
              refine ⟨948820152633194638020565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265093536844259517360753 948820152633194638020565)
              ·
                refine ⟨22237972327340499328607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 948820152633194638020565 22237972327340499328607)
                ·
                  rfl

theorem cell22_584662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_584662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584662 prefixEnd_584662 := by exact prefixLift 584662
  have htrace : WordTrace (prefixWord ++ tailWord_584662) baseStart_584662 baseEnd_584662 := by
    simpa [prefixWord, tailWord_584662, baseEnd_584662] using wordTrace_append hprefix tailTrace_584662
  have hstable : (prefixWord ++ tailWord_584662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584662).length < 2 ^ (prefixWord ++ tailWord_584662).sum := by decide
  have hdescent : baseEnd_584662 < baseStart_584662 := by decide
  rcases family_descends (prefixWord ++ tailWord_584662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584688 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_584688 : Nat := 118140960795 + 584688 * 2 ^ 59
def prefixEnd_584688 : Nat := 4983230072969 + 3 ^ 40 * 584688 * 2
def baseEnd_584688 : Nat := 200150651277409092807383

theorem tailTrace_584688 : CollatzResearch.WordTrace tailWord_584688 prefixEnd_584688 200150651277409092807383 := by
  unfold tailWord_584688
  simp only [CollatzResearch.WordTrace]
  refine ⟨10662661652891353802753359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14216882203855138403671145 10662661652891353802753359)
  ·
    refine ⟨15993992479337030704130039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10662661652891353802753359 15993992479337030704130039)
    ·
      refine ⟨23990988719005546056195059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15993992479337030704130039 23990988719005546056195059)
      ·
        refine ⟨35986483078508319084292589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23990988719005546056195059 35986483078508319084292589)
        ·
          refine ⟨13494931154440619656609721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35986483078508319084292589 13494931154440619656609721)
          ·
            refine ⟨10121198365830464742457291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13494931154440619656609721 10121198365830464742457291)
            ·
              refine ⟨15181797548745697113685937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10121198365830464742457291 15181797548745697113685937)
              ·
                refine ⟨11386348161559272835264453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15181797548745697113685937 11386348161559272835264453)
                ·
                  refine ⟨2134940280292363656612085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11386348161559272835264453 2134940280292363656612085)
                  ·
                    refine ⟨200150651277409092807383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2134940280292363656612085 200150651277409092807383)
                    ·
                      rfl

theorem cell22_584688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_584688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584688 prefixEnd_584688 := by exact prefixLift 584688
  have htrace : WordTrace (prefixWord ++ tailWord_584688) baseStart_584688 baseEnd_584688 := by
    simpa [prefixWord, tailWord_584688, baseEnd_584688] using wordTrace_append hprefix tailTrace_584688
  have hstable : (prefixWord ++ tailWord_584688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584688).length < 2 ^ (prefixWord ++ tailWord_584688).sum := by decide
  have hdescent : baseEnd_584688 < baseStart_584688 := by decide
  rcases family_descends (prefixWord ++ tailWord_584688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584735 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 6]
def baseStart_584735 : Nat := 118140960795 + 584735 * 2 ^ 59
def prefixEnd_584735 : Nat := 4983230072969 + 3 ^ 40 * 584735 * 2
def baseEnd_584735 : Nat := 66722246779305545627413

theorem tailTrace_584735 : CollatzResearch.WordTrace tailWord_584735 prefixEnd_584735 66722246779305545627413 := by
  unfold tailWord_584735
  simp only [CollatzResearch.WordTrace]
  refine ⟨21327037536612434632467659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14218025024408289754978439 21327037536612434632467659)
  ·
    refine ⟨31990556304918651948701489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21327037536612434632467659 31990556304918651948701489)
    ·
      refine ⟨23992917228688988961526117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31990556304918651948701489 23992917228688988961526117)
      ·
        refine ⟨4498671980379185430286147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23992917228688988961526117 4498671980379185430286147)
        ·
          refine ⟨6748007970568778145429221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4498671980379185430286147 6748007970568778145429221)
          ·
            refine ⟨1265251494481645902267979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6748007970568778145429221 1265251494481645902267979)
            ·
              refine ⟨1897877241722468853401969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265251494481645902267979 1897877241722468853401969)
              ·
                refine ⟨1423407931291851640051477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1897877241722468853401969 1423407931291851640051477)
                ·
                  refine ⟨66722246779305545627413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1423407931291851640051477 66722246779305545627413)
                  ·
                    rfl

theorem cell22_584735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 6].length) (baseStart_584735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584735 prefixEnd_584735 := by exact prefixLift 584735
  have htrace : WordTrace (prefixWord ++ tailWord_584735) baseStart_584735 baseEnd_584735 := by
    simpa [prefixWord, tailWord_584735, baseEnd_584735] using wordTrace_append hprefix tailTrace_584735
  have hstable : (prefixWord ++ tailWord_584735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584735).length < 2 ^ (prefixWord ++ tailWord_584735).sum := by decide
  have hdescent : baseEnd_584735 < baseStart_584735 := by decide
  rcases family_descends (prefixWord ++ tailWord_584735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584752 : List Nat := [2, 1, 1, 1, 2, 4, 4, 3, 4]
def baseStart_584752 : Nat := 118140960795 + 584752 * 2 ^ 59
def prefixEnd_584752 : Nat := 4983230072969 + 3 ^ 40 * 584752 * 2
def baseEnd_584752 : Nat := 66724186595111419735729

theorem tailTrace_584752 : CollatzResearch.WordTrace tailWord_584752 prefixEnd_584752 66724186595111419735729 := by
  unfold tailWord_584752
  simp only [CollatzResearch.WordTrace]
  refine ⟨10663828788775423267918255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14218438385033897690557673 10663828788775423267918255)
  ·
    refine ⟨15995743183163134901877383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10663828788775423267918255 15995743183163134901877383)
    ·
      refine ⟨23993614774744702352816075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15995743183163134901877383 23993614774744702352816075)
      ·
        refine ⟨35990422162117053529224113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23993614774744702352816075 35990422162117053529224113)
        ·
          refine ⟨26992816621587790146918085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35990422162117053529224113 26992816621587790146918085)
          ·
            refine ⟨5061153116547710652547141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26992816621587790146918085 5061153116547710652547141)
            ·
              refine ⟨948966209352695747352589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5061153116547710652547141 948966209352695747352589)
              ·
                refine ⟨355862328507260905257221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 948966209352695747352589 355862328507260905257221)
                ·
                  refine ⟨66724186595111419735729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355862328507260905257221 66724186595111419735729)
                  ·
                    rfl

theorem cell22_584752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 4].length) (baseStart_584752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584752 prefixEnd_584752 := by exact prefixLift 584752
  have htrace : WordTrace (prefixWord ++ tailWord_584752) baseStart_584752 baseEnd_584752 := by
    simpa [prefixWord, tailWord_584752, baseEnd_584752] using wordTrace_append hprefix tailTrace_584752
  have hstable : (prefixWord ++ tailWord_584752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584752).length < 2 ^ (prefixWord ++ tailWord_584752).sum := by decide
  have hdescent : baseEnd_584752 < baseStart_584752 := by decide
  rcases family_descends (prefixWord ++ tailWord_584752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584842 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_584842 : Nat := 118140960795 + 584842 * 2 ^ 59
def prefixEnd_584842 : Nat := 4983230072969 + 3 ^ 40 * 584842 * 2
def baseEnd_584842 : Nat := 66734456208201341485637

theorem tailTrace_584842 : CollatzResearch.WordTrace tailWord_584842 prefixEnd_584842 66734456208201341485637 := by
  unfold tailWord_584842
  simp only [CollatzResearch.WordTrace]
  refine ⟨5332735036806197976653195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14220626764816527937741853 5332735036806197976653195)
  ·
    refine ⟨7999102555209296964979793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5332735036806197976653195 7999102555209296964979793)
    ·
      refine ⟨5999326916406972723734845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7999102555209296964979793 5999326916406972723734845)
      ·
        refine ⟨2249747593652614771400567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5999326916406972723734845 2249747593652614771400567)
        ·
          refine ⟨3374621390478922157100851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2249747593652614771400567 3374621390478922157100851)
          ·
            refine ⟨5061932085718383235651277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3374621390478922157100851 5061932085718383235651277)
            ·
              refine ⟨1898224532144393713369229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5061932085718383235651277 1898224532144393713369229)
              ·
                refine ⟨711834199554147642513461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898224532144393713369229 711834199554147642513461)
                ·
                  refine ⟨66734456208201341485637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 711834199554147642513461 66734456208201341485637)
                  ·
                    rfl

theorem cell22_584842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_584842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_584842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_584842 prefixEnd_584842 := by exact prefixLift 584842
  have htrace : WordTrace (prefixWord ++ tailWord_584842) baseStart_584842 baseEnd_584842 := by
    simpa [prefixWord, tailWord_584842, baseEnd_584842] using wordTrace_append hprefix tailTrace_584842
  have hstable : (prefixWord ++ tailWord_584842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584842).length < 2 ^ (prefixWord ++ tailWord_584842).sum := by decide
  have hdescent : baseEnd_584842 < baseStart_584842 := by decide
  rcases family_descends (prefixWord ++ tailWord_584842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585007 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 3, 4]
def baseStart_585007 : Nat := 118140960795 + 585007 * 2 ^ 59
def prefixEnd_585007 : Nat := 4983230072969 + 3 ^ 40 * 585007 * 2
def baseEnd_585007 : Nat := 200259851496598594081405

theorem tailTrace_585007 : CollatzResearch.WordTrace tailWord_585007 prefixEnd_585007 200259851496598594081405 := by
  unfold tailWord_585007
  simp only [CollatzResearch.WordTrace]
  refine ⟨21336958191627025086369275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14224638794418016724246183 21336958191627025086369275)
  ·
    refine ⟨32005437287440537629553913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21336958191627025086369275 32005437287440537629553913)
    ·
      refine ⟨24004077965580403222165435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32005437287440537629553913 24004077965580403222165435)
      ·
        refine ⟨36006116948370604833248153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24004077965580403222165435 36006116948370604833248153)
        ·
          refine ⟨27004587711277953624936115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36006116948370604833248153 27004587711277953624936115)
          ·
            refine ⟨40506881566916930437404173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27004587711277953624936115 40506881566916930437404173)
            ·
              refine ⟨15190080587593848914026565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40506881566916930437404173 15190080587593848914026565)
              ·
                refine ⟨2848140110173846671379981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15190080587593848914026565 2848140110173846671379981)
                ·
                  refine ⟨1068052541315192501767493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2848140110173846671379981 1068052541315192501767493)
                  ·
                    refine ⟨200259851496598594081405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1068052541315192501767493 200259851496598594081405)
                    ·
                      rfl

theorem cell22_585007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_585007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585007 prefixEnd_585007 := by exact prefixLift 585007
  have htrace : WordTrace (prefixWord ++ tailWord_585007) baseStart_585007 baseEnd_585007 := by
    simpa [prefixWord, tailWord_585007, baseEnd_585007] using wordTrace_append hprefix tailTrace_585007
  have hstable : (prefixWord ++ tailWord_585007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585007).length < 2 ^ (prefixWord ++ tailWord_585007).sum := by decide
  have hdescent : baseEnd_585007 < baseStart_585007 := by decide
  rcases family_descends (prefixWord ++ tailWord_585007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585011 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 5]
def baseStart_585011 : Nat := 118140960795 + 585011 * 2 ^ 59
def prefixEnd_585011 : Nat := 4983230072969 + 3 ^ 40 * 585011 * 2
def baseEnd_585011 : Nat := 66753740259447972327131

theorem tailTrace_585011 : CollatzResearch.WordTrace tailWord_585011 prefixEnd_585011 66753740259447972327131 := by
  unfold tailWord_585011
  simp only [CollatzResearch.WordTrace]
  refine ⟨21337104083612533769514887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14224736055741689179676591 21337104083612533769514887)
  ·
    refine ⟨32005656125418800654272331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21337104083612533769514887 32005656125418800654272331)
    ·
      refine ⟨48008484188128200981408497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32005656125418800654272331 48008484188128200981408497)
      ·
        refine ⟨36006363141096150736056373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48008484188128200981408497 36006363141096150736056373)
        ·
          refine ⟨3375596544477764131505285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36006363141096150736056373 3375596544477764131505285)
          ·
            refine ⟨632924352089580774657241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3375596544477764131505285 632924352089580774657241)
            ·
              refine ⟨474693264067185580992931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632924352089580774657241 474693264067185580992931)
              ·
                refine ⟨712039896100778371489397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474693264067185580992931 712039896100778371489397)
                ·
                  refine ⟨66753740259447972327131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 712039896100778371489397 66753740259447972327131)
                  ·
                    rfl

theorem cell22_585011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 5].length) (baseStart_585011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585011 prefixEnd_585011 := by exact prefixLift 585011
  have htrace : WordTrace (prefixWord ++ tailWord_585011) baseStart_585011 baseEnd_585011 := by
    simpa [prefixWord, tailWord_585011, baseEnd_585011] using wordTrace_append hprefix tailTrace_585011
  have hstable : (prefixWord ++ tailWord_585011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585011).length < 2 ^ (prefixWord ++ tailWord_585011).sum := by decide
  have hdescent : baseEnd_585011 < baseStart_585011 := by decide
  rcases family_descends (prefixWord ++ tailWord_585011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585041 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 1, 4]
def baseStart_585041 : Nat := 118140960795 + 585041 * 2 ^ 59
def prefixEnd_585041 : Nat := 4983230072969 + 3 ^ 40 * 585041 * 2
def baseEnd_585041 : Nat := 200271490391433838731301

theorem tailTrace_585041 : CollatzResearch.WordTrace tailWord_585041 prefixEnd_585041 200271490391433838731301 := by
  unfold tailWord_585041
  simp only [CollatzResearch.WordTrace]
  refine ⟨21338198273503848893106977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14225465515669232595404651 21338198273503848893106977)
  ·
    refine ⟨16003648705127886669830233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21338198273503848893106977 16003648705127886669830233)
    ·
      refine ⟨12002736528845915002372675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16003648705127886669830233 12002736528845915002372675)
      ·
        refine ⟨18004104793268872503559013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12002736528845915002372675 18004104793268872503559013)
        ·
          refine ⟨3375769648737913594417315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18004104793268872503559013 3375769648737913594417315)
          ·
            refine ⟨5063654473106870391625973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375769648737913594417315 5063654473106870391625973)
            ·
              refine ⟨474717606853769099214935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5063654473106870391625973 474717606853769099214935)
              ·
                refine ⟨712076410280653648822403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474717606853769099214935 712076410280653648822403)
                ·
                  refine ⟨1068114615420980473233605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712076410280653648822403 1068114615420980473233605)
                  ·
                    refine ⟨200271490391433838731301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1068114615420980473233605 200271490391433838731301)
                    ·
                      rfl

theorem cell22_585041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_585041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585041 prefixEnd_585041 := by exact prefixLift 585041
  have htrace : WordTrace (prefixWord ++ tailWord_585041) baseStart_585041 baseEnd_585041 := by
    simpa [prefixWord, tailWord_585041, baseEnd_585041] using wordTrace_append hprefix tailTrace_585041
  have hstable : (prefixWord ++ tailWord_585041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585041).length < 2 ^ (prefixWord ++ tailWord_585041).sum := by decide
  have hdescent : baseEnd_585041 < baseStart_585041 := by decide
  rcases family_descends (prefixWord ++ tailWord_585041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585056 : List Nat := [2, 1, 1, 3, 4, 2, 1, 4, 4]
def baseStart_585056 : Nat := 118140960795 + 585056 * 2 ^ 59
def prefixEnd_585056 : Nat := 4983230072969 + 3 ^ 40 * 585056 * 2
def baseEnd_585056 : Nat := 66758875065992933202085

theorem tailTrace_585056 : CollatzResearch.WordTrace tailWord_585056 prefixEnd_585056 66758875065992933202085 := by
  unfold tailWord_585056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10669372684224753227451511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14225830245633004303268681 10669372684224753227451511)
  ·
    refine ⟨16004059026337129841177267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10669372684224753227451511 16004059026337129841177267)
    ·
      refine ⟨24006088539505694761765901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16004059026337129841177267 24006088539505694761765901)
      ·
        refine ⟨9002283202314635535662213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24006088539505694761765901 9002283202314635535662213)
        ·
          refine ⟨1687928100433994162936665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9002283202314635535662213 1687928100433994162936665)
          ·
            refine ⟨1265946075325495622202499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687928100433994162936665 1265946075325495622202499)
            ·
              refine ⟨1898919112988243433303749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265946075325495622202499 1898919112988243433303749)
              ·
                refine ⟨356047333685295643744453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1898919112988243433303749 356047333685295643744453)
                ·
                  refine ⟨66758875065992933202085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 356047333685295643744453 66758875065992933202085)
                  ·
                    rfl

theorem cell22_585056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 4].length) (baseStart_585056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585056 prefixEnd_585056 := by exact prefixLift 585056
  have htrace : WordTrace (prefixWord ++ tailWord_585056) baseStart_585056 baseEnd_585056 := by
    simpa [prefixWord, tailWord_585056, baseEnd_585056] using wordTrace_append hprefix tailTrace_585056
  have hstable : (prefixWord ++ tailWord_585056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585056).length < 2 ^ (prefixWord ++ tailWord_585056).sum := by decide
  have hdescent : baseEnd_585056 < baseStart_585056 := by decide
  rcases family_descends (prefixWord ++ tailWord_585056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585082 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_585082 : Nat := 118140960795 + 585082 * 2 ^ 59
def prefixEnd_585082 : Nat := 4983230072969 + 3 ^ 40 * 585082 * 2
def baseEnd_585082 : Nat := 200285525529323398456175

theorem tailTrace_585082 : CollatzResearch.WordTrace tailWord_585082 prefixEnd_585082 200285525529323398456175 := by
  unfold tailWord_585082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5334923416588828223837375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14226462444236875263566333 5334923416588828223837375)
  ·
    refine ⟨8002385124883242335756063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5334923416588828223837375 8002385124883242335756063)
    ·
      refine ⟨12003577687324863503634095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8002385124883242335756063 12003577687324863503634095)
      ·
        refine ⟨18005366530987295255451143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12003577687324863503634095 18005366530987295255451143)
        ·
          refine ⟨27008049796480942883176715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18005366530987295255451143 27008049796480942883176715)
          ·
            refine ⟨40512074694721414324765073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27008049796480942883176715 40512074694721414324765073)
            ·
              refine ⟨30384056021041060743573805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40512074694721414324765073 30384056021041060743573805)
              ·
                refine ⟨11394021007890397778840177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30384056021041060743573805 11394021007890397778840177)
                ·
                  refine ⟨8545515755917798334130133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11394021007890397778840177 8545515755917798334130133)
                  ·
                    refine ⟨200285525529323398456175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8545515755917798334130133 200285525529323398456175)
                    ·
                      rfl

theorem cell22_585082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_585082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585082 prefixEnd_585082 := by exact prefixLift 585082
  have htrace : WordTrace (prefixWord ++ tailWord_585082) baseStart_585082 baseEnd_585082 := by
    simpa [prefixWord, tailWord_585082, baseEnd_585082] using wordTrace_append hprefix tailTrace_585082
  have hstable : (prefixWord ++ tailWord_585082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585082).length < 2 ^ (prefixWord ++ tailWord_585082).sum := by decide
  have hdescent : baseEnd_585082 < baseStart_585082 := by decide
  rcases family_descends (prefixWord ++ tailWord_585082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585084 : List Nat := [2, 2, 2, 1, 1, 1, 7, 6]
def baseStart_585084 : Nat := 118140960795 + 585084 * 2 ^ 59
def prefixEnd_585084 : Nat := 4983230072969 + 3 ^ 40 * 585084 * 2
def baseEnd_585084 : Nat := 22254023352244006656241

theorem tailTrace_585084 : CollatzResearch.WordTrace tailWord_585084 prefixEnd_585084 22254023352244006656241 := by
  unfold tailWord_585084
  simp only [CollatzResearch.WordTrace]
  refine ⟨10669883306174033618461153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14226511074898711491281537 10669883306174033618461153)
  ·
    refine ⟨8002412479630525213845865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10669883306174033618461153 8002412479630525213845865)
    ·
      refine ⟨6001809359722893910384399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8002412479630525213845865 6001809359722893910384399)
      ·
        refine ⟨9002714039584340865576599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6001809359722893910384399 9002714039584340865576599)
        ·
          refine ⟨13504071059376511298364899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9002714039584340865576599 13504071059376511298364899)
          ·
            refine ⟨20256106589064766947547349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13504071059376511298364899 20256106589064766947547349)
            ·
              refine ⟨474752498181205475333141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20256106589064766947547349 474752498181205475333141)
              ·
                refine ⟨22254023352244006656241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 474752498181205475333141 22254023352244006656241)
                ·
                  rfl

theorem cell22_585084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 6].length) (baseStart_585084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585084 prefixEnd_585084 := by exact prefixLift 585084
  have htrace : WordTrace (prefixWord ++ tailWord_585084) baseStart_585084 baseEnd_585084 := by
    simpa [prefixWord, tailWord_585084, baseEnd_585084] using wordTrace_append hprefix tailTrace_585084
  have hstable : (prefixWord ++ tailWord_585084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585084).length < 2 ^ (prefixWord ++ tailWord_585084).sum := by decide
  have hdescent : baseEnd_585084 < baseStart_585084 := by decide
  rcases family_descends (prefixWord ++ tailWord_585084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585090 : List Nat := [3, 4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_585090 : Nat := 118140960795 + 585090 * 2 ^ 59
def prefixEnd_585090 : Nat := 4983230072969 + 3 ^ 40 * 585090 * 2
def baseEnd_585090 : Nat := 66762754697604681418717

theorem tailTrace_585090 : CollatzResearch.WordTrace tailWord_585090 prefixEnd_585090 66762754697604681418717 := by
  unfold tailWord_585090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5334996362581582565410181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14226656966884220174427149 5334996362581582565410181)
  ·
    refine ⟨1000311817984046731014409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5334996362581582565410181 1000311817984046731014409)
    ·
      refine ⟨750233863488035048260807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1000311817984046731014409 750233863488035048260807)
      ·
        refine ⟨1125350795232052572391211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 750233863488035048260807 1125350795232052572391211)
        ·
          refine ⟨1688026192848078858586817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125350795232052572391211 1688026192848078858586817)
          ·
            refine ⟨1266019644636059143940113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1688026192848078858586817 1266019644636059143940113)
            ·
              refine ⟨949514733477044357955085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266019644636059143940113 949514733477044357955085)
              ·
                refine ⟨356068025053891634233157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 949514733477044357955085 356068025053891634233157)
                ·
                  refine ⟨66762754697604681418717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 356068025053891634233157 66762754697604681418717)
                  ·
                    rfl

theorem cell22_585090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_585090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585090 prefixEnd_585090 := by exact prefixLift 585090
  have htrace : WordTrace (prefixWord ++ tailWord_585090) baseStart_585090 baseEnd_585090 := by
    simpa [prefixWord, tailWord_585090, baseEnd_585090] using wordTrace_append hprefix tailTrace_585090
  have hstable : (prefixWord ++ tailWord_585090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585090).length < 2 ^ (prefixWord ++ tailWord_585090).sum := by decide
  have hdescent : baseEnd_585090 < baseStart_585090 := by decide
  rcases family_descends (prefixWord ++ tailWord_585090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585099 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 5, 3]
def baseStart_585099 : Nat := 118140960795 + 585099 * 2 ^ 59
def prefixEnd_585099 : Nat := 4983230072969 + 3 ^ 40 * 585099 * 2
def baseEnd_585099 : Nat := 200291344976741020781123

theorem tailTrace_585099 : CollatzResearch.WordTrace tailWord_585099 prefixEnd_585099 200291344976741020781123 := by
  unfold tailWord_585099
  simp only [CollatzResearch.WordTrace]
  refine ⟨21340313707293724798718351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14226875804862483199145567 21340313707293724798718351)
  ·
    refine ⟨32010470560940587198077527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21340313707293724798718351 32010470560940587198077527)
    ·
      refine ⟨48015705841410880797116291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32010470560940587198077527 48015705841410880797116291)
      ·
        refine ⟨72023558762116321195674437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48015705841410880797116291 72023558762116321195674437)
        ·
          refine ⟨13504417267896810224188957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72023558762116321195674437 13504417267896810224188957)
          ·
            refine ⟨5064156475461303834070859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13504417267896810224188957 5064156475461303834070859)
            ·
              refine ⟨7596234713191955751106289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5064156475461303834070859 7596234713191955751106289)
              ·
                refine ⟨5697176034893966813329717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7596234713191955751106289 5697176034893966813329717)
                ·
                  refine ⟨534110253271309388749661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5697176034893966813329717 534110253271309388749661)
                  ·
                    refine ⟨200291344976741020781123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 534110253271309388749661 200291344976741020781123)
                    ·
                      rfl

theorem cell22_585099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 3].length) (baseStart_585099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585099 prefixEnd_585099 := by exact prefixLift 585099
  have htrace : WordTrace (prefixWord ++ tailWord_585099) baseStart_585099 baseEnd_585099 := by
    simpa [prefixWord, tailWord_585099, baseEnd_585099] using wordTrace_append hprefix tailTrace_585099
  have hstable : (prefixWord ++ tailWord_585099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585099).length < 2 ^ (prefixWord ++ tailWord_585099).sum := by decide
  have hdescent : baseEnd_585099 < baseStart_585099 := by decide
  rcases family_descends (prefixWord ++ tailWord_585099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585133 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_585133 : Nat := 118140960795 + 585133 * 2 ^ 59
def prefixEnd_585133 : Nat := 4983230072969 + 3 ^ 40 * 585133 * 2
def baseEnd_585133 : Nat := 200302983871576265431019

theorem tailTrace_585133 : CollatzResearch.WordTrace tailWord_585133 prefixEnd_585133 200302983871576265431019 := by
  unfold tailWord_585133
  simp only [CollatzResearch.WordTrace]
  refine ⟨21341553789170548605456053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14227702526113699070304035 21341553789170548605456053)
  ·
    refine ⟨2000770667734738931761505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21341553789170548605456053 2000770667734738931761505)
    ·
      refine ⟨1500578000801054198821129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2000770667734738931761505 1500578000801054198821129)
      ·
        refine ⟨1125433500600790649115847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1500578000801054198821129 1125433500600790649115847)
        ·
          refine ⟨1688150250901185973673771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125433500600790649115847 1688150250901185973673771)
          ·
            refine ⟨2532225376351778960510657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688150250901185973673771 2532225376351778960510657)
            ·
              refine ⟨1899169032263834220382993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532225376351778960510657 1899169032263834220382993)
              ·
                refine ⟨1424376774197875665287245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899169032263834220382993 1424376774197875665287245)
                ·
                  refine ⟨534141290324203374482717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1424376774197875665287245 534141290324203374482717)
                  ·
                    refine ⟨200302983871576265431019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 534141290324203374482717 200302983871576265431019)
                    ·
                      rfl

theorem cell22_585133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_585133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585133 prefixEnd_585133 := by exact prefixLift 585133
  have htrace : WordTrace (prefixWord ++ tailWord_585133) baseStart_585133 baseEnd_585133 := by
    simpa [prefixWord, tailWord_585133, baseEnd_585133] using wordTrace_append hprefix tailTrace_585133
  have hstable : (prefixWord ++ tailWord_585133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585133).length < 2 ^ (prefixWord ++ tailWord_585133).sum := by decide
  have hdescent : baseEnd_585133 < baseStart_585133 := by decide
  rcases family_descends (prefixWord ++ tailWord_585133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585206 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_585206 : Nat := 118140960795 + 585206 * 2 ^ 59
def prefixEnd_585206 : Nat := 4983230072969 + 3 ^ 40 * 585206 * 2
def baseEnd_585206 : Nat := 200327973263428408355795

theorem tailTrace_585206 : CollatzResearch.WordTrace tailWord_585206 prefixEnd_585206 200327973263428408355795 := by
  unfold tailWord_585206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334013519869130129553967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14229477545270721381908981 1334013519869130129553967)
  ·
    refine ⟨2001020279803695194330951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1334013519869130129553967 2001020279803695194330951)
    ·
      refine ⟨3001530419705542791496427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2001020279803695194330951 3001530419705542791496427)
      ·
        refine ⟨4502295629558314187244641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001530419705542791496427 4502295629558314187244641)
        ·
          refine ⟨3376721722168735640433481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4502295629558314187244641 3376721722168735640433481)
          ·
            refine ⟨2532541291626551730325111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3376721722168735640433481 2532541291626551730325111)
            ·
              refine ⟨3798811937439827595487667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532541291626551730325111 3798811937439827595487667)
              ·
                refine ⟨5698217906159741393231501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3798811937439827595487667 5698217906159741393231501)
                ·
                  refine ⟨2136831714809903022461813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5698217906159741393231501 2136831714809903022461813)
                  ·
                    refine ⟨200327973263428408355795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2136831714809903022461813 200327973263428408355795)
                    ·
                      rfl

theorem cell22_585206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_585206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585206 prefixEnd_585206 := by exact prefixLift 585206
  have htrace : WordTrace (prefixWord ++ tailWord_585206) baseStart_585206 baseEnd_585206 := by
    simpa [prefixWord, tailWord_585206, baseEnd_585206] using wordTrace_append hprefix tailTrace_585206
  have hstable : (prefixWord ++ tailWord_585206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585206).length < 2 ^ (prefixWord ++ tailWord_585206).sum := by decide
  have hdescent : baseEnd_585206 < baseStart_585206 := by decide
  rcases family_descends (prefixWord ++ tailWord_585206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585223 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 2, 3]
def baseStart_585223 : Nat := 118140960795 + 585223 * 2 ^ 59
def prefixEnd_585223 : Nat := 4983230072969 + 3 ^ 40 * 585223 * 2
def baseEnd_585223 : Nat := 200333792710846030680743

theorem tailTrace_585223 : CollatzResearch.WordTrace tailWord_585223 prefixEnd_585223 200333792710846030680743 := by
  unfold tailWord_585223
  simp only [CollatzResearch.WordTrace]
  refine ⟨21344836358844493976232323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14229890905896329317488215 21344836358844493976232323)
  ·
    refine ⟨32017254538266740964348485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21344836358844493976232323 32017254538266740964348485)
    ·
      refine ⟨6003235225925013930815341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32017254538266740964348485 6003235225925013930815341)
      ·
        refine ⟨2251213209721880224055753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6003235225925013930815341 2251213209721880224055753)
        ·
          refine ⟨1688409907291410168041815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2251213209721880224055753 1688409907291410168041815)
          ·
            refine ⟨2532614860937115252062723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688409907291410168041815 2532614860937115252062723)
            ·
              refine ⟨3798922291405672878094085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532614860937115252062723 3798922291405672878094085)
              ·
                refine ⟨712297929638563664642641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3798922291405672878094085 712297929638563664642641)
                ·
                  refine ⟨534223447228922748481981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 712297929638563664642641 534223447228922748481981)
                  ·
                    refine ⟨200333792710846030680743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 534223447228922748481981 200333792710846030680743)
                    ·
                      rfl

theorem cell22_585223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_585223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585223 prefixEnd_585223 := by exact prefixLift 585223
  have htrace : WordTrace (prefixWord ++ tailWord_585223) baseStart_585223 baseEnd_585223 := by
    simpa [prefixWord, tailWord_585223, baseEnd_585223] using wordTrace_append hprefix tailTrace_585223
  have hstable : (prefixWord ++ tailWord_585223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585223).length < 2 ^ (prefixWord ++ tailWord_585223).sum := by decide
  have hdescent : baseEnd_585223 < baseStart_585223 := by decide
  rcases family_descends (prefixWord ++ tailWord_585223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585264 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 7]
def baseStart_585264 : Nat := 118140960795 + 585264 * 2 ^ 59
def prefixEnd_585264 : Nat := 4983230072969 + 3 ^ 40 * 585264 * 2
def baseEnd_585264 : Nat := 66782609282911863468539

theorem tailTrace_585264 : CollatzResearch.WordTrace tailWord_585264 prefixEnd_585264 66782609282911863468539 := by
  unfold tailWord_585264
  simp only [CollatzResearch.WordTrace]
  refine ⟨10673165875847978989237423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14230887834463971985649897 10673165875847978989237423)
  ·
    refine ⟨16009748813771968483856135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10673165875847978989237423 16009748813771968483856135)
    ·
      refine ⟨24014623220657952725784203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16009748813771968483856135 24014623220657952725784203)
      ·
        refine ⟨36021934830986929088676305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24014623220657952725784203 36021934830986929088676305)
        ·
          refine ⟨27016451123240196816507229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36021934830986929088676305 27016451123240196816507229)
          ·
            refine ⟨10131169171215073806190211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27016451123240196816507229 10131169171215073806190211)
            ·
              refine ⟨15196753756822610709285317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10131169171215073806190211 15196753756822610709285317)
              ·
                refine ⟨2849391329404239507990997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15196753756822610709285317 2849391329404239507990997)
                ·
                  refine ⟨66782609282911863468539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2849391329404239507990997 66782609282911863468539)
                  ·
                    rfl

theorem cell22_585264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_585264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585264 prefixEnd_585264 := by exact prefixLift 585264
  have htrace : WordTrace (prefixWord ++ tailWord_585264) baseStart_585264 baseEnd_585264 := by
    simpa [prefixWord, tailWord_585264, baseEnd_585264] using wordTrace_append hprefix tailTrace_585264
  have hstable : (prefixWord ++ tailWord_585264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585264).length < 2 ^ (prefixWord ++ tailWord_585264).sum := by decide
  have hdescent : baseEnd_585264 < baseStart_585264 := by decide
  rcases family_descends (prefixWord ++ tailWord_585264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585281 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 7]
def baseStart_585281 : Nat := 118140960795 + 585281 * 2 ^ 59
def prefixEnd_585281 : Nat := 4983230072969 + 3 ^ 40 * 585281 * 2
def baseEnd_585281 : Nat := 66784549098717737576855

theorem tailTrace_585281 : CollatzResearch.WordTrace tailWord_585281 prefixEnd_585281 66784549098717737576855 := by
  unfold tailWord_585281
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346951792634369881843697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14231301195089579921229131 21346951792634369881843697)
  ·
    refine ⟨16010213844475777411382773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21346951792634369881843697 16010213844475777411382773)
    ·
      refine ⟨1500957547919604132317135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16010213844475777411382773 1500957547919604132317135)
      ·
        refine ⟨2251436321879406198475703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500957547919604132317135 2251436321879406198475703)
        ·
          refine ⟨3377154482819109297713555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251436321879406198475703 3377154482819109297713555)
          ·
            refine ⟨5065731724228663946570333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377154482819109297713555 5065731724228663946570333)
            ·
              refine ⟨1899649396585748979963875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5065731724228663946570333 1899649396585748979963875)
              ·
                refine ⟨2849474094878623469945813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899649396585748979963875 2849474094878623469945813)
                ·
                  refine ⟨66784549098717737576855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2849474094878623469945813 66784549098717737576855)
                  ·
                    rfl

theorem cell22_585281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_585281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585281 prefixEnd_585281 := by exact prefixLift 585281
  have htrace : WordTrace (prefixWord ++ tailWord_585281) baseStart_585281 baseEnd_585281 := by
    simpa [prefixWord, tailWord_585281, baseEnd_585281] using wordTrace_append hprefix tailTrace_585281
  have hstable : (prefixWord ++ tailWord_585281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585281).length < 2 ^ (prefixWord ++ tailWord_585281).sum := by decide
  have hdescent : baseEnd_585281 < baseStart_585281 := by decide
  rcases family_descends (prefixWord ++ tailWord_585281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585328 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 1, 4]
def baseStart_585328 : Nat := 118140960795 + 585328 * 2 ^ 59
def prefixEnd_585328 : Nat := 4983230072969 + 3 ^ 40 * 585328 * 2
def baseEnd_585328 : Nat := 200369736356660756805421

theorem tailTrace_585328 : CollatzResearch.WordTrace tailWord_585328 prefixEnd_585328 200369736356660756805421 := by
  unfold tailWord_585328
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674333011732048454402319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14232444015642731272536425 10674333011732048454402319)
  ·
    refine ⟨16011499517598072681603479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10674333011732048454402319 16011499517598072681603479)
    ·
      refine ⟨24017249276397109022405219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16011499517598072681603479 24017249276397109022405219)
      ·
        refine ⟨36025873914595663533607829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24017249276397109022405219 36025873914595663533607829)
        ·
          refine ⟨1688712839746671728137867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36025873914595663533607829 1688712839746671728137867)
          ·
            refine ⟨2533069259620007592206801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688712839746671728137867 2533069259620007592206801)
            ·
              refine ⟨1899801944715005694155101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2533069259620007592206801 1899801944715005694155101)
              ·
                refine ⟨712425729268127135308163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1899801944715005694155101 712425729268127135308163)
                ·
                  refine ⟨1068638593902190702962245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712425729268127135308163 1068638593902190702962245)
                  ·
                    refine ⟨200369736356660756805421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1068638593902190702962245 200369736356660756805421)
                    ·
                      rfl

theorem cell22_585328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_585328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585328 prefixEnd_585328 := by exact prefixLift 585328
  have htrace : WordTrace (prefixWord ++ tailWord_585328) baseStart_585328 baseEnd_585328 := by
    simpa [prefixWord, tailWord_585328, baseEnd_585328] using wordTrace_append hprefix tailTrace_585328
  have hstable : (prefixWord ++ tailWord_585328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585328).length < 2 ^ (prefixWord ++ tailWord_585328).sum := by decide
  have hdescent : baseEnd_585328 < baseStart_585328 := by decide
  rcases family_descends (prefixWord ++ tailWord_585328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585356 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_585356 : Nat := 118140960795 + 585356 * 2 ^ 59
def prefixEnd_585356 : Nat := 4983230072969 + 3 ^ 40 * 585356 * 2
def baseEnd_585356 : Nat := 200379321328878017105335

theorem tailTrace_585356 : CollatzResearch.WordTrace tailWord_585356 prefixEnd_585356 200379321328878017105335 := by
  unfold tailWord_585356
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674843633681328845411961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14233124844908438460549281 10674843633681328845411961)
  ·
    refine ⟨8006132725260996634058971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10674843633681328845411961 8006132725260996634058971)
    ·
      refine ⟨12009199087891494951088457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8006132725260996634058971 12009199087891494951088457)
      ·
        refine ⟨9006899315918621213316343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12009199087891494951088457 9006899315918621213316343)
        ·
          refine ⟨13510348973877931819974515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9006899315918621213316343 13510348973877931819974515)
          ·
            refine ⟨20265523460816897729961773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13510348973877931819974515 20265523460816897729961773)
            ·
              refine ⟨7599571297806336648735665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20265523460816897729961773 7599571297806336648735665)
              ·
                refine ⟨5699678473354752486551749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7599571297806336648735665 5699678473354752486551749)
                ·
                  refine ⟨1068689713754016091228453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5699678473354752486551749 1068689713754016091228453)
                  ·
                    refine ⟨200379321328878017105335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1068689713754016091228453 200379321328878017105335)
                    ·
                      rfl

theorem cell22_585356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_585356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585356 prefixEnd_585356 := by exact prefixLift 585356
  have htrace : WordTrace (prefixWord ++ tailWord_585356) baseStart_585356 baseEnd_585356 := by
    simpa [prefixWord, tailWord_585356, baseEnd_585356] using wordTrace_append hprefix tailTrace_585356
  have hstable : (prefixWord ++ tailWord_585356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585356).length < 2 ^ (prefixWord ++ tailWord_585356).sum := by decide
  have hdescent : baseEnd_585356 < baseStart_585356 := by decide
  rcases family_descends (prefixWord ++ tailWord_585356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585362 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_585362 : Nat := 118140960795 + 585362 * 2 ^ 59
def prefixEnd_585362 : Nat := 4983230072969 + 3 ^ 40 * 585362 * 2
def baseEnd_585362 : Nat := 200381375251496001455317

theorem tailTrace_585362 : CollatzResearch.WordTrace tailWord_585362 prefixEnd_585362 200381375251496001455317 := by
  unfold tailWord_585362
  simp only [CollatzResearch.WordTrace]
  refine ⟨5337476526335230178885585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14233270736893947143694893 5337476526335230178885585)
  ·
    refine ⟨4003107394751422634164189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5337476526335230178885585 4003107394751422634164189)
    ·
      refine ⟨1501165273031783487811571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4003107394751422634164189 1501165273031783487811571)
      ·
        refine ⟨2251747909547675231717357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1501165273031783487811571 2251747909547675231717357)
        ·
          refine ⟨844405466080378211894009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2251747909547675231717357 844405466080378211894009)
          ·
            refine ⟨633304099560283658920507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844405466080378211894009 633304099560283658920507)
            ·
              refine ⟨949956149340425488380761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633304099560283658920507 949956149340425488380761)
              ·
                refine ⟨712467112005319116285571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949956149340425488380761 712467112005319116285571)
                ·
                  refine ⟨1068700668007978674428357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712467112005319116285571 1068700668007978674428357)
                  ·
                    refine ⟨200381375251496001455317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1068700668007978674428357 200381375251496001455317)
                    ·
                      rfl

theorem cell22_585362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_585362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585362 prefixEnd_585362 := by exact prefixLift 585362
  have htrace : WordTrace (prefixWord ++ tailWord_585362) baseStart_585362 baseEnd_585362 := by
    simpa [prefixWord, tailWord_585362, baseEnd_585362] using wordTrace_append hprefix tailTrace_585362
  have hstable : (prefixWord ++ tailWord_585362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585362).length < 2 ^ (prefixWord ++ tailWord_585362).sum := by decide
  have hdescent : baseEnd_585362 < baseStart_585362 := by decide
  rcases family_descends (prefixWord ++ tailWord_585362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585375 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 1, 5]
def baseStart_585375 : Nat := 118140960795 + 585375 * 2 ^ 59
def prefixEnd_585375 : Nat := 4983230072969 + 3 ^ 40 * 585375 * 2
def baseEnd_585375 : Nat := 200385825417168300880277

theorem tailTrace_585375 : CollatzResearch.WordTrace tailWord_585375 prefixEnd_585375 200385825417168300880277 := by
  unfold tailWord_585375
  simp only [CollatzResearch.WordTrace]
  refine ⟨21350380254293823935765579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14233586836195882623843719 21350380254293823935765579)
  ·
    refine ⟨32025570381440735903648369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21350380254293823935765579 32025570381440735903648369)
    ·
      refine ⟨24019177786080551927736277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32025570381440735903648369 24019177786080551927736277)
      ·
        refine ⟨562949479361262935806319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24019177786080551927736277 562949479361262935806319)
        ·
          refine ⟨844424219041894403709479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562949479361262935806319 844424219041894403709479)
          ·
            refine ⟨1266636328562841605564219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844424219041894403709479 1266636328562841605564219)
            ·
              refine ⟨1899954492844262408346329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266636328562841605564219 1899954492844262408346329)
              ·
                refine ⟨1424965869633196806259747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899954492844262408346329 1424965869633196806259747)
                ·
                  refine ⟨2137448804449795209389621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424965869633196806259747 2137448804449795209389621)
                  ·
                    refine ⟨200385825417168300880277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2137448804449795209389621 200385825417168300880277)
                    ·
                      rfl

theorem cell22_585375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 5].length) (baseStart_585375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585375 prefixEnd_585375 := by exact prefixLift 585375
  have htrace : WordTrace (prefixWord ++ tailWord_585375) baseStart_585375 baseEnd_585375 := by
    simpa [prefixWord, tailWord_585375, baseEnd_585375] using wordTrace_append hprefix tailTrace_585375
  have hstable : (prefixWord ++ tailWord_585375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585375).length < 2 ^ (prefixWord ++ tailWord_585375).sum := by decide
  have hdescent : baseEnd_585375 < baseStart_585375 := by decide
  rcases family_descends (prefixWord ++ tailWord_585375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585401 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_585401 : Nat := 118140960795 + 585401 * 2 ^ 59
def prefixEnd_585401 : Nat := 4983230072969 + 3 ^ 40 * 585401 * 2
def baseEnd_585401 : Nat := 200394725748512899730197

theorem tailTrace_585401 : CollatzResearch.WordTrace tailWord_585401 prefixEnd_585401 200394725748512899730197 := by
  unfold tailWord_585401
  simp only [CollatzResearch.WordTrace]
  refine ⟨21351328552199630376212057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14234219034799753584141371 21351328552199630376212057)
  ·
    refine ⟨16013496414149722782159043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21351328552199630376212057 16013496414149722782159043)
    ·
      refine ⟨24020244621224584173238565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16013496414149722782159043 24020244621224584173238565)
      ·
        refine ⟨4503795866479609532482231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24020244621224584173238565 4503795866479609532482231)
        ·
          refine ⟨6755693799719414298723347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4503795866479609532482231 6755693799719414298723347)
          ·
            refine ⟨10133540699579121448085021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6755693799719414298723347 10133540699579121448085021)
            ·
              refine ⟨3800077762342170543031883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10133540699579121448085021 3800077762342170543031883)
              ·
                refine ⟨5700116643513255814547825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3800077762342170543031883 5700116643513255814547825)
                ·
                  refine ⟨4275087482634941860910869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5700116643513255814547825 4275087482634941860910869)
                  ·
                    refine ⟨200394725748512899730197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4275087482634941860910869 200394725748512899730197)
                    ·
                      rfl

theorem cell22_585401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_585401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585401 prefixEnd_585401 := by exact prefixLift 585401
  have htrace : WordTrace (prefixWord ++ tailWord_585401) baseStart_585401 baseEnd_585401 := by
    simpa [prefixWord, tailWord_585401, baseEnd_585401] using wordTrace_append hprefix tailTrace_585401
  have hstable : (prefixWord ++ tailWord_585401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585401).length < 2 ^ (prefixWord ++ tailWord_585401).sum := by decide
  have hdescent : baseEnd_585401 < baseStart_585401 := by decide
  rcases family_descends (prefixWord ++ tailWord_585401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585431 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 1, 7]
def baseStart_585431 : Nat := 118140960795 + 585431 * 2 ^ 59
def prefixEnd_585431 : Nat := 4983230072969 + 3 ^ 40 * 585431 * 2
def baseEnd_585431 : Nat := 200404995361602821480105

theorem tailTrace_585431 : CollatzResearch.WordTrace tailWord_585431 prefixEnd_585431 200404995361602821480105 := by
  unfold tailWord_585431
  simp only [CollatzResearch.WordTrace]
  refine ⟨21352422742090945499804147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14234948494727296999869431 21352422742090945499804147)
  ·
    refine ⟨32028634113136418249706221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21352422742090945499804147 32028634113136418249706221)
    ·
      refine ⟨12010737792426156843639833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32028634113136418249706221 12010737792426156843639833)
      ·
        refine ⟨9008053344319617632729875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12010737792426156843639833 9008053344319617632729875)
        ·
          refine ⟨13512080016479426449094813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9008053344319617632729875 13512080016479426449094813)
          ·
            refine ⟨5067030006179784918410555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13512080016479426449094813 5067030006179784918410555)
            ·
              refine ⟨7600545009269677377615833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5067030006179784918410555 7600545009269677377615833)
              ·
                refine ⟨5700408756952258033211875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7600545009269677377615833 5700408756952258033211875)
                ·
                  refine ⟨8550613135428387049817813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5700408756952258033211875 8550613135428387049817813)
                  ·
                    refine ⟨200404995361602821480105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8550613135428387049817813 200404995361602821480105)
                    ·
                      rfl

theorem cell22_585431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_585431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585431 prefixEnd_585431 := by exact prefixLift 585431
  have htrace : WordTrace (prefixWord ++ tailWord_585431) baseStart_585431 baseEnd_585431 := by
    simpa [prefixWord, tailWord_585431, baseEnd_585431] using wordTrace_append hprefix tailTrace_585431
  have hstable : (prefixWord ++ tailWord_585431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585431).length < 2 ^ (prefixWord ++ tailWord_585431).sum := by decide
  have hdescent : baseEnd_585431 < baseStart_585431 := by decide
  rcases family_descends (prefixWord ++ tailWord_585431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585448 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_585448 : Nat := 118140960795 + 585448 * 2 ^ 59
def prefixEnd_585448 : Nat := 4983230072969 + 3 ^ 40 * 585448 * 2
def baseEnd_585448 : Nat := 200410814809020443805053

theorem tailTrace_585448 : CollatzResearch.WordTrace tailWord_585448 prefixEnd_585448 200410814809020443805053 := by
  unfold tailWord_585448
  simp only [CollatzResearch.WordTrace]
  refine ⟨10676521391514678701586499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14235361855352904935448665 10676521391514678701586499)
  ·
    refine ⟨16014782087272018052379749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10676521391514678701586499 16014782087272018052379749)
    ·
      refine ⟨3002771641363503384821203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16014782087272018052379749 3002771641363503384821203)
      ·
        refine ⟨4504157462045255077231805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3002771641363503384821203 4504157462045255077231805)
        ·
          refine ⟨1689059048266970653961927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4504157462045255077231805 1689059048266970653961927)
          ·
            refine ⟨2533588572400455980942891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689059048266970653961927 2533588572400455980942891)
            ·
              refine ⟨3800382858600683971414337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2533588572400455980942891 3800382858600683971414337)
              ·
                refine ⟨2850287143950512978560753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3800382858600683971414337 2850287143950512978560753)
                ·
                  refine ⟨2137715357962884733920565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2850287143950512978560753 2137715357962884733920565)
                  ·
                    refine ⟨200410814809020443805053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2137715357962884733920565 200410814809020443805053)
                    ·
                      rfl

theorem cell22_585448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_585448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585448 prefixEnd_585448 := by exact prefixLift 585448
  have htrace : WordTrace (prefixWord ++ tailWord_585448) baseStart_585448 baseEnd_585448 := by
    simpa [prefixWord, tailWord_585448, baseEnd_585448] using wordTrace_append hprefix tailTrace_585448
  have hstable : (prefixWord ++ tailWord_585448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585448).length < 2 ^ (prefixWord ++ tailWord_585448).sum := by decide
  have hdescent : baseEnd_585448 < baseStart_585448 := by decide
  rcases family_descends (prefixWord ++ tailWord_585448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585480 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_585480 : Nat := 118140960795 + 585480 * 2 ^ 59
def prefixEnd_585480 : Nat := 4983230072969 + 3 ^ 40 * 585480 * 2
def baseEnd_585480 : Nat := 200421769062983027004955

theorem tailTrace_585480 : CollatzResearch.WordTrace tailWord_585480 prefixEnd_585480 200421769062983027004955 := by
  unfold tailWord_585480
  simp only [CollatzResearch.WordTrace]
  refine ⟨10677104959456713434168947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14236139945942284578891929 10677104959456713434168947)
  ·
    refine ⟨16015657439185070151253421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10677104959456713434168947 16015657439185070151253421)
    ·
      refine ⟨6005871539694401306720033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16015657439185070151253421 6005871539694401306720033)
      ·
        refine ⟨4504403654770800980040025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6005871539694401306720033 4504403654770800980040025)
        ·
          refine ⟨3378302741078100735030019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4504403654770800980040025 3378302741078100735030019)
          ·
            refine ⟨5067454111617151102545029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3378302741078100735030019 5067454111617151102545029)
            ·
              refine ⟨950147645928215831727193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5067454111617151102545029 950147645928215831727193)
              ·
                refine ⟨712610734446161873795395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950147645928215831727193 712610734446161873795395)
                ·
                  refine ⟨1068916101669242810693093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712610734446161873795395 1068916101669242810693093)
                  ·
                    refine ⟨200421769062983027004955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1068916101669242810693093 200421769062983027004955)
                    ·
                      rfl

theorem cell22_585480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_585480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585480 prefixEnd_585480 := by exact prefixLift 585480
  have htrace : WordTrace (prefixWord ++ tailWord_585480) baseStart_585480 baseEnd_585480 := by
    simpa [prefixWord, tailWord_585480, baseEnd_585480] using wordTrace_append hprefix tailTrace_585480
  have hstable : (prefixWord ++ tailWord_585480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585480).length < 2 ^ (prefixWord ++ tailWord_585480).sum := by decide
  have hdescent : baseEnd_585480 < baseStart_585480 := by decide
  rcases family_descends (prefixWord ++ tailWord_585480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
